"""Persistently supervise exact-owner processes, transports and the original service.

No membership changes, new genesis or source requests are made by this loop.
ComputeNode start.sh/resume.sh or the host service manager supervises this process.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import json
import os
from pathlib import Path
import secrets
import shlex
import signal
import subprocess
import sys
import time

from anchor import public_key
from challenge_anchor import Client, QuorumClient
from crypto import app_private, canonical, connect, digest, peer, receive, send, sign, verify


def save(path, value):
    temporary = path.with_suffix('.tmp')
    with temporary.open('wb') as output:
        os.chmod(temporary, 0o600)
        output.write(canonical(value))
        output.flush()
        os.fsync(output.fileno())
    temporary.replace(path)
    descriptor = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def birth(pid):
    result = subprocess.run(['ps', '-p', str(pid), '-o', 'stat=', '-o', 'lstart='], capture_output=True, text=True)
    fields = result.stdout.strip().split(None, 1)
    return fields[1] if result.returncode == 0 and len(fields) == 2 and 'Z' not in fields[0] else ''


def boot_identity():
    path = Path('/proc/sys/kernel/random/boot_id')
    if path.exists():
        return path.read_text().strip()
    return subprocess.check_output(['/usr/sbin/sysctl', '-n', 'kern.bootsessionuuid'], text=True).strip()


def child(state, name, argv):
    # The monitor retains this lock throughout the executable's lifetime. If
    # its parent dies before publication, a replacement cannot start a twin.
    lock = (state / (name + '.owner.lock')).open('a')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit(79)
    record = {'pid': os.getpid(), 'birth': birth(os.getpid()), 'argv': argv,
              'boot': boot_identity(), 'pgid': os.getpgid(0)}
    save(state / (name + '-process.json'), record)
    # ssh deliberately closes inherited descriptors. Keep the owner lock in
    # this small monitor, and keep the actual executable in the same group.
    process = subprocess.Popen(argv)
    raise SystemExit(process.wait())


class OwnedProcess:
    def __init__(self, state, name, argv):
        self.state, self.name, self.argv = state, name, argv
        self.path = state / (name + '-process.json')
        self.record = json.loads(self.path.read_text()) if self.path.exists() else None
        if self.record and self.record['argv'] != argv:
            raise ValueError('PROCESS_OWNER_CONFIGURATION_CHANGED: ' + name)

    def alive(self):
        if self.path.exists():
            record = json.loads(self.path.read_text())
            if record['argv'] != self.argv:
                raise ValueError('PROCESS_OWNER_CONFIGURATION_CHANGED: ' + self.name)
            self.record = record
        if not self.record or self.record.get('boot') != boot_identity() or birth(self.record['pid']) != self.record['birth']:
            return False
        try:
            if os.getpgid(self.record['pid']) != self.record['pgid'] or self.record['pgid'] != self.record['pid']:
                return False
        except ProcessLookupError:
            return False
        with (self.state / (self.name + '.owner.lock')).open('a') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                return True
            fcntl.flock(lock, fcntl.LOCK_UN)
        return False

    def start(self):
        if self.alive():
            return False
        with (self.state / (self.name + '.log')).open('ab') as log:
            process = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), '--child',
                                        str(self.state), self.name, json.dumps(self.argv)],
                                       stdin=subprocess.DEVNULL, stdout=log, stderr=log, start_new_session=True)
        end = time.monotonic() + 5
        while not self.alive():
            if time.monotonic() > end or process.poll() not in (None, 79):
                raise RuntimeError('PROCESS_START_FAILED: ' + self.name)
            time.sleep(.05)
        return True

    def stop(self):
        if self.alive():
            os.killpg(self.record['pid'], signal.SIGTERM)
            end = time.monotonic() + 8
            while self.alive() and time.monotonic() < end:
                time.sleep(.1)
            if self.alive():
                os.killpg(self.record['pid'], signal.SIGKILL)
        self.path.unlink(missing_ok=True)
        self.record = None


class Loop:
    def __init__(self, config):
        self.config = config
        self.state = Path(config['state'])
        self.state.mkdir(mode=0o700, parents=True, exist_ok=True)
        self.lock = (self.state / 'loop.lock').open('a')
        try:
            fcntl.flock(self.lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError('RECOVERY_OWNER_ALREADY_ACTIVE') from None
        self.service_config = json.loads(Path(config['service']).read_text())
        identity = digest({'loop': config, 'service': self.service_config})
        self.identity = identity
        binding = self.state / 'binding.json'
        if binding.exists() and json.loads(binding.read_text()) != {'configuration': identity}:
            raise ValueError('RECOVERY_OWNER_CONFIGURATION_CHANGED')
        save(binding, {'configuration': identity})
        self.key = app_private(Path(self.service_config['pki']) / 'server')
        self.members, self.retry = {}, {}
        for name, spec in config['members'].items():
            self.members[name] = OwnedProcess(self.state, 'member-' + name, spec['command'])
        runner = Path(config.get('service_entrypoint', Path(__file__).with_name('recovery_service.py'))).resolve()
        if not runner.is_file():
            raise ValueError('RECOVERY_SERVICE_RUNNER_MISSING')
        self.service = OwnedProcess(self.state, 'service', [sys.executable, str(runner), config['service']])
        self.last = None

    def event(self, kind, **detail):
        body = {'kind': kind, 'source': self.service_config['source'],
                'stream': self.service_config['stream'], 'at': time.time(), **detail}
        with (self.state / 'events.jsonl').open('ab', buffering=0) as output:
            output.write(canonical(sign(self.key, 'recovery-event', body)) + b'\n')
            os.fsync(output.fileno())

    def ensure_remote(self, name):
        spec = self.config['members'][name]
        remote = spec.get('remote')
        if not remote or time.monotonic() < self.retry.get(name, 0):
            return
        self.retry[name] = time.monotonic() + 30
        sys.path.insert(0, self.config['compute_node_mac'])
        from pcnode import Config, Node
        node = Node(Config.load(Path(remote['config'])), Path(remote['state']))
        snapshot = node.guard.snapshot()
        phase = snapshot['phase']
        if phase != 'healthy':
            if snapshot.get('hold_reason'):
                raise ValueError('SHARED_TRANSPORT_OPERATOR_HOLD')
            if not remote.get('recover_transport', False):
                raise ValueError('SHARED_TRANSPORT_REQUIRES_OWNER_RECOVERY')
            # Shared guard serializes the sole probe and verifies host + fsync +
            # disk reserve. Never bypass it with another SSH state or identity.
            node.recover_transport(min_free_bytes=remote['min_free_bytes'])
        node.wsl(remote['ensure'], 20, allow_probe=False)
        self.event('remote-supervisor-ensured', member=name)

    def member(self, name):
        process = self.members[name]
        endpoint = self.service_config['anchors']['endpoints'][name]
        identity = self.service_config['anchors']['trust']['members'][name]
        from quorum import membership
        scope = {**self.service_config, 'anchor': {**endpoint, 'identity': identity,
                    'cluster': membership(self.service_config['anchors']['trust'])}}
        try:
            changed = False
            if not process.alive():
                self.ensure_remote(name)
                remote = self.config['members'][name].get('remote')
                if remote:
                    sys.path.insert(0, self.config['compute_node_mac'])
                    from pcnode import Config, Node
                    node = Node(Config.load(Path(remote['config'])), Path(remote['state']))
                    with node.transport_session(allow_probe=False):
                        changed = process.start()
                else:
                    changed = process.start()
                if changed:
                    self.event('process-rebuilt', member=name, process=process.record)
            end = time.monotonic() + (15 if changed else 0)
            while True:
                try:
                    return name, Client(scope).head()
                except (ConnectionRefusedError, ConnectionResetError, EOFError):
                    if time.monotonic() > end or not process.alive():
                        raise
                    time.sleep(.2)
        except Exception as error:
            try:
                self.ensure_remote(name)
            except Exception as remote_error:
                error = remote_error
            # A dead SSH session can retain its listening socket briefly. A
            # failed authenticated head must also replace this exact tunnel.
            if self.config['members'][name].get('remote'):
                process.stop()
            return name, {'error': type(error).__name__ + ': ' + str(error)}

    def service_health(self):
        cfg = self.service_config
        with connect(Path(cfg['pki']) / 'auditor1', cfg['port']) as connection:
            uri, fingerprint, key = peer(connection)
            expected = cfg['registry']['server']
            if uri != 'urn:public-audit:server' or fingerprint != expected['fingerprint'] or key.public_bytes_raw().hex() != expected['app']:
                raise ValueError('RECOVERY_SERVICE_IDENTITY')
            message = receive(connection)
            body = verify(key, 'challenge', message)
            if body['source'] != cfg['source'] or body['stream'] != cfg['stream']:
                raise ValueError('RECOVERY_SERVICE_SCOPE')
            request = sign(app_private(Path(cfg['pki']) / 'auditor1'), 'lookup',
                           {**body, 'lookup_id': '__recovery_health__' + secrets.token_hex(32)})
            send(connection, request)
            response = verify(key, 'error', receive(connection))
            if response['code'] != 'REQUEST_NOT_COMMITTED':
                raise ValueError('RECOVERY_SERVICE_NOT_CURRENT: ' + response['code'])
            return {'cut': body['cut'], 'epoch': body['epoch']}

    def once(self):
        with ThreadPoolExecutor(max_workers=4) as pool:
            members = dict(pool.map(self.member, self.members))
        try:
            client = QuorumClient(self.service_config)
            head = client.head()  # Original CAS only heals exact signed prefixes.
            if self.service.start():
                self.event('service-rebuilt', process=self.service.record)
                end = time.monotonic() + 45
                while True:
                    try:
                        health = self.service_health()
                        break
                    except (ConnectionRefusedError, EOFError):
                        if not self.service.alive() or time.monotonic() > end:
                            raise
                        time.sleep(.2)
            else:
                health = self.service_health()
            status = {'phase': 'ready', 'head': head, 'service': health}
        except Exception as error:
            self.service.stop()
            status = {'phase': 'blocked', 'error': type(error).__name__ + ': ' + str(error)}
        failures = {name: value for name, value in members.items() if 'error' in value}
        state = {**status, 'members': members, 'unavailable': sorted(failures),
                 'processes': {'service': self.service.record, **{name: proc.record for name, proc in self.members.items()}},
                 'owner': {'pid': os.getpid(), 'birth': birth(os.getpid())},
                 'configuration': self.identity, 'at': time.time()}
        save(self.state / 'status.json', sign(self.key, 'recovery-status', state))
        marker = (status['phase'], tuple(sorted(failures)), status.get('error'))
        if marker != self.last:
            self.event('state-changed', phase=status['phase'], unavailable=sorted(failures), error=status.get('error'))
            print(json.dumps(state), flush=True)
            self.last = marker

    def run(self):
        try:
            while not (self.state / 'STOP').exists():
                self.once()
                end = time.monotonic() + self.config.get('interval', 3)
                while not (self.state / 'STOP').exists() and time.monotonic() < end:
                    time.sleep(.2)
        finally:
            self.service.stop()
            for process in self.members.values():
                process.stop()


def main():
    if len(sys.argv) == 5 and sys.argv[1] == '--child':
        child(Path(sys.argv[2]), sys.argv[3], json.loads(sys.argv[4]))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('config', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    Loop(json.loads(args.config.read_text())).run()


if __name__ == '__main__':
    main()
