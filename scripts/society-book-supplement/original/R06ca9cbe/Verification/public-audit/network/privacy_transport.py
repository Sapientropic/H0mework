"""Proof-supported public readout over the existing mTLS/signature/frame stack.

This is a readout endpoint, not the HA writer. The worker has no private-world
argument. Source equality justifies its public evaluation; original histories
are replayed independently by the consumer. All clocks and signed bytes stay
in the transcript. Scheduler independence is an explicit environment contract.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import secrets
import selectors
import signal
import socketserver
import subprocess
import threading
import time

from crypto import FRAME, MAX_FRAMES, app_private, canonical, digest, peer, receive, send, sign, tls_context
from service import Server as NativeServer

SOURCE = 'public-source-audit/privacy-readout/v1'
KINDS = {'challenge': 'privacy-challenge', 'request': 'privacy-request', 'response': 'privacy-response'}
FRAME_BYTES = FRAME * MAX_FRAMES
TTL_NS = 30_000_000_000


def signed_frame(key, kind, body):
    body = {**body, 'padding': ''}
    value = sign(key, kind, body)
    remaining = FRAME_BYTES - 4 - len(canonical(value))
    if remaining < 0:
        raise ValueError('FRAME_TOO_LARGE')
    body['padding'] = '0' * remaining
    value = sign(key, kind, body)
    if len(canonical(value)) != FRAME_BYTES - 4:
        raise ValueError('FRAME_SIZE')
    return value


class Worker:
    def __init__(self, config):
        command = config['command']
        expected = ['--trust=0', '-j1', '-DElab.async=false', '-DwarningAsError=true',
                    '--run', 'scripts/verification/public-network-privacy-source.lean', 'public']
        contract = config.get('contract', 'original-public-privacy/v1')
        if contract == 'complete-default-supply-privacy/v1':
            expected[-2] = 'scripts/verification/public-supply-network-source.lean'
        elif contract == 'original77-donor-public/v1':
            expected[-2] = 'scripts/verification/public-donor-arrival-source.lean'
        elif contract == 'original-source-arrival-public/v1':
            expected[-2] = 'scripts/verification/public-arrival-network-source.lean'
        elif contract == 'complete-default-productive-privacy/v1':
            expected[-2] = 'scripts/verification/public-productive-network-source.lean'
        elif contract == 'complete-default-material-privacy/v1':
            expected[-2] = 'scripts/verification/public-material-network-source.lean'
        elif contract != 'original-public-privacy/v1':
            raise ValueError('PUBLIC_WORKER_CONTRACT')
        if command[1:] != expected:
            raise ValueError('PUBLIC_WORKER_REQUIRED')
        timeout = config.get('timeout', 25)
        if type(timeout) not in (int, float) or not 0 < timeout <= 300:
            raise ValueError('PUBLIC_WORKER_DEADLINE')
        self.errors = Path(config['stderr']).open('x')
        env = os.environ.copy()
        env['LEAN_PATH'] = config['lean_path']
        self.process = subprocess.Popen(command, cwd=config['cwd'], env=env, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.errors, bufsize=0)
        self.lock = threading.RLock()
        self.poisoned = False
        self.timeout = timeout

    def poison(self):
        self.poisoned = True
        if self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=2)

    def call(self, request):
        with self.lock:
            if self.poisoned:
                raise RuntimeError('PUBLIC_WORKER_RECOVERY_REQUIRED')
            deadline = time.monotonic()+self.timeout
            try:
                data = canonical(request)+b'\n'
                if len(data) > FRAME_BYTES:
                    raise RuntimeError('PUBLIC_WORKER_INPUT_BOUND')
                os.set_blocking(self.process.stdin.fileno(), False)
                with selectors.DefaultSelector() as selector:
                    selector.register(self.process.stdin, selectors.EVENT_WRITE)
                    while data:
                        if not selector.select(max(0, deadline-time.monotonic())):
                            raise RuntimeError('PUBLIC_WORKER_TIMEOUT')
                        data = data[os.write(self.process.stdin.fileno(), data):]
                buffer = bytearray()
                with selectors.DefaultSelector() as selector:
                    selector.register(self.process.stdout, selectors.EVENT_READ)
                    while b'\n' not in buffer:
                        if not selector.select(max(0, deadline-time.monotonic())):
                            raise RuntimeError('PUBLIC_WORKER_TIMEOUT')
                        part = os.read(self.process.stdout.fileno(), FRAME_BYTES)
                        if not part:
                            raise RuntimeError('PUBLIC_WORKER_EXITED')
                        buffer.extend(part)
                        if len(buffer) > FRAME_BYTES:
                            raise RuntimeError('PUBLIC_WORKER_OUTPUT_BOUND')
                line, extra = bytes(buffer).split(b'\n', 1)
                result = json.loads(line)
                if extra or not isinstance(result, dict):
                    raise RuntimeError('PUBLIC_WORKER_ENCODING')
                return result
            except Exception as error:
                # An uncertain output is never left queued for the next request.
                self.poison()
                if isinstance(error, RuntimeError):
                    raise
                raise RuntimeError('PUBLIC_WORKER_ENCODING') from None

    def close(self):
        self.process.stdin.close()
        try:
            self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.poison()
        self.process.stdout.close()
        self.errors.close()


class Gateway:
    def __init__(self, config):
        if set(config) != {'pki', 'registry', 'worker', 'descriptor', 'journal', 'binding'}:
            raise ValueError('CONFIGURATION_FIELDS')
        self.config = config
        for filename, expected in config['binding'].items():
            import hashlib
            if hashlib.sha256(Path(filename).read_bytes()).hexdigest() != expected:
                raise ValueError('SOURCE_BINDING')
        self.pki = Path(config['pki'])
        self.key = app_private(self.pki/'server')
        import hashlib
        if hashlib.sha256(Path(config['worker']['command'][0]).read_bytes()).hexdigest() != config['descriptor']['compiler_sha256']:
            raise ValueError('PUBLIC_COMPILER_BINDING')
        self.worker = Worker(config['worker'])
        self.lock = threading.RLock()
        self.index = 0
        self.previous = '0'*64
        self.used = set()
        self.journal = Path(config['journal']).open('x')

    def append(self, body):
        with self.lock:
            row = sign(self.key, 'privacy-measurement',
                       dict(source=SOURCE, index=self.index, previous=self.previous, **body))
            self.journal.write(canonical(row).decode()+'\n')
            self.journal.flush()
            os.fsync(self.journal.fileno())
            self.index += 1
            self.previous = digest(row)
            return row

    def close(self):
        self.worker.close()
        self.journal.close()


class Handler(socketserver.BaseRequestHandler):
    def handle(self):
        from crypto import verify
        gate = self.server.gateway
        challenge = request = response = None
        issued = received = work_start = work_done = release = send_start = send_done = None
        observed = None
        answer = {'error': 'TRANSPORT_INCOMPLETE'}
        try:
            self.request.settimeout(35)
            uri, fingerprint, certified = peer(self.request)
            observed = dict(uri=uri, fingerprint=fingerprint, app=certified.public_bytes_raw().hex())
            registered = next((entry for entry in gate.config['registry'].values()
                               if 'urn:public-audit:'+entry['actor'] == uri and entry['fingerprint'] == fingerprint), None)
            if registered is None or certified.public_bytes_raw().hex() != registered['app']:
                raise ValueError('PEER_NOT_REGISTERED')
            issued = time.monotonic_ns()
            challenge = signed_frame(gate.key, KINDS['challenge'], dict(
                source=SOURCE, actor=uri, peer=fingerprint, descriptor=gate.config['descriptor'],
                nonce=secrets.token_hex(32), issued_ns=issued, expires_ns=issued+TTL_NS))
            send(self.request, challenge)
            request = receive(self.request)
            received = time.monotonic_ns()
            try:
                body = verify(certified, KINDS['request'], request)
            except Exception:
                raise ValueError('REQUEST_SIGNATURE') from None
            if set(body) != {'source', 'actor', 'challenge', 'request_id', 'release_after_ms', 'input', 'padding'}:
                raise ValueError('REQUEST_FIELDS')
            if (body['source'] != SOURCE or body['actor'] != uri or body['challenge'] != digest(challenge)):
                raise ValueError('CHALLENGE_BINDING')
            if received > issued+TTL_NS:
                raise ValueError('CHALLENGE_EXPIRED')
            identifier = body['request_id']
            if not isinstance(identifier, str) or len(identifier) != 32 or any(c not in '0123456789abcdef' for c in identifier):
                raise ValueError('REQUEST_ID')
            hold = body['release_after_ms']
            if type(hold) is not int or not 0 <= hold <= 3000:
                raise ValueError('RELEASE_POLICY')
            public = body['input']
            if (not isinstance(public, dict) or set(public) - {'mode','cut','candidate','history','births','replies','queries','ordinal','phases','handoffs'}):
                raise ValueError('SOURCE_INPUT_FIELDS')
            with gate.lock:
                if identifier in gate.used:
                    raise ValueError('REPLAY')
                gate.used.add(identifier)
            release = received+hold*1_000_000
            work_start = time.monotonic_ns()
            answer = gate.worker.call(public)
            work_done = time.monotonic_ns()
            while (remaining := release-time.monotonic_ns()) > 0:
                time.sleep(min(.05, remaining/1_000_000_000))
        except Exception as error:
            answer = {'error': str(error) if isinstance(error, (ValueError, RuntimeError)) else type(error).__name__}
            work_done = time.monotonic_ns()
        try:
            send_start = time.monotonic_ns()
            body = dict(source=SOURCE, descriptor=gate.config['descriptor'],
                        challenge=digest(challenge) if challenge else None,
                        request=digest(request) if request else None, actor=observed['uri'] if observed else None,
                        native=answer, issued_ns=issued, received_ns=received, work_start_ns=work_start,
                        work_done_ns=work_done, release_ns=release, send_start_ns=send_start)
            response = signed_frame(gate.key, KINDS['response'], body)
            send(self.request, response)
            send_done = time.monotonic_ns()
        except (OSError, EOFError):
            pass
        finally:
            gate.append(dict(peer=observed, challenge=challenge, request=request, response=response,
                             sent_ns=send_done, observed_end_ns=time.monotonic_ns()))


def serve(config):
    gate = Gateway(config)
    server = NativeServer(('127.0.0.1', 0), Handler)
    server.gateway = gate
    server.context = tls_context(gate.pki/'server', server=True)
    print(json.dumps(dict(port=server.server_address[1], pid=os.getpid(), backend_pid=gate.worker.process.pid)), flush=True)
    signal.signal(signal.SIGTERM, lambda *_: threading.Thread(target=server.shutdown, daemon=True).start())
    try:
        server.serve_forever(poll_interval=.1)
    finally:
        server.server_close()
        gate.close()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('config', type=Path)
    args = parser.parse_args()
    serve(json.loads(args.config.read_text()))
