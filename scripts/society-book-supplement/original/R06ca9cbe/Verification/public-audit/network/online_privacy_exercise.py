"""Actual original HA transactions on two private branches of the sealed prefix.

Only task-owned local processes are stopped. Existing live nodes, keys, journals
and their immutable views are read-only inputs to this experiment.
"""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import argparse
import base64
import copy
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import secrets
import selectors
import shutil
import signal
import socket
import socketserver
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
from contextlib import contextmanager

import anchor
import governance
import handoff
from crypto import app_private, canonical, connect, create_pki, digest, peer, receive, send, sign, verify
from ha_quorum import Quorum
from quorum import membership
from recovery_loop import birth

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
PREFIX = 'Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Privacy/'
spec = importlib.util.spec_from_file_location('original_handoff_actual', ROOT/'Lean/scripts/verification/public-handoff-actual.py')
original_handoff = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original_handoff)


def load(path): return json.loads(Path(path).read_text())
def save(path, value): Path(path).write_bytes(canonical(value)+b'\n')
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rows(path):
    with sqlite3.connect(Path(path).as_uri()+'?mode=ro', uri=True) as db:
        return db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()


def stop(job, *, crash=False):
    process, errors = job
    tree = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,pgid=,uid='], text=True)
    processes = [tuple(map(int, line.split())) for line in tree.splitlines()]
    owned = {process.pid}
    while True:
        descendants = {pid for pid, parent, _, uid in processes if parent in owned and uid == os.getuid()}
        if descendants <= owned: break
        owned |= descendants
    descendants = {pid: birth(pid) for pid, _, _, uid in processes if pid in owned and uid == os.getuid()}
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGKILL if crash else signal.SIGTERM)
        try: process.wait(timeout=15)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait(timeout=5)
    # Engine readers own sessions of their own; a writer crash does not reap them.
    for pid, started in descendants.items():
        if pid != process.pid and started and birth(pid) == started:
            try: os.kill(pid, signal.SIGTERM)
            except ProcessLookupError: pass
    process.stdout.close()
    errors.close()


def launch(entry, config, directory, label):
    errors = (directory/(label+'.stderr')).open('x')
    process = subprocess.Popen([sys.executable, str(HERE/entry), str(config)],
        stdout=subprocess.PIPE, stderr=errors, text=True, start_new_session=True)
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        if not selector.select(180):
            stop((process, errors), crash=True)
            raise TimeoutError('OWNED_SERVICE_STARTUP: '+label)
    first = process.stdout.readline()
    if not first:
        stop((process, errors))
        raise RuntimeError('OWNED_SERVICE_STARTUP: '+label+' '+(directory/(label+'.stderr')).read_text()[-4000:])
    ready = json.loads(first)
    ready['command'] = subprocess.check_output(['ps', '-p', str(process.pid), '-o', 'command='], text=True).strip()
    save(directory/(label+'-ready.json'), ready)
    return (process, errors), ready


class Tap:
    """Capture complete relayed TCP byte streams, including TLS handshakes."""
    def __init__(self, port, path):
        owner = self
        self.index = 0
        self.lock = threading.Lock()
        self.output = gzip.open(path, 'wt')

        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                with owner.lock:
                    number = owner.index
                    owner.index += 1
                upstream = socket.create_connection(('127.0.0.1', port), timeout=30)
                def relay(source, destination, direction):
                    try:
                        while data := source.recv(65536):
                            point = time.monotonic_ns()
                            with owner.lock:
                                owner.output.write(canonical({'connection': number, 'direction': direction,
                                    'phase': 'received', 'at_ns': point,
                                    'bytes': base64.b64encode(data).decode()}).decode()+'\n')
                                owner.output.flush()
                            destination.sendall(data)
                            with owner.lock:
                                owner.output.write(canonical({'connection': number, 'direction': direction,
                                    'phase': 'forwarded', 'at_ns': time.monotonic_ns(), 'length': len(data)}).decode()+'\n')
                                owner.output.flush()
                    except (OSError, EOFError):
                        with owner.lock:
                            owner.output.write(canonical({'connection': number, 'direction': direction,
                                'phase': 'interrupted', 'at_ns': time.monotonic_ns()}).decode()+'\n')
                            owner.output.flush()
                    finally:
                        with owner.lock:
                            owner.output.write(canonical({'connection': number, 'direction': direction,
                                'phase': 'eof', 'at_ns': time.monotonic_ns()}).decode()+'\n')
                            owner.output.flush()
                        try: destination.shutdown(socket.SHUT_WR)
                        except OSError: pass
                thread = threading.Thread(target=relay, args=(upstream, self.request, 'server'), daemon=True)
                thread.start()
                relay(self.request, upstream, 'client')
                thread.join(timeout=35)
                upstream.close()
        class Server(socketserver.ThreadingTCPServer):
            allow_reuse_address = True
            daemon_threads = False
        self.server = Server(('127.0.0.1', 0), Handler)
        self.port = self.server.server_address[1]
        self.thread = threading.Thread(target=self.server.serve_forever, kwargs={'poll_interval': .05}, daemon=True)
        self.thread.start()

    def close(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()
        self.output.close()


def private_settings(settings, variant, directory, label):
    result = copy.deepcopy(settings)
    result['private_variant'] = variant
    result['backend'][-1] = variant
    result['error_log'] = str(directory/(label+'-source.stderr'))
    return result


@contextmanager
def credentials(out):
    path = out/'credentials'
    path.mkdir(mode=0o700, exist_ok=True)
    try:
        yield path
    except BaseException:
        save(out/'recovery-required.json', {'credentials': str(path),
            'reason': 'Retain owned keys and exact journals until this unfinished run is reconciled'})
        raise
    else:
        shutil.rmtree(path)


def exchange(cfg, port, actor, operation, *, lookup=None, request_id=None):
    profile = Path(cfg['pki'])/('auditor'+actor)
    times = {'connect_start_ns': time.monotonic_ns()}
    with connect(profile, port) as connection:
        connection.settimeout(90)
        times['connected_ns'] = time.monotonic_ns()
        uri, fingerprint, key = peer(connection)
        challenge = receive(connection)
        times['challenge_received_ns'] = time.monotonic_ns()
        issued = verify(key, 'challenge', challenge)
        if uri != 'urn:public-audit:server' or fingerprint != cfg['registry']['server']['fingerprint']:
            raise ValueError('ONLINE_SERVER_IDENTITY')
        if lookup is not None:
            kind = 'lookup'
            body = {**issued, 'lookup_id': lookup, 'request_id': secrets.token_hex(16)}
        else:
            kind = 'energy-handoff'
            prefix = rows(cfg['database'])
            _, scope, current = handoff.context(cfg, prefix)
            registration = governance.registered(prefix)[0]
            body = {**issued, 'source': cfg['source'], 'stream': cfg['stream'],
                'parent': {'seq': len(prefix), 'head': prefix[-1][2]},
                'member': governance.member(cfg, prefix, actor), 'executor': registration['result']['key'],
                'cut': current['cut'], 'epoch': current['version'], 'op': operation,
                'query': {'slots': 63, 'fields': 3}, 'unit': 'energy', 'scope': scope,
                'actor': actor, 'request_id': request_id or secrets.token_hex(16)}
            execution = original_handoff.authorize(Path(cfg['original_live_root']), cfg, prefix,
                operation, body['query'], Path(cfg['database']).parent,
                body['request_id'], actor)
            body['execution'] = execution['execution']
        request = sign(app_private(profile), kind, body)
        times['request_sent_ns'] = time.monotonic_ns()
        send(connection, request)
        try:
            response = receive(connection)
            verify(key, response['kind'], response)
        except (OSError, EOFError) as error:
            response = {'transport_error': type(error).__name__}
        times['response_received_ns'] = time.monotonic_ns()
        return sign(app_private(profile), 'online-client-observation', {
            'peer': {'uri': uri, 'fingerprint': fingerprint, 'app': key.public_bytes_raw().hex()},
            'tls': connection.version(), 'cipher': connection.cipher()[0],
            'challenge': challenge, 'request': request, 'response': response, 'times': times})


def finish_recovery(cfg, q, directory, observations, pending, ready, prefix):
    assert len(rows(cfg['database'])) == 26
    assert json.loads(rows(cfg['database'])[-1][3]) == json.loads(pending)['message']
    tap = Tap(ready['port'], directory/'tls-2.jsonl.gz')
    try:
        lost = json.loads(pending)['message']['body']['request']['body']['request_id']
        observations.append(exchange(cfg, tap.port, '1', None, lookup=lost))
        save(directory/'observations.json', observations)
        observations.append(exchange(cfg, tap.port, '1', None, lookup=lost))
        save(directory/'observations.json', observations)
        last = exchange(cfg, tap.port, '2', 'read'); observations.append(last)
        assert last['body']['response']['body']['event']['native']['reason'] == 'UNFUNDED'
    finally:
        tap.close()
    final = rows(cfg['database'])
    assert len(final) == 27 and final[:24] == prefix
    assert final[-1][2] == q.head()['head']
    assert all(node.head()['seq'] == 27 for node in q.nodes.values())
    save(directory/'events.json', final)
    save(directory/'observations.json', observations)
    save(directory/'pending.json', json.loads(pending))
    save(directory/'trust.json', cfg['anchors']['trust'])
    return final


def run(live, baseline, out, resume=False):
    if out.exists():
        assert resume and (out/'recovery-required.json').is_file() and not (out/'accepted.json').exists()
    out.mkdir(parents=True, exist_ok=True)
    usage = shutil.disk_usage(out)
    if usage.free < 512*1024**2: raise RuntimeError('ONLINE_WORKSPACE_SPACE')
    manifest = load(live/'ha/deployment.json')
    original = copy.deepcopy(manifest['mac']['service'])
    original_rows = rows(original['database'])
    assert len(original_rows) == 27
    prefix = original_rows[:24]
    save(out/'original-prefix.json', prefix)
    save(out/'resource-plan.json', {'owner': 'process-generated-society', 'node': 'local Mac',
        'consumer': 'independent online privacy replay', 'max_new_work_mib': 256,
        'new_remote_jobs': 0, 'free_bytes': usage.free, 'original_live_events': 27})
    source_paths = [PREFIX+'Online.lean', 'Verification/public-audit/network/source_semantics.py',
        'Lean/scripts/verification/public-online-privacy-build.py',
        'Verification/public-audit/network/online_privacy.py',
        'Verification/public-audit/network/online_privacy_exercise.py',
        'Verification/public-audit/network/service.py', 'Verification/public-audit/network/ha_service.py',
        'Verification/public-audit/network/ha_anchor.py', 'Verification/public-audit/network/semantic_anchor.py',
        'Verification/public-audit/network/handoff.py', 'Verification/public-audit/network/continuation.py',
        'Verification/public-audit/network/energy.py', 'Verification/public-audit/network/crypto.py']
    binding = {str(ROOT/name): sha(ROOT/name) for name in source_paths}
    exporters = load(out.parent/'exporters-01/accepted.json')['exporters']
    for name, entry in exporters.items():
        assert sha(entry['exporter']) == entry['exporter_sha256']
        contract = out.parent/'exporters-01'/(name+'-contract.lean')
        assert sha(contract) == entry['contract_sha256']
        binding[entry['exporter']] = entry['exporter_sha256']
        binding[str(contract)] = entry['contract_sha256']
    lean = Path(load(baseline/'actual/one/config.json')['worker']['command'][0])
    results = []
    with credentials(out) as temporary:
        temporary = Path(temporary)
        for lane, variant in (('one', 'private-one'), ('two', 'private-two')):
            directory = out/lane
            directory.mkdir(exist_ok=resume)
            jobs, taps = [], []
            stop_renew = threading.Event()
            renewer = None
            cfg = copy.deepcopy(original)
            pki = temporary/lane/'audit'
            if not pki.exists():
                shutil.copytree(original['pki'], pki, ignore=shutil.ignore_patterns('*.lock'))
            cfg.update(database=str(directory/'service.sqlite'), pki=str(pki), port=0,
                       recover_from_anchor=True, test_boundary='after-intent', original_live_root=str(live))
            cfg['backend'] = [str(lean), '--trust=0', '-j1', '--run',
                              manifest['semantic']['configurations']['a']['exporter'], variant]
            cfg['lean_path'] = manifest['semantic']['configurations']['a']['lean_path']
            cfg['backend_error'] = str(directory/'base-source.stderr')
            for name in ('governance', 'energy', 'continuation', 'handoff'):
                cfg[name] = private_settings(cfg[name], variant, directory, name)
                installed = exporters[name]
                original_hash = cfg[name]['descriptor']['exporter_sha256']
                cfg[name]['exporter'] = installed['exporter']
                cfg[name]['backend'][4] = installed['exporter']
                cfg[name]['private_exporter'] = {
                    'original_exporter_sha256': original_hash, 'exporter_sha256': installed['exporter_sha256'],
                    'contract': str(out.parent/'exporters-01'/(name+'-contract.lean')),
                    'contract_sha256': installed['contract_sha256']}
            worker = copy.deepcopy(load(baseline/'actual/one/config.json')['worker'])
            worker['stderr'] = str(directory/'public-worker.stderr')
            worker['compiler_sha256'] = sha(lean)
            cfg['online_privacy'] = {'worker': worker, 'source_inputs': binding,
                'journal': str(directory/'boundary.jsonl'),
                'private_journal': str(directory/'private-state.jsonl'),
                'prefix': {'seq': 24, 'head': prefix[-1][2]}}
            trust = {'version': 1, 'threshold': 3, 'members': {}}
            configs = {}
            for member in 'abcd':
                location = temporary/lane/member
                prior = directory/(member+'-config.json')
                if prior.exists():
                    saved = load(prior)
                    registry = {**saved['registry'], 'server': saved['transport_writer']}
                else:
                    registry = create_pki(location, anchor=True)
                trust['members'][member] = registry['anchor']
                configs[member] = {'pki': str(location), 'registry': {**cfg['registry'], 'anchor': registry['anchor']},
                    'transport_writer': registry['server'], 'database': str(directory/(member+'.sqlite')),
                    'streams': {cfg['stream']: {'source': cfg['source'], 'writer': cfg['registry']['server']}},
                    **{name: cfg[name] for name in ('governance', 'energy', 'continuation', 'handoff', 'governance_members', 'semantic_policy')},
                    'ha': copy.deepcopy(cfg['ha'])}
            endpoints = {}
            public = directory/'public'
            public.mkdir(exist_ok=resume)
            save(public/'registry.json', cfg['registry'])
            (public/'ca.pem').write_bytes((pki/'ca.pem').read_bytes())
            for label in cfg['registry']:
                (public/(label+'.pem')).write_bytes((pki/label/'cert.pem').read_bytes())
            try:
                for member, ac in configs.items():
                    ac['cluster'] = membership(trust)
                    if not Path(ac['database']).exists():
                        seed = anchor.Journal(ac, True)
                        for seq, previous, head, text in prefix:
                            seed.execute({'op': 'append', 'source': cfg['source'], 'stream': cfg['stream'],
                                          'seq': seq, 'previous': previous, 'head': head, 'message': json.loads(text)})
                        seed.db.close()
                    ac['ha'] = {'trust': trust, 'owners': cfg['ha']['owners'], 'lease_seconds': 60}
                    semantic = private_settings(manifest['semantic']['configurations']['a'], variant, directory, member+'-semantic')
                    semantic['background_warmup'] = True
                    semantic['warm_on_start'] = False
                    semantic['replay_seconds'] = 120
                    semantic['governance_context'] = {key: cfg[key] for key in
                        ('source', 'stream', 'registry', 'ha', 'semantic_policy', 'governance', 'energy', 'continuation', 'handoff')}
                    ac['semantic'] = semantic
                    with socket.socket() as reservation:
                        reservation.bind(('127.0.0.1', 0)); ac['port'] = reservation.getsockname()[1]
                    path = directory/(member+'-config.json'); existed = path.exists(); save(path, ac)
                    job, ready = launch('semantic_anchor.py', path, directory, member+('-resumed' if existed else ''))
                    jobs.append(job)
                    endpoints[member] = {'host': '127.0.0.1', 'hostname': 'anchor.local',
                                         'port': ready['port'], 'pki': ac['pki']}
                cfg['anchors'] = {'trust': trust, 'endpoints': endpoints}
                q = Quorum(cfg)
                count = len(rows(cfg['database'])) if Path(cfg['database']).exists() else 24
                deadline = time.monotonic()+180
                while True:
                    states = {
                        name: node.call('semantic-status') for name, node in q.nodes.items()}
                    save(directory/'semantic-ready.json', states)
                    if all(state['prefix']['seq'] == count and state['warm_error'] is None for state in states.values()):
                        break
                    if time.monotonic() > deadline:
                        raise TimeoutError('ORIGINAL_PREFIX_WARMUP: '+repr(states))
                    time.sleep(1)
                print('ONLINE PREFIX READY', lane, '4 independent kernels replayed original24', flush=True)
                cfg['ha']['grant'] = q.grant()
                def renew():
                    while not stop_renew.wait(8):
                        try: q.grant(cfg['ha']['grant'])
                        except Exception as error: save(directory/'renewal-error.json', {'error': repr(error)})
                renewer = threading.Thread(target=renew, daemon=True); renewer.start()
                path = directory/'config.json'; save(path, cfg)
                if count == 25 and Path(cfg['database']+'.pending.json').exists():
                    pending = Path(cfg['database']+'.pending.json').read_bytes()
                    observations = load(directory/'observations.json')
                    assert len(observations) == 2
                    observations.append({'coordinator_observation_lost': load(directory/'ha-fault-boundary.json'),
                                         'request': json.loads(pending)['message']['body']['request']})
                    save(directory/'observations.json', observations)
                    job, ready = launch('online_privacy.py', path, directory, 'writer-2')
                    jobs.append(job)
                    final = finish_recovery(cfg,q,directory,observations,pending,ready,prefix)
                    results.append({'lane':lane,'variant':variant,'events':27,'head':final[-1][2],
                        'observations':len(observations),'paid_energy':5,'recovered_same_intent':True,
                        'coordinator_observation_lost':True})
                    print('ONLINE RESUME PASS',lane,'same paid event25 and staged26; no new handoff payment',flush=True)
                    continue
                job, ready = launch('online_privacy.py', path, directory, 'writer-1')
                jobs.append(job)
                tap = Tap(ready['port'], directory/'tls-1.jsonl.gz'); taps.append(tap)
                observations = []
                first = exchange(cfg, tap.port, '2', 'replace')
                assert first['body']['response']['kind'] == 'response', first['body']['response']
                observations.append(first)
                save(directory/'observations.json', observations)
                native = first['body']['response']['body']['event']['native']
                assert native['next']['holder'] == 2 and native['next']['energy'] == ['0']*4
                assert [row['kind'] for row in native['rows']] == ['revoke','transfer','transfer','propose','accept','use','use']
                assert native['reason'] == 'DELIVERED'
                print('ONLINE ACTUAL', lane, 'paid handoff: 5 energy; actual next; 4 semantic anchors', flush=True)
                observations.append(exchange(cfg, tap.port, '2', None, lookup=first['body']['request']['body']['request_id']))
                save(directory/'observations.json', observations)
                (directory/'ha-fault-arm.json').write_text('{}\n')
                with ThreadPoolExecutor(max_workers=1) as pool:
                    future = pool.submit(exchange, cfg, tap.port, '1', 'read')
                    deadline = time.monotonic()+90
                    while not (directory/'ha-fault-boundary.json').exists():
                        if future.done(): raise RuntimeError('FAULT_NOT_REACHED: '+str(future.result()))
                        if time.monotonic()>deadline: raise TimeoutError('ONLINE_INTENT_BOUNDARY')
                        time.sleep(.05)
                    pending = Path(cfg['database']+'.pending.json').read_bytes()
                    assert len(rows(cfg['database'])) == 25
                    stop(jobs.pop(), crash=True)
                    observations.append(future.result(timeout=15))
                    save(directory/'observations.json', observations)
                tap.close(); taps.remove(tap)
                # Original pending reconciliation commits this exact staged event.
                job, ready = launch('online_privacy.py', path, directory, 'writer-2')
                jobs.append(job)
                final = finish_recovery(cfg,q,directory,observations,pending,ready,prefix)
                results.append({'lane': lane, 'variant': variant, 'events': 27, 'head': final[-1][2],
                                'observations': len(observations), 'paid_energy': 5, 'recovered_same_intent': True})
                print('ONLINE ACTUAL PASS', lane, '27 events; intent crash/restart; repeated lookup no repayment', flush=True)
            finally:
                stop_renew.set()
                if renewer: renewer.join(10)
                for job in reversed(jobs): stop(job)
                for tap in taps: tap.close()
                governance.close_readers()
                from energy import close_readers
                close_readers()
    assert rows(original['database']) == original_rows
    files = {str(path.relative_to(out)): sha(path) for path in out.rglob('*') if path.is_file()}
    save(out/'accepted.json', {'source_inputs': binding, 'baseline': str(baseline), 'lanes': results,
        'files': files, 'original_live_events': 27, 'original_live_head': original_rows[-1][2],
        'private_keys_remaining': [], 'scope': 'Actual original HA writer; paid handoff and exact pending recovery; full signed application bytes and captured TLS streams'})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('live', type=Path); parser.add_argument('baseline', type=Path); parser.add_argument('out', type=Path)
    parser.add_argument('--resume',action='store_true')
    args = parser.parse_args()
    run(args.live.resolve(), args.baseline.resolve(), args.out.resolve(),args.resume)
