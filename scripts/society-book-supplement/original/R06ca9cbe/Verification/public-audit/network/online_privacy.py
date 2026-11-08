"""Original HA writer with a public-source check before intent and every reply.

The original Handler, transaction, fencing and recovery remain the execution
path. A branch is installed in private worker configuration, never in a request.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

import continuation
import governance
import handoff
import regeneration
import source_extension
import ha_service
import quorum
import service
from crypto import canonical, digest, peer, sign, tls_context
from ha_quorum import Quorum
from privacy_transport import Worker
from application_receipts import Journal as ApplicationJournal


def source_input(config, rows, event):
    kind = event['type']
    if kind == 'energy-continuation':
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = {'mode': 'continuation', **continuation.argument(config, rows, event)}
    elif kind == 'energy-handoff':
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = {'mode': 'handoff', **handoff.argument(config, rows, event)}
    elif kind == 'source-extension':
        expected = {'type', 'source', 'stream', 'request', 'peer', 'native'}
        source_extension.expected(config, rows, event)
        value = {'mode': 'source-extension', 'native': event['native']}
    elif kind == 'energy-regeneration':
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = regeneration.argument(config, rows, event)
    elif kind == 'material-extension':
        import material_extension
        expected = {'type', 'source', 'stream', 'request', 'peer', 'native'}
        material_extension.expected(config, rows, event)
        value = {'mode': 'source-extension', 'native': event['native']}
    elif kind in {'donor-extension','energy-donor'}:
        import donor_arrival_live as donor
        if kind==donor.CONTROL:
            expected={'type','source','stream','request','peer','native'}
            donor.expected(config,rows,event)
            value={'mode':'source-extension','native':event['native']}
        else:
            expected={'type','source','stream','request','peer','scope','native','nextScope'}
            value=donor.argument(config,rows,event)
    elif kind == 'arrival-extension':
        import arrival_extension
        expected = {'type', 'source', 'stream', 'request', 'peer', 'native'}
        arrival_extension.expected(config, rows, event)
        value = {'mode': 'source-extension', 'native': event['native']}
    elif kind == 'energy-arrival':
        import arrival_regeneration
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = arrival_regeneration.argument(config, rows, event)
    elif kind == 'productive-extension':
        import productive_extension
        expected = {'type', 'source', 'stream', 'request', 'peer', 'native'}
        productive_extension.expected(config, rows, event)
        value = {'mode': 'source-extension', 'native': event['native']}
    elif kind == 'energy-productive':
        import productive_regeneration
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = productive_regeneration.argument(config, rows, event)
    elif kind == 'energy-material':
        import material_regeneration
        expected = {'type', 'source', 'stream', 'request', 'peer', 'scope', 'native', 'nextScope'}
        value = material_regeneration.argument(config, rows, event)
    else:
        raise ValueError('ONLINE_PRIVACY_KIND_REQUIRED')
    if set(event) != expected:
        raise ValueError('ONLINE_EVENT_FIELDS')
    return value


class Store(ha_service.Store):
    def __init__(self, config):
        settings = config['online_privacy']
        if set(settings) != {'worker', 'source_inputs', 'journal', 'private_journal', 'prefix'}:
            raise ValueError('ONLINE_PRIVACY_CONFIGURATION')
        for filename, expected in settings['source_inputs'].items():
            if hashlib.sha256(Path(filename).read_bytes()).hexdigest() != expected:
                raise ValueError('ONLINE_SOURCE_BINDING')
        if hashlib.sha256(Path(settings['worker']['command'][0]).read_bytes()).hexdigest() != settings['worker']['compiler_sha256']:
            raise ValueError('ONLINE_COMPILER_BINDING')
        worker = dict(settings['worker'])
        worker['stderr'] += '.'+str(os.getpid())
        self.public_worker = Worker(worker)
        self.boundary_journal = Path(settings['journal']).open('a')
        self.private_journal = Path(settings['private_journal']).open('a')
        os.chmod(settings['private_journal'], 0o600)
        self.checked = {}
        self.wire_lock = threading.Lock()
        self.wire_index = 0
        try:
            super().__init__(config)
            rows = governance.rows_of(self.database)
            prefix = settings['prefix']
            if len(rows) < prefix['seq'] or rows[prefix['seq']-1][2] != prefix['head']:
                raise ValueError('ONLINE_ORIGINAL_PREFIX')
            for index, row in enumerate(rows[prefix['seq']:], prefix['seq']):
                self.check_event(rows[:index], json.loads(row[3])['body'], 'restore')
        except BaseException:
            if hasattr(self, 'backend'):
                self.backend.close()
            if hasattr(self, 'database'):
                self.database.close()
            if hasattr(self, 'writer_lock'):
                self.writer_lock.close()
            self.public_worker.close()
            self.boundary_journal.close()
            self.private_journal.close()
            raise

    def check_event(self, rows, event, phase):
        value = source_input(self.config, rows, event)
        identity = digest({'prefix': rows[-1][2], 'event': event})
        started = time.monotonic_ns()
        if identity not in self.checked:
            result = self.public_worker.call(value)
            if canonical(result) != canonical(event['native']):
                raise ValueError('ONLINE_COMPLETE_SOURCE_MISMATCH')
            if event['type'] == 'energy-handoff':
                # Private IPC inspection shares the exact already-used source
                # worker. It never becomes an application response or authority.
                own = handoff.native_call(self.config, {**{key: item for key, item in value.items() if key != 'mode'},
                                                       '__private_audit': True})
                import energy
                engine = energy._readers[digest(self.config['handoff'])]
                private = sign(self.key, 'online-private-state', {
                    'event': digest(event), 'seq': len(rows)+1, 'private': own,
                    'argv': engine.process.args, 'pid': engine.process.pid,
                    'observed_command': subprocess.check_output(
                        ['ps','-p',str(engine.process.pid),'-o','command='],text=True).strip()})
                self.private_journal.write(canonical(private).decode()+'\n')
                self.private_journal.flush()
                os.fsync(self.private_journal.fileno())
            self.checked[identity] = digest(result)
            if len(self.checked) > 64:
                self.checked.pop(next(iter(self.checked)))
        proof = sign(self.key, 'online-privacy-boundary', {
            'source': self.config['source'], 'stream': self.config['stream'],
            'phase': phase, 'seq': len(rows)+1, 'parent': rows[-1][2],
            'request_id': event['request']['body']['request_id'], 'event': digest(event),
            'input': value, 'native': self.checked[identity],
            'started_ns': started, 'finished_ns': time.monotonic_ns()})
        with self.wire_lock:
            self.boundary_journal.write(canonical(proof).decode()+'\n')
            self.boundary_journal.flush()
            os.fsync(self.boundary_journal.fileno())
        return proof

    def append(self, event):
        self.check_event(governance.rows_of(self.database), event, 'before-intent')
        return super().append(event)

    def reconcile_pending(self, recover):
        if self.pending_path.is_file():
            pending = json.loads(self.pending_path.read_text())
            if (set(pending) != {'seq', 'previous', 'message'} or type(pending['seq']) is not int or
                    pending['seq'] <= self.config['online_privacy']['prefix']['seq'] or
                    pending['seq'] > self.anchor.head()['seq']+1):
                raise ValueError('ONLINE_PENDING_SCHEMA')
            if pending['seq'] > self.config['online_privacy']['prefix']['seq']:
                prefix = governance.rows_of(self.database)[:pending['seq']-1]
                if len(prefix) != pending['seq']-1 or prefix[-1][2] != pending['previous']:
                    prefix = []
                    for seq in range(1, pending['seq']):
                        entry = self.anchor.get(seq)
                        point = entry['receipt']['body']
                        prefix.append((seq, point['previous'], point['head'], canonical(entry['message']).decode()))
                if prefix[-1][2] != pending['previous']:
                    raise ValueError('ONLINE_PENDING_PARENT')
                self.check_event(prefix, pending['message']['body'], 'before-reconcile')
        return super().reconcile_pending(recover)

    def response_for(self, seq):
        rows = governance.rows_of(self.database)
        if seq > self.config['online_privacy']['prefix']['seq']:
            self.check_event(rows[:seq-1], json.loads(rows[seq-1][3])['body'], 'reply')
        return super().response_for(seq)

    def close(self):
        self.public_worker.close()
        self.boundary_journal.close()
        self.private_journal.close()
        self.backend.close()
        self.database.close()
        self.writer_lock.close()


class WireSocket:
    def __init__(self, connection, receipt=None):
        self.connection = connection
        self.operations = []
        self.receipt = receipt

    def __getattr__(self, name):
        return getattr(self.connection, name)

    def recv(self, count):
        data = self.connection.recv(count)
        self.operations.append({'direction': 'received', 'at_ns': time.monotonic_ns(),
                                'bytes': base64.b64encode(data).decode()})
        if self.receipt:self.receipt.add('io',self.operations[-1])
        return data

    def sendall(self, data):
        started = time.monotonic_ns()
        self.connection.sendall(data)
        self.operations.append({'direction': 'sent', 'at_ns': started,
                                'finished_ns': time.monotonic_ns(),
                                'bytes': base64.b64encode(data).decode()})
        if self.receipt:self.receipt.add('io',self.operations[-1])


class Handler(service.Handler):
    def handle(self):
        store = self.server.store
        original = self.request
        started = time.monotonic_ns()
        journal=ApplicationJournal(store.config['online_privacy']['journal']+'.applications.jsonl',
            store.key,store.config['source'],store.config['stream'],'server')
        receipt=journal.start({'owner':store.config['ha']['owner']})
        metadata=None;error=None
        wire = WireSocket(original,receipt)
        self.request = wire
        try:
            uri,fingerprint,key=peer(original)
            metadata=dict(peer={'uri':uri,'fingerprint':fingerprint,'app':key.public_bytes_raw().hex()},
                          tls=original.version(),cipher=original.cipher()[0])
            receipt.add('tls',metadata)
            super().handle()
        except BaseException as problem:
            error=type(problem).__name__;raise
        finally:
            receipt.close(error)
            if metadata is not None:
                with store.wire_lock:
                    value = sign(store.key, 'online-wire-observation', {
                        'index': store.wire_index, 'started_ns': started,
                        'finished_ns': time.monotonic_ns(), **metadata,
                        'operations': wire.operations})
                    store.boundary_journal.write(canonical(value).decode()+'\n')
                    store.boundary_journal.flush()
                    os.fsync(store.boundary_journal.fileno())
                    store.wire_index += 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('config', type=Path)
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    if config.get('lean_path'):
        os.environ['LEAN_PATH'] = config['lean_path']
    quorum.Client = Quorum
    config['recover_from_anchor'] = True
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    store = Store(config)
    try:
        with service.Server(('127.0.0.1', config.get('port', 0)), Handler) as server:
            server.store = store
            server.context = tls_context(Path(config['pki'])/'server', server=True)
            print(json.dumps({'port': server.server_address[1], 'pid': os.getpid(),
                              'backend_pid': store.backend.process.pid,
                              'public_pid': store.public_worker.process.pid,
                              'public_stderr': store.public_worker.errors.name,
                              'head': store.head()}), flush=True)
            server.serve_forever(poll_interval=.1)
    finally:
        store.close()
        governance.close_readers()
        from energy import close_readers
        close_readers()


if __name__ == '__main__':
    main()
