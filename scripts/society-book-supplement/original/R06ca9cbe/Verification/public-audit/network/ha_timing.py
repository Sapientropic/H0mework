"""Original HA public execution; own private frames never enter its configuration.

The source's frame/next commuting theorem reconstructs each whole private next.
Private replay is a separate consumer of committed events, not a reply gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

import anchor
from challenge_anchor import Handler as AnchorHandler
import governance
import ha_service
import online_privacy
import quorum
import semantic_anchor
import service
from crypto import canonical, digest, sign, tls_context
from ha_quorum import Quorum
from privacy_transport import Worker
from source_semantics import Engine


FORBIDDEN = {'private_variant', 'private_exporter', 'private_journal', '__private_audit', 'own_frame'}


def public_configuration(config):
    from donor_result_codec import enabled
    enabled(config)
    def visit(value):
        if isinstance(value, dict):
            if FORBIDDEN.intersection(value): raise ValueError('PRIVATE_INPUT_ON_PUBLIC_PATH')
            for item in value.values(): visit(item)
        elif isinstance(value, list):
            for item in value: visit(item)
        elif value == 'private-two': raise ValueError('PRIVATE_SELECTOR_ON_PUBLIC_PATH')
    visit(config)
    if config.get('public_representative') != 'original-fixed-source/v1':
        raise ValueError('PUBLIC_REPRESENTATIVE_REQUIRED')
    for name in ('governance','energy','continuation','handoff','regeneration','refeed','productive','arrival','donor','semantic'):
        if name in config:
            settings = config[name]
            if settings['backend'][-1] != 'private-one': raise ValueError('PUBLIC_SOURCE_ARGV')
            if hashlib.sha256(Path(settings['exporter']).read_bytes()).hexdigest() != settings['descriptor']['exporter_sha256']:
                raise ValueError('PUBLIC_ORIGINAL_EXPORTER')
    if 'backend' in config:
        settings=config['public_base_source']
        if config['backend']!=settings['backend'] or settings['backend'][-1]!='private-one':
            raise ValueError('PUBLIC_BASE_SOURCE_ARGV')
        Engine(settings)


class Store(online_privacy.Store):
    def __init__(self, config):
        public_configuration(config)
        settings = config['online_privacy']
        if set(settings) != {'worker','source_inputs','journal','prefix'}:
            raise ValueError('PUBLIC_BOUNDARY_CONFIGURATION')
        for filename, expected in settings['source_inputs'].items():
            if hashlib.sha256(Path(filename).read_bytes()).hexdigest() != expected:
                raise ValueError('PUBLIC_BOUNDARY_SOURCE')
        worker = dict(settings['worker'])
        if hashlib.sha256(Path(worker['command'][0]).read_bytes()).hexdigest() != worker['compiler_sha256']:
            raise ValueError('PUBLIC_COMPILER')
        worker['stderr'] += '.'+str(os.getpid())
        self.public_worker = Worker(worker)
        self.boundary_journal = Path(settings['journal']).open('a')
        self.checked = {}
        self.wire_lock = threading.Lock()
        self.wire_index = 0
        try:
            # Call the original transaction store directly: the previous
            # private-inspection initializer is intentionally not on this path.
            ha_service.Store.__init__(self, config)
            rows = governance.rows_of(self.database)
            prefix = settings['prefix']
            if len(rows) < prefix['seq'] or rows[prefix['seq']-1][2] != prefix['head']:
                raise ValueError('PUBLIC_ORIGINAL_PREFIX')
            for index, row in enumerate(rows[prefix['seq']:], prefix['seq']):
                self.check_event(rows[:index], json.loads(row[3])['body'], 'restore')
        except BaseException:
            if hasattr(self,'backend'): self.backend.close()
            if hasattr(self,'database'): self.database.close()
            if hasattr(self,'writer_lock'): self.writer_lock.close()
            self.public_worker.close(); self.boundary_journal.close()
            raise

    def check_event(self, rows, event, phase):
        value = online_privacy.source_input(self.config, rows, event)
        identity = digest({'prefix':rows[-1][2],'event':event})
        started = time.monotonic_ns()
        if identity not in self.checked:
            result = self.public_worker.call(value)
            if canonical(result) != canonical(event['native']):
                raise ValueError('PUBLIC_COMPLETE_SOURCE_MISMATCH')
            self.checked[identity] = digest(result)
            if len(self.checked) > 64: self.checked.pop(next(iter(self.checked)))
        proof = sign(self.key, 'online-privacy-boundary', {
            'source':self.config['source'],'stream':self.config['stream'], 'phase':phase,
            'seq':len(rows)+1,'parent':rows[-1][2], 'request_id':event['request']['body']['request_id'],
            'event':digest(event),'input':value,'native':self.checked[identity],
            'started_ns':started,'finished_ns':time.monotonic_ns()})
        with self.wire_lock:
            self.boundary_journal.write(canonical(proof).decode()+'\n')
            self.boundary_journal.flush(); os.fsync(self.boundary_journal.fileno())
        return proof

    def close(self):
        self.public_worker.close(); self.boundary_journal.close()
        self.backend.close(); self.database.close(); self.writer_lock.close()

    def append(self,event):
        self.check_event(governance.rows_of(self.database),event,'before-intent')
        message=sign(self.key,'ledger',event);previous=self.head()
        seq=self.database.execute('SELECT count(*) FROM events').fetchone()[0]+1
        self.save_pending(seq,previous,message)
        try:intent=self.anchor.stage(seq,previous,message)
        except BaseException:
            self.poisoned=True;self.backend.close();raise
        self.boundary('after-intent',seq=seq,previous=previous,message=message,intent=intent)
        result=service.Store.append(self,event)
        if result!=anchor.ledger_hash(previous,message):raise ValueError('HA_ORIGINAL_EVENT_CHANGED')
        original=Quorum.append.__get__(self.anchor,type(self.anchor))
        def append(seq,previous,message):
            self.boundary('after-source',seq=seq,previous=previous,message=message,intent=intent)
            return original(seq,previous,message)
        self.anchor.append=append
        return result

    def boundary(self,name,**detail):
        if self.config.get('test_boundary')!=name:return
        path=Path(self.config['database']).parent/'ha-fault-arm.json'
        if path.exists():
            path.rename(path.with_name('ha-fault-consumed.json'))
            # No privileged ps executable is available inside the file sandbox.
            # The outside observer separately binds this owned PID and its birth.
            from recovery_loop import save
            save(path.with_name('ha-fault-boundary.json'),sign(self.key,'ha-fault-boundary',{
                'phase':name,'source':self.config['source'],'stream':self.config['stream'],
                'owner':self.config['ha']['owner'],'grant':self.config['ha']['grant'],
                'pid':os.getpid(),'at':time.time(),**detail}))
            os.kill(os.getpid(),signal.SIGSTOP)


class Journal(semantic_anchor.Journal):
    def __init__(self, config):
        public_configuration(config)
        super().__init__(config)

    def execute(self,body):
        if body.get('op')=='semantic-status':
            with self.lock:
                if body['source']!=self.config['streams'][body['stream']]['source']:
                    raise ValueError('ANCHOR_SOURCE')
                process=self.engine.process
                return {'prefix':{'seq':self.engine.count,'head':self.engine.head},
                    'descriptor':self.engine.descriptor,'warm_error':self.warm_error,
                    'backend':{'pid':process.pid,'argv':process.args} if process and process.poll() is None else None,
                    'decisions':self.db.execute('SELECT id FROM semantic_decisions ORDER BY rowid DESC LIMIT 8').fetchall()}
        return super().execute(body)


def workers():
    import energy
    result = []
    for engine in [*governance._readers.values(), *energy._readers.values()]:
        process = engine.process
        if process is not None and process.poll() is None:
            result.append({'pid':process.pid,'argv':process.args})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('role',choices=('writer','anchor')); parser.add_argument('config',type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    public_configuration(config)
    if config.get('lean_path'): os.environ['LEAN_PATH'] = config['lean_path']
    signal.signal(signal.SIGTERM,lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    if args.role == 'writer':
        quorum.Client = Quorum; config['recover_from_anchor'] = True
        store = Store(config)
        try:
            with service.Server(('127.0.0.1',config.get('port',0)),online_privacy.Handler) as server:
                server.store = store; server.context = tls_context(Path(config['pki'])/'server',server=True)
                print(json.dumps({'port':server.server_address[1],'pid':os.getpid(),
                    'backend_pid':store.backend.process.pid,'public_pid':store.public_worker.process.pid,
                    'public_stderr':store.public_worker.errors.name,'head':store.head(),'workers':workers()}),flush=True)
                server.serve_forever(poll_interval=.1)
        finally:
            store.close(); governance.close_readers()
            from energy import close_readers
            close_readers()
    else:
        journal = Journal(config)
        try:
            with anchor.Server(('127.0.0.1',config['port']),AnchorHandler) as server:
                server.journal = journal; server.context = tls_context(Path(config['pki'])/'anchor',server=True)
                print(json.dumps({'port':config['port'],'pid':os.getpid(),'role':'public-semantic-ha'}),flush=True)
                server.serve_forever(poll_interval=.1)
        finally:
            journal.stop_warming.set()
            if journal.warmer: journal.warmer.join(125)
            journal.engine.close(); governance.close_readers()
            from energy import close_readers
            close_readers(); journal.db.close()


if __name__ == '__main__': main()
