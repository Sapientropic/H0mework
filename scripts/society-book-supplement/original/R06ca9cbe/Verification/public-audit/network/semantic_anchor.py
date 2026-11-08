"""Original HA journal with independent local Lean semantics before every vote."""
import argparse
import json
from pathlib import Path
import signal
import threading
import time

import anchor
from challenge_anchor import Handler
from crypto import canonical,digest,sign,tls_context
from ha_anchor import Journal as HAJournal
from source_semantics import Engine,Incomplete,Mismatch


class Journal(HAJournal):
    def __init__(self, config):
        super().__init__(config)
        descriptor=config['semantic']['descriptor']
        if (set(config['streams'])!={descriptor['stream']} or
                config['streams'][descriptor['stream']]['source']!=descriptor['source']):
            raise ValueError('SEMANTIC_SOURCE_BINDING')
        self.db.executescript('CREATE TABLE IF NOT EXISTS semantic_binding(value TEXT NOT NULL);'
                             'CREATE UNIQUE INDEX IF NOT EXISTS semantic_singleton ON semantic_binding((1));'
                             'CREATE TABLE IF NOT EXISTS semantic_decisions(id TEXT PRIMARY KEY,payload TEXT NOT NULL);')
        value=canonical(config['semantic']['descriptor']).decode()
        prior=self.db.execute('SELECT value FROM semantic_binding').fetchall()
        if not prior:self.db.execute('INSERT INTO semantic_binding VALUES(?)',(value,))
        elif prior!=[(value,)]:raise ValueError('SEMANTIC_BINDING_CHANGED')
        if config.get('governance'):
            self.db.execute('CREATE TABLE IF NOT EXISTS governance_binding(value TEXT NOT NULL UNIQUE)')
            value=canonical(config['governance']['descriptor']).decode()
            prior=self.db.execute('SELECT value FROM governance_binding').fetchall()
            if not prior:self.db.execute('INSERT INTO governance_binding VALUES(?)',(value,))
            elif prior!=[(value,)]:raise ValueError('NATIVE_GOVERNANCE_BINDING_CHANGED')
        self.engine=Engine(config['semantic'])
        self.semantic_lock=threading.Lock()
        self.prevalidated=None
        self.warm_error=None
        self.stop_warming=threading.Event()
        self.warmer=None
        if config['semantic'].get('background_warmup',False):
            self.warm_error='SOURCE_REPLAY_PENDING'
            self.warmer=threading.Thread(target=self.warm_loop,daemon=True)
            self.warmer.start()
        elif config['semantic'].get('warm_on_start',not config.get('energy')):
            try:self.engine.sync(self.rows(next(iter(config['streams']))))
            except Incomplete as problem:self.warm_error=problem.reason
        else:self.warm_error='SOURCE_REPLAY_PENDING'

    def warm_loop(self):
        while not self.stop_warming.is_set():
            try:
                with self.semantic_lock:
                    with self.lock:rows=self.rows(next(iter(self.config['streams'])))
                    self.engine.sync(rows,deadline=time.monotonic()+120)
                    if self.config.get('arrival'):
                        from arrival_regeneration import native_call
                        native_call(self.config, {'mode':'source-extension','native':{'warm':'public'}})
                    if self.config.get('productive'):
                        from productive_regeneration import native_call
                        native_call(self.config, {'mode':'source-extension','native':{'warm':'public'}})
                    if self.config.get('regeneration'):
                        # Load the new pure public worker before reporting voter
                        # readiness; this readout creates no service event.
                        from regeneration import native_call
                        native_call(self.config, {'mode':'source-extension','native':{'warm':'public'}})
                    self.warm_error=None
            except Exception as problem:
                self.warm_error=problem.reason if isinstance(problem,Incomplete) else type(problem).__name__
            self.stop_warming.wait(5)

    def rows(self, stream):
        return self.db.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq',(stream,)).fetchall()

    def decision(self, witness):
        value=sign(self.key,'source-semantic-decision',witness);key=digest(value)
        self.db.execute('INSERT OR IGNORE INTO semantic_decisions VALUES(?,?)',(key,canonical(value).decode()))
        return key

    def validate_extension(self, stream, message):
        super().validate_extension(stream,message)
        rows=self.rows(stream)
        point=(stream,len(rows),rows[-1][2] if rows else '0'*64,digest(message))
        if self.prevalidated!=point:
            raise Incomplete('SOURCE_PREFLIGHT_REQUIRED')

    def execute(self, body):
        if body.get('op') in {'ha-stage','append'}:
            with self.lock:
                stream=body['stream'];self.owner(body);self.check_fence(body)
                self.validate_message(stream,body['message'])
                committed=self.db.execute('SELECT 1 FROM entries WHERE stream=? AND seq=?',
                                          (stream,body['seq'])).fetchone()
                if committed:return super().execute(body)
            # Kernel work must not hold the lease/CAS lock. On return, the
            # committed prefix and the fence are checked again atomically.
            with self.semantic_lock:
                with self.lock:
                    stream=body['stream'];self.owner(body);self.check_fence(body)
                    self.validate_message(stream,body['message'])
                    rows=self.rows(stream)
                    committed=self.db.execute('SELECT 1 FROM entries WHERE stream=? AND seq=?',
                                              (stream,body['seq'])).fetchone()
                if committed:
                    with self.lock:return super().execute(body)
                try:
                    witness=self.engine.check(rows,body['message'])
                    self.warm_error=None
                except Mismatch as problem:
                    with self.lock:self.decision(problem.witness)
                    raise
                with self.lock:
                    if self.rows(stream)!=rows:raise Incomplete('SOURCE_PREFIX_MOVED')
                    if witness is not None:self.decision(witness)
                    self.prevalidated=(stream,len(rows),rows[-1][2] if rows else '0'*64,digest(body['message']))
                    try:return super().execute(body)
                    finally:self.prevalidated=None
        with self.lock:
            if body.get('op')=='semantic-status':
                if body['source']!=self.config['streams'][body['stream']]['source']:raise ValueError('ANCHOR_SOURCE')
                return {**self.engine.status(),'warm_error':self.warm_error,
                        'decisions':self.db.execute('SELECT id FROM semantic_decisions ORDER BY rowid DESC LIMIT 8').fetchall()}
            if body.get('op')=='semantic-decision':
                row=self.db.execute('SELECT payload FROM semantic_decisions WHERE id=?',(body['id'],)).fetchone()
                if not row:raise ValueError('SEMANTIC_DECISION_NOT_FOUND')
                return json.loads(row[0])
            try:return super().execute(body)
            except Mismatch as problem:
                # HAJournal has rolled back the attempted intent/CAS. Preserve
                # the actual comparison separately without changing authority.
                self.decision(problem.witness);raise

    def execute_request(self,body):
        return self.execute(body)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('config',type=Path)
    config=json.loads(parser.parse_args().config.read_text());journal=Journal(config)
    signal.signal(signal.SIGTERM,lambda *_:(_ for _ in ()).throw(SystemExit(0)))
    try:
        with anchor.Server((config.get('bind','127.0.0.1'),config['port']),Handler) as server:
            server.journal=journal;server.context=tls_context(Path(config['pki'])/'anchor',server=True)
            print(json.dumps({'mode':'source-semantic-ha','port':config['port']}),flush=True)
            server.serve_forever(poll_interval=.1)
    finally:
        journal.stop_warming.set();journal.engine.close()
        from governance import close_readers
        close_readers()
        from energy import close_readers as close_energy_readers
        close_energy_readers()
        if journal.warmer:journal.warmer.join(2)
        journal.db.close()


if __name__=='__main__':main()
