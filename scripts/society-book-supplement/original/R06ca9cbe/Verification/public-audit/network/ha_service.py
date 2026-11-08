"""Same Lean Store with a quorum intent before source advance, and fenced CAS."""
import argparse
import json
import os
from pathlib import Path
import signal
import time

import quorum
import service
from anchor import ledger_hash
from crypto import canonical, sign, tls_context
from ha_quorum import Quorum
from recovery_loop import birth, boot_identity, save


def boundary(store, name, **detail):
    config = store.config
    if config.get('test_boundary') != name:
        return
    path = Path(config['database']).parent/'ha-fault-arm.json'
    if path.exists():
        path.rename(path.with_name('ha-fault-consumed.json'))
        save(path.with_name('ha-fault-boundary.json'), sign(store.key, 'ha-fault-boundary', {
            'phase': name, 'source': config['source'], 'stream': config['stream'],
            'owner': config['ha']['owner'], 'grant': config['ha']['grant'],
            'pid': os.getpid(), 'birth': birth(os.getpid()), 'at': time.time(), **detail}))
        os.kill(os.getpid(), signal.SIGSTOP)


class Store(service.Store):
    def append(self, event):
        message = sign(self.key, 'ledger', event); previous = self.head()
        seq = self.database.execute('SELECT count(*) FROM events').fetchone()[0]+1
        self.save_pending(seq,previous,message)
        try:intent = self.anchor.stage(seq, previous, message)
        except BaseException:
            # A timed-out stage may already exist remotely. The existing
            # backend-health supervisor reopens this same fsynced request.
            self.poisoned=True
            self.backend.close()
            raise
        boundary(self, 'after-intent', seq=seq, previous=previous, message=message, intent=intent)
        result = super().append(event)
        if result != ledger_hash(previous, message):
            raise ValueError('HA_ORIGINAL_EVENT_CHANGED')
        original = Quorum.append.__get__(self.anchor, type(self.anchor))
        def append(seq, previous, message):
            boundary(self, 'after-source', seq=seq, previous=previous, message=message, intent=intent)
            return original(seq, previous, message)
        self.anchor.append = append
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('config', type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    if config.get('lean_path'):
        os.environ['LEAN_PATH'] = config['lean_path']
    quorum.Client = Quorum; config['recover_from_anchor'] = True
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    store = Store(config)
    try:
        with service.Server((config.get('bind', '127.0.0.1'), config['port']), service.Handler) as server:
            server.store = store; server.context = tls_context(Path(config['pki'])/'server', server=True)
            save(Path(config['database']).parent/'ha-service-ready.json', sign(store.key, 'ha-service-ready', {
                'source': config['source'], 'stream': config['stream'], 'grant': config['ha']['grant'],
                'pid': os.getpid(), 'birth': birth(os.getpid()), 'boot': boot_identity(),
                'backend': {'pid': store.backend.process.pid, 'birth': birth(store.backend.process.pid)},
                'head': store.head(), 'at': time.time()}))
            server.serve_forever(poll_interval=.2)
    finally:
        store.backend.close(); store.database.close()
        from governance import close_readers
        close_readers()
        from energy import close_readers as close_energy_readers
        close_energy_readers()


if __name__ == '__main__':
    main()
