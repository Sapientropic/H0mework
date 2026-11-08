"""Public timing execution on the original HA ledger and native admission.

The frozen timing Store and admitted Journal are composed here. Owner-frame
materialization belongs to a closed public epoch, never a request or lease gate.
"""
import argparse
import copy
import fcntl
import json
import os
from pathlib import Path
import signal
import sys
import threading
import time

import ha_coordinator
import ha_timing
import native_spare
import online_privacy
import quorum
import semantic_anchor
import service
from crypto import app_private, canonical, digest, sign, tls_context
from ha_quorum import Quorum
from recovery_loop import OwnedProcess, birth, boot_identity, save


class Journal(native_spare.Journal):
    def __init__(self, config):
        ha_timing.public_configuration(config)
        if not config.get('donor_history'):
            super().__init__(config)
            return
        from donor_source_view import Engine
        cold = copy.deepcopy(config)
        cold['semantic'].update(background_warmup=False, warm_on_start=False)
        super().__init__(cold)
        try:
            self.engine.close()
            self.engine = Engine(config)
            self.config = config
            self.engine.sync(self.rows(next(iter(config['streams']))))
            self.db.execute('CREATE TABLE IF NOT EXISTS donor_history_binding(value TEXT NOT NULL UNIQUE)')
            value = canonical(config['donor_history']).decode()
            prior = self.db.execute('SELECT value FROM donor_history_binding').fetchall()
            if not prior:
                self.db.execute('INSERT INTO donor_history_binding VALUES(?)', (value,))
            elif prior != [(value,)]:
                raise ValueError('DONOR_HISTORY_BINDING_CHANGED')
        except BaseException:
            self.engine.close(); self.db.close()
            raise
        self.warm_error = 'SOURCE_REPLAY_PENDING'
        if config['semantic'].get('background_warmup', False):
            self.warmer = threading.Thread(target=self.warm_loop, daemon=True)
            self.warmer.start()
        elif config['semantic'].get('warm_on_start', False):
            self.warm_once()

    def warm_once(self):
        import donor_arrival_live
        with self.semantic_lock:
            with self.lock:
                rows = self.rows(next(iter(self.config['streams'])))
            self.engine.sync(rows)
            donor_arrival_live.native_call(self.config['semantic']['governance_context'],
                                          {'mode': 'source-extension', 'native': {'warm': 'public'}})
            self.warm_error = None

    def warm_loop(self):
        if not self.config.get('donor_history'):
            return super().warm_loop()
        from source_semantics import Incomplete
        while not self.stop_warming.is_set():
            try:
                self.warm_once()
            except Exception as problem:
                self.warm_error = problem.reason if isinstance(problem, Incomplete) else type(problem).__name__
            self.stop_warming.wait(5)


def writer(config):
    if config.get('lean_path'):
        os.environ['LEAN_PATH'] = config['lean_path']
    if config.get('source_interface_fault'):
        from supply_interface_fault import Quorum as WriterQuorum
    else:
        WriterQuorum = Quorum
    quorum.Client = WriterQuorum
    config['recover_from_anchor'] = True
    if config.get('donor_history'):
        from donor_current_store import Store
    else:
        Store = ha_timing.Store
    store = Store(config)
    try:
        with service.Server((config.get('bind', '127.0.0.1'), config['port']), online_privacy.Handler) as server:
            server.store = store
            server.context = tls_context(Path(config['pki'])/'server', server=True)
            save(Path(config['database']).parent/'ha-service-ready.json', sign(store.key, 'ha-service-ready', {
                'source': config['source'], 'stream': config['stream'], 'grant': config['ha']['grant'],
                'pid': os.getpid(), 'birth': birth(os.getpid()), 'boot': boot_identity(),
                'backend': {'pid': store.backend.process.pid, 'birth': birth(store.backend.process.pid)},
                'public_timing': {'entrypoint': 'live_timing.py', 'configuration': digest(config),
                    'worker': {'pid': store.public_worker.process.pid,
                               'birth': birth(store.public_worker.process.pid),
                               'argv': store.public_worker.process.args}},
                'head': store.head(), 'at': time.time()}))
            server.serve_forever(poll_interval=.2)
    finally:
        store.close()
        import governance, energy
        governance.close_readers()
        energy.close_readers()


def coordinator(path):
    config = json.loads(path.read_text())
    current = json.loads(Path(config['service']).read_text())
    ha_timing.public_configuration(current)
    if config.get('public_timing') != 'original-fixed-source/v1':
        raise ValueError('PUBLIC_TIMING_CONTROLLER_REQUIRED')
    if current.get('source_interface_fault'):
        from supply_interface_fault import Quorum as RecoveryQuorum
        ha_coordinator.Quorum = RecoveryQuorum
    if current.get('donor_history'):
        from donor_current_store import FollowStore
        ha_coordinator.Store = FollowStore

    class PublicProcess(OwnedProcess):
        def __init__(self, state, name, argv):
            if name == 'ha-service':
                expected = [sys.executable, str(Path(ha_coordinator.__file__).with_name('ha_service.py')),
                            str(Path(state)/'ha-service.json')]
                if argv != expected:
                    raise ValueError('ORIGINAL_HA_CHILD_CHANGED')
                argv = [sys.executable, str(Path(__file__).resolve()), 'writer', argv[-1]]
            super().__init__(state, name, argv)

        def start(self):
            # This maintenance inhibit can only defer a child. Removing it
            # grants no request authority; TLS, source and quorum gates remain.
            if self.name == 'ha-service' and current.get('writer_inhibit') and Path(current['writer_inhibit']).exists():
                return False
            return super().start()

    # Dependency injection leaves the original grant/intent/failover loop intact.
    ha_coordinator.OwnedProcess = PublicProcess
    sys.argv = [sys.argv[0], str(path)]
    try:
        ha_coordinator.main()
    finally:
        import governance, energy
        governance.close_readers()
        energy.close_readers()


def host(home):
    config = json.loads((home/'config.json').read_text())
    ha_timing.public_configuration(config)
    native_spare.admission(config)
    lock = (home/'host.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    state = home/'state'
    state.mkdir(exist_ok=True)
    process = OwnedProcess(state, 'anchor', [sys.executable, str(Path(__file__).resolve()),
                                           'anchor', str(home/'config.json')])
    key = app_private(home/'pki/anchor')
    try:
        while not (home/'STOP').exists():
            process.start()
            save(home/'status.json', sign(key, 'recovery-host-status', {
                'boot': boot_identity(), 'source': native_spare.point_source(config), 'cluster': config['cluster'],
                'process': process.record, 'at': time.time(), 'mode': 'ha_public_timing_native_spare_v1',
                'entrypoint': 'live_timing.py', 'admission': digest(config['native_admission'])}))
            time.sleep(1)
    finally:
        process.stop()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('role', choices=('coordinator', 'writer', 'anchor', 'host'))
    parser.add_argument('path', type=Path)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    if args.role == 'coordinator':
        coordinator(args.path)
    elif args.role == 'writer':
        writer(json.loads(args.path.read_text()))
    elif args.role == 'host':
        host(args.path)
    else:
        semantic_anchor.Journal = Journal
        sys.argv = [sys.argv[0], str(args.path)]
        semantic_anchor.main()


if __name__ == '__main__':
    main()
