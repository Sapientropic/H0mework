"""Activate a pre-enrolled source verifier without rewriting its historical policy."""
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

import anchor
from crypto import app_private, canonical, digest, sign, verify
from recovery_loop import OwnedProcess, boot_identity, save
import semantic_anchor


def admission(config):
    certificate = config['native_admission']
    point = certificate['point']
    trust = config['ha']['trust']
    if (set(point) != {'source', 'stream', 'cluster', 'prefix', 'previous', 'current', 'descriptors'}
            or point['cluster'] != config['cluster'] or point['previous'] != list('abc')
            or point['current'] != list('abcd') or config['governance_members'] != point['current']
            or point['source'] != config['semantic_policy']['source']
            or point['stream'] != config['semantic_policy']['stream']):
        raise ValueError('NATIVE_ADMISSION_BINDING')
    descriptors = {'base': config['semantic']['descriptor'],
                   **{name: config[name]['descriptor'] for name in ('governance', 'energy', 'continuation', 'handoff')}}
    if point['descriptors'] != descriptors:
        raise ValueError('NATIVE_ADMISSION_SOURCE')
    members = []
    for entry in certificate['votes']:
        member = entry['member']
        if member not in trust['members']:
            raise ValueError('NATIVE_ADMISSION_MEMBER')
        value = verify(anchor.public_key(trust['members'][member]), 'native-source-ready', entry['receipt'])
        if value['point'] != point or value['member'] != member or value['compiler'] != descriptors['base']['compiler']:
            raise ValueError('NATIVE_ADMISSION_READY')
        members.append(member)
    # All existing source verifiers and the new pre-enrolled verifier attest
    # their own actual replay of this same committed prefix.
    if members != list('abcd'):
        raise ValueError('NATIVE_ADMISSION_COVERAGE')
    return point


class Journal(semantic_anchor.Journal):
    def __init__(self, config):
        point = admission(config)
        historical = copy.deepcopy(config)
        historical['governance_members'] = point['previous']
        historical['semantic'].update(background_warmup=False, warm_on_start=False)
        super().__init__(historical)
        try:
            row = self.db.execute('SELECT hash FROM entries WHERE stream=? AND seq=?',
                                  (point['stream'], point['prefix']['seq'])).fetchone()
            if row != (point['prefix']['head'],):
                raise ValueError('NATIVE_ADMISSION_PREFIX')
            self.db.execute('CREATE TABLE IF NOT EXISTS native_admission(value TEXT NOT NULL UNIQUE)')
            value = canonical(config['native_admission']).decode()
            prior = self.db.execute('SELECT value FROM native_admission').fetchall()
            if not prior:
                self.db.execute('INSERT INTO native_admission VALUES(?)', (value,))
            elif prior != [(value,)]:
                raise ValueError('NATIVE_ADMISSION_CHANGED')
            self.config = config
        except BaseException:
            self.stop_warming.set()
            self.engine.close()
            self.db.close()
            raise
        if config['semantic'].get('background_warmup', False):
            self.warm_error = 'SOURCE_REPLAY_PENDING'
            self.warmer = threading.Thread(target=self.warm_loop, daemon=True)
            self.warmer.start()


def host(home):
    config = json.loads((home/'config.json').read_text())
    admission(config)
    lock = (home/'host.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    state = home/'state'
    state.mkdir(exist_ok=True)
    process = OwnedProcess(state, 'anchor', [sys.executable, str(Path(__file__).resolve()), 'anchor', str(home/'config.json')])
    key = app_private(home/'pki/anchor')
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    try:
        while not (home/'STOP').exists():
            process.start()
            save(home/'status.json', sign(key, 'recovery-host-status', {
                'boot': boot_identity(), 'source': point_source(config), 'cluster': config['cluster'],
                'process': process.record, 'at': time.time(), 'mode': 'ha_fenced_native_spare_v1',
                'entrypoint': 'native_spare.py', 'admission': digest(config['native_admission'])}))
            time.sleep(1)
    finally:
        process.stop()


def point_source(config):
    return next(iter(config['streams'].values()))['source']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('role', choices=('host', 'anchor'))
    parser.add_argument('path', type=Path)
    args = parser.parse_args()
    if args.role == 'host':
        host(args.path)
    else:
        semantic_anchor.Journal = Journal
        sys.argv = [sys.argv[0], str(args.path)]
        semantic_anchor.main()


if __name__ == '__main__':
    main()
