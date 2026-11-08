"""Native-manager host for HA anchors; original signing key and journal retained."""
import json
import os
from pathlib import Path
import signal
import sys
import time
import fcntl

from crypto import app_private, sign
from recovery_loop import OwnedProcess, boot_identity, save


def main():
    home = Path(sys.argv[1]); config = json.loads((home/'config.json').read_text())
    lock = (home/'host.lock').open('a'); fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    state = home/'state'; state.mkdir(exist_ok=True)
    entrypoint = config.get('anchor_entrypoint', 'ha_anchor.py')
    if entrypoint not in {'ha_anchor.py', 'semantic_anchor.py'}:
        raise ValueError('HA_ANCHOR_ENTRYPOINT')
    if entrypoint == 'semantic_anchor.py' and not config.get('semantic'):
        raise ValueError('SEMANTIC_CONFIGURATION_REQUIRED')
    process = OwnedProcess(state, 'anchor', [sys.executable, str(Path(__file__).with_name(entrypoint)), str(home/'config.json')])
    key = app_private(home/'pki/anchor')
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    try:
        while not (home/'STOP').exists():
            process.start()
            save(home/'status.json', sign(key, 'recovery-host-status', {
                'boot': boot_identity(), 'source': next(iter(config['streams'].values()))['source'],
                'cluster': config['cluster'], 'process': process.record, 'at': time.time(),
                'mode': 'ha_fenced_v1', 'entrypoint': entrypoint}))
            time.sleep(1)
    finally:
        process.stop()


if __name__ == '__main__':
    main()
