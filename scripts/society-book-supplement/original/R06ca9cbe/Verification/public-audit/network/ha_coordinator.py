"""Two pre-enrolled physical candidates; the anchors fence every actual write."""
from concurrent.futures import ThreadPoolExecutor
import fcntl
import json
import os
from pathlib import Path
import signal
import sqlite3
import sys
import time

from anchor import public_key
from crypto import app_private, digest, sign, verify
from ha_quorum import Quorum, Reader
from service import Store
from recovery_loop import OwnedProcess, birth, boot_identity, save


def follow(service, reader):
    if not Path(service['database']).exists():
        return None
    lock_id = digest({'source': service['source'], 'stream': service['stream'], 'trust': service['anchors']['trust']})
    with (Path(service['pki'])/'server'/(lock_id+'.writer.lock')).open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        store = object.__new__(Store)
        store.config = service; store.key = app_private(Path(service['pki'])/'server')
        store.anchor = reader; store.pending_path = Path(service['database']+'.pending.json')
        store.database = sqlite3.connect(service['database'], isolation_level=None)
        try:
            store.reconcile_pending(True); store.reconcile_anchor(True); store.clear_pending()
            return {'seq': len(store.anchor.entries), 'head': store.head(),
                    'source': service['source'], 'stream': service['stream']}
        finally:
            store.database.close()


def native_rejoin_required(members,point,states):
    return any(name in members and state['remaining_ns']==0 and
               all(state[key]==point[key] for key in ('owner','epoch','lease_id'))
               for name,state in states.items())


def main():
    path = Path(sys.argv[1]); config = json.loads(path.read_text()); state = Path(config['state'])
    state.mkdir(parents=True, exist_ok=True)
    lock = (state/'ha-coordinator.lock').open('a'); fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    service = json.loads(Path(config['service']).read_text()); owner = service['ha']['owner']
    key = app_private(Path(service['ha']['owner_profile'])); signer = public_key(service['registry']['server'])
    grant = None; grant_path = state/'grant.json'
    if grant_path.exists():
        grant = json.loads(grant_path.read_text())
    child_config = state/'ha-service.json'
    child = OwnedProcess(state, 'ha-service', [sys.executable, str(Path(__file__).with_name('ha_service.py')), str(child_config)])
    members = {name: OwnedProcess(state, 'ha-member-'+name, argv) for name, argv in config.get('members', {}).items()}
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(SystemExit(0)))
    last = None; retiring = None; q = Quorum(service); reader = Reader(service)
    q.proposal_path = state/'proposal.json'
    try:
        while not (state/'STOP').exists():
            for process in members.values():
                process.start()
            error = None; phase = 'standby'; head = None
            try:
                if retiring or grant:
                    states=q.collect('status')
                    if retiring:
                        if len(states)<3 or any(state['remaining_ns']>0 and
                            all(state[key]==retiring[key] for key in ('owner','epoch','lease_id'))
                            for state in states.values()):
                            raise ValueError('NATIVE_VOTER_LEASE_REJOIN')
                        retiring=None
                    elif native_rejoin_required(service.get('governance_members',()),grant['point'],states):
                        # An expired returning native voter cannot rejoin this
                        # token. Let it expire before acquiring a fresh term.
                        retiring=grant['point'];child.stop();grant=None
                        raise ValueError('NATIVE_VOTER_LEASE_REJOIN')
                try:
                    grant = q.grant(grant)
                except ValueError:
                    child.stop(); grant = q.grant()
                save(grant_path, grant)
                service['ha']['grant'] = grant
                if not child.alive():
                    head = q.recover()
                    save(child_config, service); child.start()
                ready_path = Path(service['database']).parent/'ha-service-ready.json'
                if ready_path.exists():
                    ready = verify(signer, 'ha-service-ready', json.loads(ready_path.read_text()))
                    if (ready['grant']['point'] == grant['point'] and birth(ready['pid']) == ready['birth']
                            and child.alive() and os.getpgid(ready['pid']) == child.record['pgid']):
                        backend = ready.get('backend')
                        if (backend and birth(backend['pid']) == backend['birth'] and
                                os.getpgid(backend['pid']) == child.record['pgid']):
                            phase = 'leader'; head = q.head()
                        else:
                            child.stop(); phase = 'recovering'
                    else:
                        phase = 'recovering'
                else:
                    phase = 'recovering'
            except Exception as problem:
                error = type(problem).__name__+': '+str(problem); child.stop()
                grant = None
                try:
                    head = follow(service, reader)
                except Exception as follow_error:
                    error += '; follow: '+type(follow_error).__name__+': '+str(follow_error)
            body = {'phase': phase, 'error': error, 'owner': owner, 'source': service['source'],
                    'stream': service['stream'], 'grant': grant, 'head': head,
                    'boot': boot_identity(), 'pid': os.getpid(), 'birth': birth(os.getpid()),
                    'service': child.record, 'members': {name: value.record for name, value in members.items()},
                    'configuration': digest(config), 'at': time.time()}
            save(state/'ha-status.json', sign(key, 'ha-coordinator', body))
            marker = (phase, error, grant['point']['epoch'] if grant else None)
            if marker != last:
                with (state/'ha-events.jsonl').open('a') as output:
                    output.write(json.dumps(sign(key, 'ha-coordinator', body))+'\n'); output.flush(); os.fsync(output.fileno())
                print(json.dumps(body), flush=True); last = marker
            end = time.monotonic()+config.get('interval', 2)
            while time.monotonic() < end and not (state/'STOP').exists():
                time.sleep(.1)
    finally:
        child.stop()
        for process in members.values():
            process.stop()
        from governance import close_readers
        close_readers()
        from energy import close_readers as close_energy_readers
        close_energy_readers()


if __name__ == '__main__':
    main()
