"""Actual public epochs on the original two candidates, then a closed audit epoch."""
import argparse
import fcntl
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import sys
import threading
import time

import importlib.util
ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key
from crypto import canonical, verify
from ha_client import Relay, Handler as RelayHandler
from online_privacy_exercise import Tap, exchange
from recovery_loop import save

spec = importlib.util.spec_from_file_location('actual_timing_roll', Path(__file__).with_name('public-live-timing.py'))
roll = importlib.util.module_from_spec(spec)
spec.loader.exec_module(roll)
load, execute = roll.load, roll.execute


def states(box, manifest):
    value = {'mac': load(box/'runtime/ha-status.json')}
    item = manifest['nodes']['c']
    value['spark'] = json.loads(execute('c', 'from pathlib import Path\nprint(Path('+repr(item['home']+'/ha/runtime/ha-status.json')+').read_text())', manifest, 40))
    for owner, signed in value.items():
        body = verify(public_key(manifest['owners'][owner]), 'ha-coordinator', signed)
    return value


def wait_leader(box, manifest, wanted=None):
    end = time.monotonic()+240
    while time.monotonic() < end:
        current = states(box, manifest)
        active = [o for o, v in current.items() if v['body']['phase'] == 'leader' and time.time()-v['body']['at'] < 20]
        if len(active) == 1 and (wanted is None or active == [wanted]):
            return active[0], current[active[0]]
        time.sleep(2)
    raise TimeoutError('ORIGINAL_PUBLIC_LEADER_NOT_READY:'+repr({o: (v['body']['phase'],v['body']['error']) for o,v in current.items()}))


def epoch(box, manifest, owner, signed):
    home = box/'ha/live-timing'
    directory = home/('epoch-'+owner)
    directory.mkdir(exist_ok=True)
    assert not any(directory.iterdir()), 'resume the existing epoch before issuing more queries'
    cfg = manifest[owner]['service']
    member = 'a' if owner == 'mac' else 'c'
    ready_path = str(Path(cfg['database']).parent/'ha-service-ready.json')
    ready = json.loads(execute(member, 'from pathlib import Path\nprint(Path('+repr(ready_path)+').read_text())', manifest, 40))
    rb = verify(public_key(cfg['registry']['server']), 'ha-service-ready', ready)
    assert rb['public_timing']['entrypoint'] == 'live_timing.py'
    assert rb['grant']['point'] == signed['body']['grant']['point']
    address = load(box/'ha/addresses.json')[member]
    client_cfg = {**cfg, 'pki': manifest['mac']['service']['pki']}
    observations = []
    with Relay(('127.0.0.1', 0), RelayHandler) as relay:
        relay.target = (address, cfg['port'])
        thread = threading.Thread(target=relay.serve_forever, kwargs={'poll_interval': .1}, daemon=True)
        thread.start()
        tap = Tap(relay.server_address[1], directory/'tls-1.jsonl.gz')
        try:
            for row in load(home/'original-events.json')[24:]:
                body = json.loads(row[3])['body']['request']['body']
                for repeat in range(2):
                    value = exchange(client_cfg, tap.port, body['actor'], None, lookup=body['request_id'])
                    result = verify(public_key(cfg['registry']['server']), 'lookup-response', value['body']['response'])['result']
                    assert result['ledger'] == json.loads(row[3]) and result['head'] == row[2]
                    observations.append(value)
                    save(directory/'observations.json', observations)
        finally:
            tap.close()
            relay.shutdown()
            thread.join()
    journal = cfg['online_privacy']['journal']
    raw = execute(member, 'from pathlib import Path\nprint(Path('+repr(journal)+').read_text(),end="")', manifest, 40)
    (directory/'boundary.jsonl').write_text(raw)
    assert [list(r) for r in roll.spare.rows(manifest['mac']['service']['database'])] == load(home/'original-events.json')
    print('ACTUAL PUBLIC CANDIDATE '+owner+': original25/26/27 replied twice; full TLS retained; no new event/payment', flush=True)
    result = {'owner': owner, 'state': signed, 'ready': ready, 'finished_ns': time.monotonic_ns()}
    save(directory/'epoch.json', result)
    return result


def inventory(box, manifest, member):
    roots = []
    if member == 'a':
        roots.append(load(box/'runtime/ha-status.json')['body']['pid'])
        home = str(box/'local-anchor')
        codepath = str(NETWORK)
    else:
        home = manifest['nodes'][member]['home']
        codepath = manifest['nodes'][member]['code']
    script = f'''import json,os,subprocess,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from crypto import app_private,sign
p=Path({home!r});roots={roots!r}
raw=subprocess.check_output(['ps','-axo','pid=,ppid=,uid=,command='],text=True)
rows=[]
for line in raw.splitlines():
 a=line.strip().split(None,3)
 if len(a)==4:rows.append((int(a[0]),int(a[1]),int(a[2]),a[3]))
if {member!='a'!r}:
 anchor=json.loads((p/'status.json').read_text())['body']['process']['pid']
 parent=next(r[1] for r in rows if r[0]==anchor)
 assert 'live_timing.py host ' in next(r[3] for r in rows if r[0]==parent)
 roots.append(parent)
if {member=='c'!r}:roots.append(json.loads((p/'ha/runtime/ha-status.json').read_text())['body']['pid'])
owned=set(roots)
while True:
 children={{r[0] for r in rows if r[1] in owned and r[2]==os.getuid()}}
 if children<=owned:break
 owned|=children
processes=[{{'pid':a,'parent':b,'birth':birth(a),'command':c}} for a,b,u,c in rows if a in owned and u==os.getuid()]
assert all('private-two' not in r['command'] and '__private_audit' not in r['command'] for r in processes)
print(json.dumps(sign(app_private(p/'pki/anchor'),'public-epoch-inventory',{{'member':{member!r},'boot':boot_identity(),'processes':processes,'source':{manifest['source']!r}}})))
'''
    return json.loads(execute(member, script, manifest, 45))


def stop_anchors(manifest):
    for member in 'bcd':
        if member == 'd':
            execute(member, "import os,subprocess\nfrom pathlib import Path\np=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist'\nsubprocess.run(['launchctl','bootout','gui/'+str(os.getuid()),str(p)],check=True)", manifest, 60)
        else:
            roll.spare.transport.node(member).wsl(('sudo -n ' if member == 'c' else '')+'systemctl '+('--user ' if member == 'b' else '')+'stop homework-public-anchor-recovery.service\n', 90, allow_probe=False)


def close_inventory(box, manifest, inventories):
    closed = {}
    for member in 'abcd':
        home_node = str(box/'local-anchor') if member == 'a' else manifest['nodes'][member]['home']
        codepath = str(NETWORK) if member == 'a' else manifest['nodes'][member]['code']
        reports = [verify(public_key(manifest['trust']['members'][member]), 'public-epoch-inventory', item[member]) for item in inventories]
        processes = { (p['pid'], p['birth']): p for r in reports for p in r['processes'] }
        report = {**reports[-1], 'processes': list(processes.values())}
        script = f'''import json,sys,time,os,signal
from pathlib import Path
sys.path.insert(0,{codepath!r})
from recovery_loop import birth,boot_identity
from crypto import app_private,sign
r={report!r};assert r['boot']==boot_identity()
retired=[]
for p in r['processes']:
 if p['birth'] and birth(p['pid'])==p['birth']:
  os.kill(p['pid'],signal.SIGTERM);retired.append(p)
end=time.monotonic()+2
while time.monotonic()<end and any(birth(p['pid'])==p['birth'] for p in retired):time.sleep(.1)
for p in retired:
 if birth(p['pid'])==p['birth']:os.kill(p['pid'],signal.SIGKILL)
end=time.monotonic()+5
while time.monotonic()<end and any(birth(p['pid'])==p['birth'] for p in retired):time.sleep(.1)
remaining=[p for p in r['processes'] if birth(p['pid'])==p['birth']]
assert not remaining,remaining
print(json.dumps(sign(app_private(Path({home_node!r})/'pki/anchor'),'public-epoch-closed',{{**r,'remaining':remaining,'closed_at':time.time(),'retired_after_owner_exit':retired}})))
'''
        closed[member] = json.loads(execute(member, script, manifest, 45))
    return closed


def resume(box, manifest):
    for member in 'bcd':
        if member == 'd':
            execute(member, "import os,subprocess\nfrom pathlib import Path\np=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist'\nsubprocess.run(['launchctl','bootstrap','gui/'+str(os.getuid()),str(p)],check=True)", manifest, 60)
        else:
            roll.spare.transport.node(member).wsl(('sudo -n ' if member == 'c' else '')+'systemctl '+('--user ' if member == 'b' else '')+'start homework-public-anchor-recovery.service\n', 90, allow_probe=False)
    item = manifest['nodes']['c']
    execute('c', 'from pathlib import Path\nPath('+repr(item['home']+'/ha/runtime/STOP')+').unlink(missing_ok=True)', manifest, 40)
    roll.spare.transport.node('c').wsl('sudo -n systemctl restart homework-public-source-ha.service\n', 90, allow_probe=False)
    roll.module('timing_epoch_stop', 'public-recovery-isolation.py').stop(box)
    (box/'runtime/STOP').unlink(missing_ok=True)
    subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'), str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
                    sys.executable, '-u', str(NETWORK/'live_timing.py'), 'coordinator', str(box/'ha/mac/controller.json')], check=True, capture_output=True)
    save(box/'ha/live-timing/resumed.json', {'at_ns': time.monotonic_ns(), 'source': manifest['source']})


def run(box):
    home = box/'ha/live-timing'
    manifest = load(box/'ha/deployment.json')
    if (home/'owner-nexts.json').exists() and (home/'privacy-independent/accepted.json').exists() and (home/'resumed.json').exists():
        subprocess.run([sys.executable, str(Path(__file__).with_name('public-live-timing-check.py')), str(box)], check=True)
        print('ORIGINAL LIVE TIMING ALREADY PAID: independently checked; no repeated epoch or private replay', flush=True)
        return
    if not (home/'epochs.json').exists():
        paid = list(home.glob('epoch-*/epoch.json'))
        if paid:
            assert len(paid) == 1
            epochs = [load(paid[0])];first = epochs[0]['owner']
        else:
            first, state = wait_leader(box, manifest)
            epochs = [epoch(box, manifest, first, state)]
        frozen = roll.freeze_writer(box, manifest, first)
        try:
            second = 'spark' if first == 'mac' else 'mac'
            _, state = wait_leader(box, manifest, second)
            epochs.append(epoch(box, manifest, second, state))
            save(home/'epochs.json', epochs)
        finally:
            roll.spare.writer_signal(box, manifest, first, 'SIGCONT', frozen)
    frozen = {}
    try:
        for owner in ('spark', 'mac'):
            frozen[owner] = roll.freeze_writer(box, manifest, owner)
            save(home/'audit-barrier.json', frozen)
        inventories = {m: inventory(box, manifest, m) for m in 'abcd'}
        prior = load(home/'public-inventories.json') if (home/'public-inventories.json').exists() else []
        if isinstance(prior, dict):prior = [prior]
        prior.append(inventories)
        save(home/'public-inventories.json', prior)
        for owner in ('spark', 'mac'):
            roll.retire_writer(box, manifest, owner, frozen[owner])
        stop_anchors(manifest)
        closed = close_inventory(box, manifest, prior)
        save(home/'closed.json', closed)
        subprocess.run([sys.executable, str(Path(__file__).with_name('public-live-timing-check.py')), str(box), '--frames'], check=True)
        audit_out = home/'privacy-independent'
        subprocess.run([sys.executable, str(Path(__file__).with_name('public-privacy-audit.py')), str(box),
                        str(box.parent/'privacy/accepted-03'), str(audit_out)], check=True)
    finally:
        resume(box, manifest)
    wait_leader(box, manifest)
    subprocess.run([sys.executable, str(Path(__file__).with_name('public-live-timing-check.py')), str(box)], check=True)
    print('ACTUAL ORIGINAL LIVE TIMING EPOCHS COMPLETE: dual takeover; closed private audit; original runtime resumed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box', type=Path)
    args = parser.parse_args()
    lock = (args.box.resolve()/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    run(args.box.resolve())
