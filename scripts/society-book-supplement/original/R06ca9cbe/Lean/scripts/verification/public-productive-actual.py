"""Commit productive admission and paid recovery through the original TLS service."""
import argparse
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from continuous_capture import Tap
from crypto import canonical
from recovery_loop import save
import energy,governance,productive_extension,productive_regeneration

import importlib.util
def module(name,filename):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
deploy=module('productive_actual_deploy','public-productive-deploy.py')
original=module('productive_actual_original','public-supply-actual.py')


def wait_runtime(box,manifest):
    # Cold reconstruction replays each already-paid public prefix separately.
    # This observes its existing supervisor; it never starts another replay.
    end=time.monotonic()+1800
    while True:
        states=original.continuous.epoch.states(box,manifest)
        active=[o for o,v in states.items() if v['body']['phase']=='leader' and time.time()-v['body']['at']<20]
        if len(active)==1:return active[0],states[active[0]]
        if time.monotonic()>=end:raise TimeoutError('PRODUCTIVE_PUBLIC_RUNTIME_NOT_READY')
        time.sleep(10)


def wait_prefix(box,manifest,expected):
    end=time.monotonic()+1800
    while original.continuous.rows(manifest)!=expected:
        if time.monotonic()>=end:raise TimeoutError('PRODUCTIVE_ORIGINAL_FOLLOWER_NOT_READY')
        time.sleep(10)
    original.continuous.wait_prefix(box,manifest,expected)


def run(box):
    lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=deploy.location(box);directory=home/'actual';directory.mkdir(exist_ok=True)
    manifest=deploy.load(box/'ha/deployment.json');before=original.continuous.rows(manifest)
    if not (directory/'before.json').exists():
        if dict(seq=len(before),head=before[-1][2])!=deploy.load(home/'admission.json')['point']['prefix']:
            raise ValueError('PRODUCTIVE_ACTIVATION_PARENT_MOVED')
        save(directory/'before.json',before)
    initial=deploy.load(directory/'before.json')
    if before[:len(initial)]!=initial:raise ValueError('PRODUCTIVE_ORIGINAL_PREFIX_CHANGED')
    owner,_=wait_runtime(box,manifest)
    from productive_readiness import commands
    continuation=commands()+[dict(kind='cycle',mode='normal') for _ in range(3)]+[dict(kind='service',query=dict(slots=63,fields=3)) for _ in range(2)]
    labels=['productive-admission']+['productive-'+str(n) for n in range(len(continuation))]
    modes=['normal']+continuation
    relay,thread=original.relay_for(box,manifest,owner)
    tap=Tap(relay.server_address[1],directory/('tls-'+str(len(list(directory.glob('tls-*.jsonl.gz')))+1)+'.jsonl.gz'),timeout=original.response_timeout(manifest[owner]['service']))
    try:
        results=[]
        for index,(label,mode) in enumerate(zip(labels,modes,strict=True)):
            results.append(original.submit(box,manifest,directory,tap.port,label,'2',productive_extension.EVENT if index==0 else productive_regeneration.KIND,mode))
            committed=initial+[[r['anchor']['body']['seq'],r['anchor']['body']['previous'],r['anchor']['body']['head'],canonical(r['ledger']).decode()] for r in results]
            visible=original.continuous.rows(manifest)
            if len(visible)>=len(committed):
                if visible[:len(committed)]!=committed:raise ValueError('PRODUCTIVE_SIGNED_PREFIX_CHANGED')
                if len(visible)==len(committed):wait_prefix(box,manifest,committed)
            else:wait_prefix(box,manifest,committed)
        # The local follower may trail the already signed final response.
        # Wait for that exact committed chain, never freeze the lagging snapshot.
        rows=initial+[[r['anchor']['body']['seq'],r['anchor']['body']['previous'],
            r['anchor']['body']['head'],canonical(r['ledger']).decode()] for r in results]
        wait_prefix(box,manifest,rows)
        if rows[:len(initial)]!=initial or len(rows)!=len(initial)+15:raise ValueError('PRODUCTIVE_DUPLICATE_OR_MISSING_EVENT')
        value,scope,current=productive_regeneration.context(manifest['mac']['service'],rows)
        save(directory/'source-input.json',value);save(directory/'events.json',rows)
        save(directory/'after.json',dict(rows=rows,current=current,scope=scope))
        save(directory/'public-complete.json',dict(events=len(rows),parent=len(initial),head=rows[-1][2],requests=14,owner=owner,physical_reboots=0))
        print('ACTUAL PRODUCTIVE LOOP PASS: original53 + admission +14 own successors; paid refusal/recovery; original-ID lookups',flush=True)
    finally:
        tap.close();relay.shutdown();relay.server_close();thread.join(3)
        governance.close_readers();energy.close_readers()


def close_and_audit(box):
    lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=deploy.location(box);directory=home/'actual';manifest=deploy.load(box/'ha/deployment.json')
    if (directory/'owner-accepted.json').exists():
        current=original.continuous.epoch.states(box,manifest)
        if not any(v['body']['phase'] in {'leader','recovering','standby'} and time.time()-v['body']['at']<20 for v in current.values()):
            original.continuous.resume_runtime(box,manifest)
        wait_runtime(box,manifest)
        save(directory/'resumed.json',dict(at=time.time(),states=original.continuous.epoch.states(box,manifest)))
        return
    if not (directory/'public-complete.json').exists():raise ValueError('ACTUAL_PRODUCTIVE_NOT_COMPLETE')
    rows=original.continuous.rows(manifest);save(directory/'events.json',rows)
    frozen={};transition=False
    try:
        for owner in ('spark','mac'):
            frozen[owner]=deploy.roll.freeze_writer(box,manifest,owner);save(directory/'audit-barrier.json',frozen)
        inventory={n:original.continuous.epoch.inventory(box,manifest,n) for n in 'abcd'}
        prior=deploy.load(directory/'inventories.json') if (directory/'inventories.json').exists() else []
        prior.append(inventory);save(directory/'inventories.json',prior);transition=True
        for owner in ('spark','mac'):deploy.prior.retire_writer(box,manifest,owner,frozen[owner])
        original.continuous.epoch.stop_anchors(manifest)
        save(directory/'closed.json',original.continuous.epoch.close_inventory(box,manifest,prior))
        for owner,member in [('mac','a'),('spark','c')]:
            journal=manifest[owner]['service']['online_privacy']['journal']
            for name,path in [('boundary',journal),('applications',journal+'.applications.jsonl')]:
                raw=deploy.execute(member,'from pathlib import Path\nprint(Path('+repr(path)+').read_text(),end="")',manifest,120)
                (directory/(owner+'-'+name+'.jsonl')).write_text(raw)
        subprocess.run([sys.executable,str(Path(__file__).with_name('public-productive-live-check.py')),str(box),'--closed'],check=True)
    finally:
        if transition:
            for owner,record in frozen.items():deploy.prior.retire_writer(box,manifest,owner,record)
            original.continuous.resume_runtime(box,manifest)
        else:
            for owner,record in frozen.items():deploy.roll.spare.writer_signal(box,manifest,owner,'SIGCONT',record)
    wait_runtime(box,manifest)
    save(directory/'resumed.json',dict(at=time.time(),states=original.continuous.epoch.states(box,manifest)))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--close',action='store_true');a=p.parse_args()
    if a.close:close_and_audit(a.box.resolve())
    else:run(a.box.resolve())
