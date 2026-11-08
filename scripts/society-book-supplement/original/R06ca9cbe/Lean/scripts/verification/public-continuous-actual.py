"""New original requests across closed public epochs, retaining unknown intents."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import importlib.util
import json
from pathlib import Path
import secrets
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import public_key
from crypto import app_private, canonical, connect, digest, peer, receive, send, sign, verify
from ha_client import Relay, Handler as RelayHandler
from continuous_capture import Tap
from recovery_loop import save
import handoff


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec);spec.loader.exec_module(value)
    return value


roll = module('continuous_roll', 'public-live-timing.py')
epoch = module('continuous_epoch', 'public-live-timing-actual.py')
original = module('continuous_owner', 'public-handoff-actual.py')
load, sha = roll.load, roll.sha
PLANS = [[('2',{'slots':1,'fields':3}),('1',{'slots':2,'fields':1})],
         [('2',{'slots':63,'fields':3}),('2',{'slots':1,'fields':3})]]


def rows(manifest):
    return [list(r) for r in roll.spare.rows(manifest['mac']['service']['database'])]


def wait_prefix(box, manifest, expected):
    from ha_quorum import Quorum
    q = Quorum(manifest['mac']['service'])
    end = time.monotonic()+200
    while time.monotonic() < end:
        local = rows(manifest)
        if local == expected:
            try:
                states = {n:c.call('semantic-status') for n,c in q.nodes.items()}
                if all(s['prefix'] == {'seq':len(expected),'head':expected[-1][2]} and s['backend']
                       and not s['warm_error'] for s in states.values()):
                    return
            except (ValueError, OSError, EOFError):
                pass
        time.sleep(1)
    raise TimeoutError('CONTINUOUS_COMMITTED_PREFIX_NOT_READY')


def setup(box):
    home = box/'ha/continuous';home.mkdir(exist_ok=True)
    manifest = load(box/'ha/deployment.json')
    if manifest.get('continuous_epochs'):
        assert manifest['continuous_epochs']['evidence'] == str(home)
        return home, manifest
    literal = rows(manifest)
    assert len(literal) == 27
    baseline = home/'baseline';baseline.mkdir(exist_ok=True)
    final = load(box/'ha/handoff/final-check.json')
    integration = load(box/'ha/live-timing/main-verified.json')
    assert final['exit'] == 0 and final['full'] and final['main_verified']
    assert final['events'] == 27 and final['head'] == literal[-1][2]
    commit = integration['commit']
    subprocess.run(['git','merge-base','--is-ancestor',commit,'refs/heads/main'],cwd=ROOT,check=True)
    import hashlib
    for path, wanted in final['inputs'].items():
        assert hashlib.sha256(subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)).hexdigest() == wanted
    save(baseline/'events.json', literal)
    save(baseline/'full.json', final)
    save(baseline/'main.json', integration)
    save(baseline/'deployment.json', manifest)
    save(home/'resource-plan.json', {'owner':'process-generated-society','consumer':'default continuous public-source audit',
        'existing_node_states':['public-anchor-'+n+'-20261102' for n in ('pc','spark','studio')],
        'new_jobs':0,'new_remote_libraries':0,'max_new_local_mib':64,'host_reboots':0})
    manifest['continuous_epochs'] = {'evidence':str(home),'baseline_commit':commit,
        'baseline_receipt':sha(baseline/'full.json'),'baseline':{'seq':27,'head':literal[-1][2]}}
    save(box/'ha/deployment.json', manifest)
    return home, manifest


def observe(box, manifest, directory, port, label, actor, query=None, lookup=None):
    cfg = manifest['mac']['service'];profile = Path(cfg['pki'])/('auditor'+actor)
    times = {'connect_start_ns':time.monotonic_ns()}
    with connect(profile, port) as connection:
        connection.settimeout(90)
        times['connected_ns'] = time.monotonic_ns()
        uri, fingerprint, key = peer(connection)
        assert uri == 'urn:public-audit:server' and fingerprint == cfg['registry']['server']['fingerprint']
        challenge = receive(connection);issued = verify(key,'challenge',challenge)
        times['challenge_received_ns'] = time.monotonic_ns()
        if lookup is not None:
            request = sign(app_private(profile),'lookup',{**issued,'lookup_id':lookup,'request_id':secrets.token_hex(16)})
        else:
            prefix = rows(manifest)
            _,_,current = handoff.context(cfg,prefix)
            assert (current['cut'],current['version']) == (issued['cut'],issued['epoch'])
            body = original.authorize(box,cfg,prefix,'read',query,directory,label,actor)
            request = sign(app_private(profile),'energy-handoff',{**issued,**body,'request_id':secrets.token_hex(16)})
        # The complete original request survives observer exit before any send.
        save(directory/(label+'-request.json'),request)
        save(directory/(label+'-challenge.json'),challenge)
        times['request_sent_ns'] = time.monotonic_ns()
        send(connection,request)
        try:
            response = receive(connection);verify(key,response['kind'],response)
        except (OSError,EOFError) as problem:
            response = {'transport_error':type(problem).__name__}
        times['response_received_ns'] = time.monotonic_ns()
        cipher = connection.cipher()
        observation = sign(app_private(profile),'online-client-observation',{
            'peer':{'uri':uri,'fingerprint':fingerprint,'app':key.public_bytes_raw().hex()},
            'tls':connection.version(),'cipher':cipher[0] if cipher else None,
            'challenge':challenge,'request':request,'response':response,'times':times})
        save(directory/(label+'-observation.json'),observation)
        return observation


def lookup_twice(box, manifest, directory, port, label, original_request):
    for repeat in range(2):
        value = observe(box,manifest,directory,port,label+'-lookup-'+str(repeat),
            original_request['body']['actor'],lookup=original_request['body']['request_id'])
        envelope = verify(public_key(manifest['mac']['service']['registry']['server']),'lookup-response',value['body']['response'])
        assert envelope['result']['event']['request'] == original_request


def relay_for(box, manifest, owner):
    relay = Relay(('127.0.0.1',0),RelayHandler)
    relay.target = (load(box/'ha/addresses.json')['a' if owner=='mac' else 'c'],manifest[owner]['service']['port'])
    thread = threading.Thread(target=relay.serve_forever,kwargs={'poll_interval':.1},daemon=True);thread.start()
    return relay, thread


def batch(box, manifest, directory, plan, fault=False):
    directory.mkdir(exist_ok=True)
    if (directory/'public-complete.json').exists():
        return
    before = load(directory/'before.json') if (directory/'before.json').exists() else rows(manifest)
    assert rows(manifest)[:len(before)] == before
    save(directory/'before.json',before)
    owner, state = epoch.wait_leader(box,manifest,'mac' if fault else None)
    if not (directory/'start.json').exists():save(directory/'start.json',{'owner':owner,'state':state})
    relay, thread = relay_for(box,manifest,owner)
    attempt=max([int(p.name.split('-')[1].split('.')[0]) for p in directory.glob('tls-*.jsonl.gz')]+[0])+1
    tap = Tap(relay.server_address[1],directory/('tls-'+str(attempt)+'.jsonl.gz'))
    observations = []
    try:
        for index,(actor,query) in enumerate(plan):
            label = 'step-'+str(index)
            paid=[directory/(label+s+'.json') for s in ('-observation','-lookup-0-observation','-lookup-1-observation')]
            if all(p.exists() for p in paid):
                observations.append(load(paid[0]))
                continue
            if (directory/(label+'-request.json')).exists():
                request=load(directory/(label+'-request.json'))
                assert request['body']['actor']==actor and request['body']['query']==query
                assert (directory/(label+'-observation.json')).exists(), 'ORIGINAL_SUBMISSION_OBSERVATION_REQUIRED'
                observations.append(load(directory/(label+'-observation.json')))
                for repeat in range(2):
                    if not (directory/(label+'-lookup-'+str(repeat)+'-observation.json')).exists():
                        value=observe(box,manifest,directory,tap.port,label+'-lookup-'+str(repeat),actor,lookup=request['body']['request_id'])
                        assert value['body']['response']['kind']=='lookup-response'
                save(directory/'observations.json',observations)
                continue
            if fault and index == len(plan)-1:
                arm = box/'ha-fault-arm.json'
                assert not arm.exists()
                for name in ('ha-fault-boundary.json','ha-fault-consumed.json'):
                    if (box/name).exists():(directory/('prior-'+name)).write_bytes((box/name).read_bytes())
                save(arm,{'phase':'after-source','owner':owner})
                frozen = None
                try:
                    save(directory/'before-fault.json',epoch.states(box,manifest))
                    with ThreadPoolExecutor(max_workers=1) as pool:
                        pending = pool.submit(observe,box,manifest,directory,tap.port,label,actor,query)
                        end = time.monotonic()+50
                        while time.monotonic() < end:
                            if (box/'ha-fault-boundary.json').exists() and (directory/(label+'-request.json')).exists():
                                boundary = load(box/'ha-fault-boundary.json')
                                if boundary['body'].get('message',{}).get('body',{}).get('request') == load(directory/(label+'-request.json')):
                                    break
                            if pending.done():raise RuntimeError('SOURCE_BOUNDARY_NOT_REACHED:'+repr(pending.result()))
                            time.sleep(.1)
                        else:raise TimeoutError('SOURCE_BOUNDARY_NOT_REACHED')
                        save(directory/'boundary.json',boundary)
                        save(directory/'pending.json',load(Path(manifest['mac']['service']['database']+'.pending.json')))
                        frozen = roll.freeze_writer(box,manifest,owner)
                        save(directory/'isolated.json',frozen)
                        _, takeover = epoch.wait_leader(box,manifest,'spark')
                        save(directory/'takeover.json',takeover)
                        observations.append(pending.result(timeout=100))
                    relay2, thread2 = relay_for(box,manifest,'spark')
                    tap2 = Tap(relay2.server_address[1],directory/('tls-'+str(attempt+1)+'.jsonl.gz'))
                    try:lookup_twice(box,manifest,directory,tap2.port,label,load(directory/(label+'-request.json')))
                    finally:
                        tap2.close();relay2.shutdown();relay2.server_close();thread2.join()
                finally:
                    if frozen:roll.spare.writer_signal(box,manifest,owner,'SIGCONT',frozen)
            else:
                value = observe(box,manifest,directory,tap.port,label,actor,query)
                observations.append(value)
                assert value['body']['response']['kind'] == 'response',value['body']['response']
                request = load(directory/(label+'-request.json'))
                lookup_twice(box,manifest,directory,tap.port,label,request)
            save(directory/'observations.json',observations)
            expected=list(before)
            for prior in range(index+1):
                receipt=load(directory/('step-'+str(prior)+'-lookup-1-observation.json'))['body']['response']
                result=verify(public_key(manifest['mac']['service']['registry']['server']),'lookup-response',receipt)['result']
                point=result['anchor']['body']
                expected.append([point['seq'],point['previous'],point['head'],canonical(result['ledger']).decode()])
            wait_prefix(box,manifest,expected)
    finally:
        tap.close();relay.shutdown();relay.server_close();thread.join()
    after = rows(manifest)
    save(directory/'events.json',after)
    for name in ('mac','spark'):
        member = 'a' if name=='mac' else 'c'
        value = roll.execute(member,'from pathlib import Path\nprint(Path('+repr(manifest[name]['service']['online_privacy']['journal'])+').read_text(),end="")',manifest,45)
        (directory/(name+'-boundary.jsonl')).write_text(value)
    save(directory/'public-complete.json',{'before':len(before),'after':len(after),'head':after[-1][2]})
    print('ACTUAL NEW PUBLIC BATCH:',len(before),'->',len(after),'; new signed requests, exact duplicate lookups, original intents retained',flush=True)


def close_and_audit(box, manifest, directory):
    if (directory/'accepted.json').exists():
        current=epoch.states(box,manifest)
        if not any(v['body']['phase']=='leader' and time.time()-v['body']['at']<20 for v in current.values()):
            resume_runtime(box,manifest)
        epoch.wait_leader(box,manifest)
        if not (directory/'resumed.json').exists():
            save(directory/'resumed.json',{'at':time.time(),'state':epoch.states(box,manifest)})
        return
    frozen = {}
    transition = False
    try:
        for owner in ('spark','mac'):
            frozen[owner] = roll.freeze_writer(box,manifest,owner)
            save(directory/'audit-barrier.json',frozen)
        inventory = {m:epoch.inventory(box,manifest,m) for m in 'abcd'}
        prior = load(directory/'inventories.json') if (directory/'inventories.json').exists() else []
        prior.append(inventory);save(directory/'inventories.json',prior)
        transition = True
        for owner in ('spark','mac'):roll.retire_writer(box,manifest,owner,frozen[owner])
        epoch.stop_anchors(manifest)
        save(directory/'closed.json',epoch.close_inventory(box,manifest,prior))
        subprocess.run([sys.executable,str(Path(__file__).with_name('public-continuous-check.py')),str(box),'--epoch',str(directory),'--closed'],check=True)
    finally:
        if transition:
            for owner,record in frozen.items():roll.retire_writer(box,manifest,owner,record)
            resume_runtime(box,manifest)
        else:
            for owner,record in frozen.items():roll.spare.writer_signal(box,manifest,owner,'SIGCONT',record)
    epoch.wait_leader(box,manifest)
    save(directory/'resumed.json',{'at':time.time(),'state':epoch.states(box,manifest)})


def resume_runtime(box,manifest):
    for member in 'bcd':
        if member == 'd':
            roll.execute(member,"import os,subprocess\nfrom pathlib import Path\nd='gui/'+str(os.getuid());p=Path.home()/'Library/LaunchAgents/com.homework.public-anchor-recovery.plist'\nif subprocess.run(['launchctl','print',d+'/com.homework.public-anchor-recovery'],capture_output=True).returncode!=0:subprocess.run(['launchctl','bootstrap',d,str(p)],check=True)",manifest,60)
        else:
            roll.spare.transport.node(member).wsl(('sudo -n ' if member=='c' else '')+'systemctl '+('--user ' if member=='b' else '')+'start homework-public-anchor-recovery.service\n',90,allow_probe=False)
    item=manifest['nodes']['c']
    roll.execute('c','from pathlib import Path\nPath('+repr(item['home']+'/ha/runtime/STOP')+').unlink(missing_ok=True)',manifest,40)
    roll.spare.transport.node('c').wsl('sudo -n systemctl restart homework-public-source-ha.service\n',90,allow_probe=False)
    roll.module('continuous_stop','public-recovery-isolation.py').stop(box)
    (box/'runtime/STOP').unlink(missing_ok=True)
    subprocess.run([str(ROOT/'ComputeNode/mac/start.sh'),str(ROOT/'ComputeNode/state/public-recovery-coordinator-20261103'),
        sys.executable,'-u',str(NETWORK/'live_timing.py'),'coordinator',str(box/'ha/mac/controller.json')],check=True,capture_output=True)


def run(box):
    home, manifest = setup(box)
    plan={'batches':[[{'actor':actor,'op':'read','query':query} for actor,query in phase] for phase in PLANS]}
    path=home/'request-plan.json'
    if path.exists():assert load(path)==plan
    else:save(path,plan)
    manifest['continuous_epochs']['request_plan_sha256']=sha(path)
    save(box/'ha/deployment.json',manifest)
    plans=PLANS
    for number,plan in enumerate(plans):
        directory = home/('epoch-'+str(number))
        if (directory/'resumed.json').exists():continue
        if number == 1:
            owner,state = epoch.wait_leader(box,manifest)
            if owner != 'mac':
                frozen = roll.freeze_writer(box,manifest,owner)
                save(home/'between-epochs-handover.json',frozen)
                try:epoch.wait_leader(box,manifest,'mac')
                finally:roll.spare.writer_signal(box,manifest,owner,'SIGCONT',frozen)
        batch(box,manifest,directory,plan,fault=number==1)
        close_and_audit(box,manifest,directory)
    print('CONTINUOUS ORIGINAL SOURCE COMPLETE: two new public epochs and independent closed audits; original service resumed',flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);args=p.parse_args()
    box=args.box.resolve();lock=(box/'ha/live-timing/operation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    run(box)
