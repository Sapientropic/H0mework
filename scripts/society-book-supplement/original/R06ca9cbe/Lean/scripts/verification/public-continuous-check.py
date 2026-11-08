"""Consume a growing original ledger and its closed public-epoch evidence."""
import argparse
import ast
import base64
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from crypto import canonical, digest, verify
from online_privacy import source_input
from online_privacy_check import frames as application_frames, tls_streams
from quorum import verify_certificate
from recovery_loop import save
from service import Store
from source_semantics import Engine
import continuation
import handoff
from ha_timing_check import MODULE, MOUTHS


def module(name,filename):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


roll=module('continuous_check_roll','public-live-timing.py')
live=module('continuous_live_consumer','public-live-timing-check.py')
base=module('continuous_ha_consumer','public-ha-check.py')
native=module('continuous_native_consumer','public-native-spare-check.py')
load,sha=roll.load,roll.sha


def release_readers(*engines):
    """End only this consumer's children through their existing stdin protocol."""
    import governance,energy
    owned=[*engines,*governance._readers.values(),*energy._readers.values()]
    for engine in {id(e):e for e in owned}.values():
        process=engine.process
        if process:
            if not process.stdin.closed:process.stdin.close()
            try:process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.terminate()
                try:process.wait(timeout=2)
                except subprocess.TimeoutExpired:process.kill();process.wait(timeout=5)
            process.stdout.close();engine.process=None
        if engine.error:engine.error.close();engine.error=None
        engine.count=0;engine.head='0'*64;engine.buffer=b''
    governance._readers.clear();energy._readers.clear()


def source_inputs(home):
    paths=set(load(home/'baseline/full.json')['inputs']) | {
        'Lean/scripts/verification/public-continuous-actual.py','Lean/scripts/verification/public-continuous-check.py',
        'Lean/scripts/verification/public-live-timing.py','Lean/scripts/verification/public-live-timing-actual.py',
        'Lean/scripts/verification/public-live-timing-check.py','Verification/public-audit/network/continuous_capture.py'}
    pending=list(paths);seen=set()
    while pending:
        path=pending.pop()
        if path in seen or not path.endswith('.py'):continue
        seen.add(path);tree=ast.parse((ROOT/path).read_text())
        candidates=[]
        for node in ast.walk(tree):
            names=([item.name for item in node.names] if isinstance(node,ast.Import) else
                   [node.module] if isinstance(node,ast.ImportFrom) and node.module else [])
            candidates.extend(NETWORK/(name.split('.')[0]+'.py') for name in names)
            if isinstance(node,ast.Constant) and isinstance(node.value,str) and node.value.endswith('.py') and '/' not in node.value:
                candidates.append(Path(__file__).with_name(node.value))
        for target in candidates:
            if target.is_file():
                relative=str(target.relative_to(ROOT))
                if relative not in paths:paths.add(relative);pending.append(relative)
    return {p:sha(ROOT/p) for p in sorted(paths)}


def baseline(box,manifest):
    home=box/'ha/continuous';point=manifest['continuous_epochs']
    before=load(home/'baseline/events.json');full=load(home/'baseline/full.json')
    assert len(before)==27 and point['baseline']=={'seq':27,'head':before[-1][2]}
    assert full['exit']==0 and full['full'] and full['main_verified'] and full['events']==27
    assert sha(home/'baseline/full.json')==point['baseline_receipt']
    subprocess.run(['git','merge-base','--is-ancestor',point['baseline_commit'],'refs/heads/main'],cwd=ROOT,check=True)
    for path,wanted in full['inputs'].items():
        raw=subprocess.check_output(['git','show',point['baseline_commit']+':'+path],cwd=ROOT)
        assert hashlib.sha256(raw).hexdigest()==wanted,('ORIGINAL_ACCEPTED_SOURCE',path)
    for name,wanted in manifest['protocol'].items():assert sha(NETWORK/name)==wanted
    return before


def wires(directory,config):
    result=[];boundaries=[]
    for owner in ('mac','spark'):
        for line in (directory/(owner+'-boundary.jsonl')).read_text().splitlines():
            signed=json.loads(line);value=verify(public_key(config['registry']['server']),signed['kind'],signed)
            if signed['kind']=='online-privacy-boundary':
                assert value['started_ns']<=value['finished_ns'];boundaries.append(value)
            else:
                assert signed['kind']=='online-wire-observation'
                assert value['started_ns']<=value['finished_ns']
                data={'sent':b'','received':b''}
                for operation in value['operations']:
                    assert value['started_ns']<=operation['at_ns']<=value['finished_ns']
                    if 'finished_ns' in operation:assert operation['at_ns']<=operation['finished_ns']<=value['finished_ns']
                    data[operation['direction']]+=base64.b64decode(operation['bytes'],validate=True)
                result.append((owner,value,application_frames(data['sent']),application_frames(data['received'])))
    return boundaries,result


def public_epoch(manifest,directory):
    config=manifest['mac']['service'];server=public_key(config['registry']['server'])
    before=load(directory/'before.json');rows=load(directory/'events.json')
    assert rows[:len(before)]==before and len(rows)>len(before)
    boundaries,observed=wires(directory,config)
    outcomes=[];unknown=[];matches=set();lookups=0;requests=[]
    lookup_counts={row[0]:0 for row in rows[len(before):]}
    for index,row in enumerate(rows[len(before):]):
        event=verify(server,'ledger',json.loads(row[3]));request=event['request'];body=request['body']
        actor=body['actor'];key=public_key(config['registry']['auditor'+actor])
        verify(key,'energy-handoff',request)
        assert request==load(directory/('step-'+str(index)+'-request.json'))
        assert event['source']==config['source'] and event['stream']==config['stream']
        raw=source_input(config,rows[:row[0]-1],event)
        assert continuation.check_flows(event['native'],handoff.context(config,rows[:row[0]-1])[2])==[]
        assert any(b['phase']=='before-intent' and b['seq']==row[0] and b['event']==digest(event)
                   and b['input']==raw and b['native']==digest(event['native']) for b in boundaries)
        assert event['native']['packets']==[] and all(not r['accepted'] for r in event['native']['rows'])
        requests.append(raw);outcomes.append(event['native']['reason'])
    observations=sorted(directory.glob('*-observation.json'))
    assert len(observations)==3*len(outcomes), 'EVERY_NEW_REQUEST_NEEDS_TWO_ORIGINAL_ID_LOOKUPS'
    for path in observations:
        value=load(path);actor=value['body']['request']['body']['actor'];key=public_key(config['registry']['auditor'+actor])
        observed_client=verify(key,'online-client-observation',value)
        request=observed_client['request'];body=verify(key,request['kind'],request)
        challenge=verify(server,'challenge',observed_client['challenge'])
        for field in ('source','stream','actor','nonce','seq','cut','epoch','expires'):assert body[field]==challenge[field]
        times=[observed_client['times'][n] for n in ('connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns')]
        assert times==sorted(times) and all(type(t) is int for t in times)
        response=observed_client['response']
        if 'transport_error' in response:
            assert request['kind']=='energy-handoff' and response['transport_error'] in {'TimeoutError','EOFError','ConnectionResetError','SSLEOFError'}
            partial=[(owner,value,sent,received) for owner,value,sent,received in observed
                     if sent and sent[0]==observed_client['challenge'] and received==[request]]
            assert len(partial)<=1
            if partial:
                assert partial[0][1]['tls']=='TLSv1.3' and len(partial[0][2]) in (1,2)
                if len(partial[0][2])==2:
                    late=partial[0][2][1];reply=verify(server,late['kind'],late)
                    if late['kind']=='response':assert reply['event']['request']==request
                    else:assert late['kind']=='error'
            committed=[row for row in rows[len(before):] if json.loads(row[3])['body']['request']==request]
            assert len(committed)==1,'UNKNOWN_OUTCOME_REQUIRES_THE_ORIGINAL_COMMITTED_REQUEST'
            fault_path=directory/'boundary.json'
            if fault_path.exists() and load(fault_path)['body']['message']['body']['request']==request:
                fault=verify(server,'ha-fault-boundary',load(fault_path));pending=load(directory/'pending.json')
                assert fault['phase']=='after-source' and fault['message']==pending['message']
                assert pending['seq']==fault['seq'] and pending['previous']==fault['previous']
                assert json.loads(rows[pending['seq']-1][3])==pending['message']
                isolated=load(directory/'isolated.json')
                assert isolated['source']==config['source'] and any(p['pid']==fault['pid'] and p['birth'] for p in isolated['observed_processes'])
            else:assert partial,'AN_UNOBSERVED_LOSS_NEEDS_TYPED_INSUFFICIENT_EVIDENCE'
            unknown.append({'request':digest(request),'raw_response':response,'tls':observed_client['tls'],
                            'server_observation':partial[0][1] if partial else None,
                            'observation_status':'interrupted at the signed source boundary'})
            continue
        envelope=verify(server,response['kind'],response)
        assert observed_client['tls']=='TLSv1.3'
        if request['kind']=='lookup':
            assert response['kind']=='lookup-response' and envelope['request']==digest(request)
            result=envelope['result'];lookups+=1
        else:
            assert request['kind']=='energy-handoff' and response['kind']=='response';result=envelope
        row=rows[result['anchor']['body']['seq']-1]
        assert result['ledger']==json.loads(row[3]) and result['event']==json.loads(row[3])['body'] and result['head']==row[2]
        assert row[0]>len(before)
        verify_certificate(manifest['trust'],result['anchor'],source=config['source'],stream=config['stream'],
                           seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
        assert result['request']==digest(result['event']['request'])
        if request['kind']=='lookup':
            assert body['lookup_id']==result['event']['request']['body']['request_id']
            assert result['event']['request']['body']['actor']==actor
            lookup_counts[row[0]]+=1
        else:
            assert result['event']['request']==request and result['request']==digest(request)
        matching=[(owner,value) for owner,value,sent,received in observed
                  if sent==[observed_client['challenge'],response] and received==[request]]
        assert len(matching)==1,'COMPLETE_SIGNED_APPLICATION_OBSERVATION_REQUIRED'
        matches.add(digest(request))
    assert lookups==2*len(outcomes) and all(count==2 for count in lookup_counts.values())
    if (directory/'takeover.json').exists():
        start=load(directory/'start.json');takeover=load(directory/'takeover.json')
        old=verify(public_key(manifest['owners'][start['owner']]),'ha-coordinator',start['state'])
        after=verify(public_key(manifest['owners']['spark']),'ha-coordinator',takeover)
        assert old['owner']=='mac' and after['owner']=='spark' and after['phase']=='leader'
        assert after['grant']['point']['epoch']>old['grant']['point']['epoch']
        prior=verify(public_key(manifest['owners']['spark']),'ha-coordinator',load(directory/'before-fault.json')['spark'])
        assert all(prior[k]==after[k] for k in ('pid','birth','boot'))
    streams=tls_streams(directory)
    return {'before':len(before),'after':len(rows),'outcomes':outcomes,'new_requests':len(outcomes),
            'duplicate_lookups':lookups,'complete_observations':len(matches),'unknown':unknown,
            'tls_streams':len(streams),'inputs':requests}


def reconstruct(box,directory):
    manifest=live.public_closed(box,directory)
    rows=load(directory/'events.json');before=load(directory/'before.json')
    assert rows[:len(before)]==before and rows==[list(r) for r in roll.spare.rows(manifest['mac']['service']['database'])]
    public=public_epoch(manifest,directory)
    source=ROOT/'Lean/scripts/verification/ha-timing-owner-source.lean'
    library=box.parent/'privacy/timing-01/lib';env=os.environ.copy();env['LEAN_PATH']=str(library)
    results={};started=time.monotonic_ns()
    for lane,variant in (('one','private-one'),('two','private-two')):
        command=[manifest['mac']['service']['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',str(source),variant]
        result=subprocess.run(command,cwd=ROOT/'Lean',env=env,text=True,capture_output=True,
            input=''.join(canonical(value).decode()+'\n' for value in public['inputs']),timeout=120)
        assert result.returncode==0 and not result.stderr,result.stderr
        answers=[json.loads(line) for line in result.stdout.splitlines()]
        assert len(answers)==len(rows)-len(before)
        for index,answer in enumerate(answers):
            event=json.loads(rows[len(before)+index][3])['body']
            assert answer['native']==event['native']
            assert answer['actualPublic']==answer['rebuiltPublic']==event['native']['next']
            assert answer['consumedRequests']==len(public['inputs'][index]['handoffs'])
            assert all(p['sourceInitial']==p['actualNext']==p['rebuiltNext'] for p in answer['frame'])
            assert answer['frame'][3]['actualNext']==('39' if lane=='one' else '38')
        results[lane]={'argv':command,'answers':answers}
    accepted={'closed':sha(directory/'closed.json'),'events':sha(directory/'events.json'),'public':public,
        'owner_source':sha(source),'proof_artifacts':{name:sha(library/(MODULE+name+'.olean')) for name in ('Timing','Timing/Source')},
        'started_ns':started,'finished_ns':time.monotonic_ns(),'lanes':results}
    save(directory/'accepted.json',accepted)
    print('INDEPENDENT CONTINUOUS EPOCH PASS:',len(before),'->',len(rows),'; new source requests; full observations; two actual own-next histories; public roles closed',flush=True)


def audit(box,full=False,check_main=False):
    lock=(box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    manifest=load(box/'ha/deployment.json');config=manifest['mac']['service'];home=box/'ha/continuous'
    prefix=baseline(box,manifest);literal=base.database(Path(config['database']))
    rows=[list(r) for r in literal['rows']]
    assert rows[:len(prefix)]==prefix and len(rows)>len(prefix),'NEW_ORIGINAL_EVENTS_REQUIRED'
    validator=object.__new__(Store);validator.config=config;validator.anchor=object()
    class Signer:
        def public_key(self):return public_key(config['registry']['server'])
    validator.key=Signer()
    import sqlite3
    validator.database=sqlite3.connect(Path(config['database']).as_uri()+'?mode=ro',uri=True)
    try:validator.validate_ledger();validator.validate_anchor_receipts()
    finally:validator.database.close()
    remote=base.collect(box,manifest)
    node=base.transport.node('b')
    script="$v=(Get-CimInstance Win32_OperatingSystem).LastBootUpTime\n[DateTimeOffset]::new($v).ToUnixTimeSeconds()\n"
    observed=node._run_remote([*node.ssh,'powershell','-NoProfile','-Command','-'],input=script.encode(),
                             capture_output=True,timeout=30,allow_probe=False)
    assert observed.returncode==0,'WINDOWS_HOST_BOOT_READ_UNAVAILABLE'
    remote['b']['windows_boot_unix']=int(observed.stdout.decode().strip())
    base.check_current(box,manifest,config,literal,remote)
    admitted=native.admitted_runtime(box,manifest)
    live.current_runtime(box,manifest)
    engine=Engine({**manifest['semantic']['configurations']['a'],'replay_seconds':180,
                   'error_log':str(home/'independent-source.log')})
    try:engine.sync(literal['rows'])
    finally:release_readers(engine)
    cursor=prefix;epochs=[]
    plan=load(home/'request-plan.json')
    assert sha(home/'request-plan.json')==manifest['continuous_epochs']['request_plan_sha256']
    assert len(plan['batches'])>=2
    for directory in sorted(home.glob('epoch-*')):
        if not directory.is_dir():continue
        before=load(directory/'before.json');after=load(directory/'events.json')
        assert before==cursor and rows[:len(after)]==after,'EPOCH_GAP_OR_REORDER'
        public=public_epoch(manifest,directory);accepted=load(directory/'accepted.json')
        expected_plan=plan['batches'][len(epochs)]
        assert len(after)-len(before)==len(expected_plan)
        for expected,row in zip(expected_plan,after[len(before):]):
            body=json.loads(row[3])['body']['request']['body']
            assert {k:body[k] for k in ('actor','op','query')}==expected
        assert accepted['closed']==sha(directory/'closed.json') and accepted['events']==sha(directory/'events.json')
        assert accepted['public']==public and accepted['owner_source']==sha(ROOT/'Lean/scripts/verification/ha-timing-owner-source.lean')
        for lane in ('one','two'):
            for index,answer in enumerate(accepted['lanes'][lane]['answers']):
                event=json.loads(after[len(before)+index][3])['body']
                assert answer['native']==event['native'] and answer['actualPublic']==answer['rebuiltPublic']==event['native']['next']
                assert answer['consumedRequests']==len(public['inputs'][index]['handoffs'])
                assert all(p['sourceInitial']==p['actualNext']==p['rebuiltNext'] for p in answer['frame'])
                assert answer['frame'][3]['actualNext']==('39' if lane=='one' else '38')
        inventories=load(directory/'inventories.json');closed=load(directory/'closed.json');assert set(closed)==set('abcd')
        for member in 'abcd':
            report=verify(public_key(manifest['trust']['members'][member]),'public-epoch-closed',closed[member])
            seen=set()
            for item in inventories:
                old=verify(public_key(manifest['trust']['members'][member]),'public-epoch-inventory',item[member])
                seen|={(p['pid'],p['birth']) for p in old['processes']}
            assert seen=={(p['pid'],p['birth']) for p in report['processes']} and not report['remaining']
        assert (directory/'resumed.json').is_file()
        epochs.append(public);cursor=after
    assert cursor==rows and len(epochs)==len(plan['batches']),'UNCONSUMED_CURRENT_SUFFIX'
    proof=load(box/'ha/live-timing/privacy-independent/timing/accepted.json')
    assert proof['standard_axiom_mouths']==len(MOUTHS)
    for name,wanted in proof['proof_sources'].items():
        assert sha(ROOT/'Lean'/(MODULE+name+'.lean'))==wanted
        artifact=sha(box/'ha/live-timing/privacy-independent/timing/lib'/(MODULE+name+'.olean'))
        for directory in home.glob('epoch-*'):
            if directory.is_dir():assert load(directory/'accepted.json')['proof_artifacts'][name]==artifact
    kernel=load(home/'kernel.json')
    assert kernel['exit']==0 and kernel['mouths']==len(MOUTHS)
    assert kernel['proof_sources']==proof['proof_sources'] and kernel['log_sha256']==sha(home/'kernel.log')
    for directory in home.glob('epoch-*'):
        if directory.is_dir():assert kernel['artifacts']==load(directory/'accepted.json')['proof_artifacts']
    if full:
        native.original_cases(box)
        module('continuous_original_physical','public-governance-check.py').physical_baseline()
        result=subprocess.run([sys.executable,str(Path(__file__).with_name('public-source-final-audit.py')),'--check-main'],cwd=ROOT,text=True,capture_output=True)
        (home/'original-six.log').write_text(result.stdout+result.stderr)
        assert result.returncode==0,result.stdout[-1600:]+result.stderr[-1600:]
    inputs=source_inputs(home)
    if check_main:
        for p,wanted in inputs.items():assert hashlib.sha256(subprocess.check_output(['git','show','refs/heads/main:'+p],cwd=ROOT)).hexdigest()==wanted
    assert rows==[list(r) for r in roll.spare.rows(config['database'])], 'SOURCE_CHANGED_DURING_AUDIT'
    result={'exit':0,'full':full,'main_verified':check_main,'events':len(rows),'head':rows[-1][2],
        'baseline_events':len(prefix),'epochs':epochs,'new_events':len(rows)-len(prefix),'admitted':admitted,
        'source_inputs':inputs,'own_nexts':2*(len(rows)-len(prefix)),'at':time.time()}
    save(home/'final-check.json',result)
    print('INDEPENDENT CONTINUOUS ORIGINAL AUDIT PASS:',len(prefix),'->',len(rows),'; 4 native voters; 2 closed epochs; all new requests/unknown intents/own nexts consumed; main='+str(check_main),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--epoch',type=Path)
    p.add_argument('--closed',action='store_true');p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    if a.closed:
        assert a.epoch is not None;reconstruct(a.box.resolve(),a.epoch.resolve())
    else:audit(a.box.resolve(),a.full,a.check_main)
