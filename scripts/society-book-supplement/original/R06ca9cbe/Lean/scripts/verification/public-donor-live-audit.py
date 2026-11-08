"""Independently consume original donor commits, HA proofs and paid privacy proof."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
import donor_arrival_admission as auth
import donor_arrival_live as donor
from crypto import canonical,digest,verify
from anchor import public_key
from ha_quorum import Quorum,verify_quorum
from quorum import verify_certificate
from recovery_loop import save


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def verify_actual(box,work,paid,partial=False,collect=False):
    deploy=module('donor_audit_deploy','public-donor-live-deploy.py');proof=module('donor_audit_privacy','public-arrival-donor-privacy-check.py')
    privacy=proof.verify(box,True)
    manifest=deploy.load(box/'ha/deployment.json');config=manifest['mac']['service'];directory=work/'actual'
    original=deploy.load(work/'original.json')['rows'];source=deploy.load(paid/'evidence-a.json')['output']
    point=config['donor_admission']['point'];plan=deploy.load(paid/'request.json')
    before=[json.loads(r[3])['body']['native'] for r in original[69:]]
    source_facts=auth.inspect_trace(ROOT,source,plan,before)
    rows=deploy.actual.continuous.rows(manifest)
    auth.require(rows[:77]==original and (78<=len(rows)<=90 if partial else len(rows)==90),'DONOR_AUDIT_ACTUAL_PREFIX')
    auth.owner.history(deploy.load(box/'local-anchor/config.json'),rows)
    expected=[config['donor_admission']]+source['left']['output']
    q=Quorum(config);proofs=[]
    for index,value in enumerate(rows[77:]):
        message=json.loads(value[3]);event=verify(public_key(config['registry']['server']),'ledger',message)
        auth.require(event['type']==(donor.CONTROL if index==0 else donor.ACTION) and
            event['native']==expected[index],'DONOR_AUDIT_SOURCE_OUTPUT')
        donor.expected(config,rows[:77+index],event,native=False)
        result=deploy.load(directory/(('donor-control' if index==0 else 'donor-'+str(index-1))+'-result.json'))
        receipt=result['anchor'];verify_certificate(manifest['trust'],receipt,source=point['source'],stream='recovery',
            seq=value[0],previous=value[1],head=value[2],message=message)
        facts=q.collect('proof',seq=value[0]) if collect else deploy.load(directory/('ha-proof-'+str(value[0])+'.json'))
        accepted=[]
        for member,item in facts.items():
            if not item.get('proof'):continue
            fact=verify(public_key(manifest['trust']['members'][member]),'ha-event',item['proof'])
            token=fact['grant']['point'];p=dict(token=token,seq=value[0],previous=value[1],head=value[2],message=digest(message),operation_id=event['request']['body']['request_id'])
            auth.require(fact['operation']=='append' and fact['point']==p and fact['source']==point['source'] and
                fact['stream']=='recovery' and fact['cluster']==point['cluster'],'DONOR_AUDIT_FENCED_APPEND')
            verify_quorum({'ha':{'trust':manifest['trust']}},fact['grant'],'ha-grant',token)
            verify_quorum({'ha':{'trust':manifest['trust']}},fact['intent'],'ha-intent',p)
            auth.require(len({v['member'] for v in fact['intent']['votes']})>=3,'DONOR_AUDIT_NATIVE_QUORUM')
            auth.anchor.verify_commit(manifest['trust']['members'][member],fact['receipt'],source=point['source'],stream='recovery',seq=value[0],
                previous=value[1],head=value[2],message=message,cluster=point['cluster'])
            accepted.append(member)
        auth.require(len(accepted)>=3,'DONOR_AUDIT_THREE_COMMIT_PROOFS')
        if collect:save(directory/('ha-proof-'+str(value[0])+'.json'),facts)
        proofs.append(accepted)
        label='donor-control' if index==0 else 'donor-'+str(index-1)
        request=deploy.load(directory/(label+'-request.json'))
        for repeat in range(2):
            observation=deploy.load(directory/(label+'-lookup-'+str(repeat)+'-observation.json'))
            body=verify(public_key(config['registry']['auditor2']),'online-client-observation',observation)
            response=verify(public_key(config['registry']['server']),'lookup-response',body['response'])
            auth.require(response['request']==digest(body['request']) and
                body['request']['body']['lookup_id']==request['body']['request_id'] and
                response['result']['ledger']==message,'DONOR_AUDIT_ORIGINAL_ID_LOOKUP')
    if collect:
        def node(member):
            cfgpath=str(box/'local-anchor/config.json') if member=='a' else manifest['nodes'][member]['home']+'/config.json'
            code=str(ROOT/'Verification/public-audit/network') if member=='a' else manifest['nodes'][member]['code']
            script=f'''import json,sys
from pathlib import Path
sys.path.insert(0,{code!r});import source_readiness
c=json.loads(Path({cfgpath!r}).read_text());member,signed,prefix=source_readiness.snapshot(c)
print(json.dumps(dict(member=member,rows=signed,prefix=prefix)))
'''
            return member,json.loads(deploy.execute(member,script,manifest,120))
        with ThreadPoolExecutor(max_workers=4) as pool:replicas=dict(pool.map(node,'abcd'))
        save(directory/'replicas.json',replicas)
    replicas=deploy.load(directory/'replicas.json')
    auth.require(set(replicas)==set('abcd'),'DONOR_AUDIT_ALL_ORIGINAL_REPLICAS')
    checker=module('donor_audit_journals','public-donor-arrival-admission-check.py')
    for member,item in replicas.items():
        checker.local_journal(point,member,item['rows'],rows)
    report=dict(verdict='accepted',events=len(rows),original_events=77,source_events=len(rows)-77,main_privacy_verified=privacy['main_verified'],
        native_computations=0,private_replays=0,lookup_repeats=2*(len(rows)-77),fenced_commit_members=proofs,
        actual_source_facts=source_facts if len(rows)==90 else None,completed_word=len(rows)==90,
        combined_timing_acceptance=False)
    save(directory/'independent.json',report);print(json.dumps(report));return report


def runtime(box,work,manifest,rows):
    deploy=module('donor_runtime_transport','public-donor-live-deploy.py');cfg=manifest['mac']['service']
    states={member:node.call('semantic-status') for member,node in Quorum(cfg).nodes.items()};prefix=dict(seq=len(rows),head=rows[-1][2])
    auth.require(set(states)==set('abcd') and all(v['prefix']==prefix and v['backend'] and not v['warm_error'] for v in states.values()),'DONOR_RUNTIME_FOUR_NATIVE_VOTERS')
    candidates={}
    for owner,member in [('mac','a'),('spark','c')]:
        entry=deploy.load(work/('staged-'+member+'.json'));service=manifest[owner]['service']
        entry={**entry,'code':manifest['application_receipts']['candidates'][owner]['code']}
        state=str(box/'runtime') if member=='a' else manifest['nodes'][member]['home']+'/ha/runtime'
        script=f'''import hashlib,json,os,shlex,subprocess,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
from crypto import digest
from recovery_loop import birth,boot_identity
from ha_timing import public_configuration
p=Path({state!r});c=json.loads(Path({manifest[owner]['controller']['service']!r}).read_text())
assert digest(c)=={digest(service)!r};public_configuration(c)
w=c['online_privacy']['worker'];d=c['donor']
assert w['contract']=='original77-donor-public/v1' and w['lean_path']==d['lean_path'] and w['cwd']==d['cwd']
assert (Path(w['cwd'])/w['command'][-2])==Path(d['exporter'])
assert hashlib.sha256(Path(d['exporter']).read_bytes()).hexdigest()==d['descriptor']['exporter_sha256']
assert {{n:hashlib.sha256((Path({entry['code']!r})/n).read_bytes()).hexdigest() for n in {list(manifest['protocol'])!r}}}=={manifest['protocol']!r}
s=json.loads((p/'ha-status.json').read_text());b=s['body'];assert birth(b['pid'])==b['birth'] and b['boot']==boot_identity()
def argv(pid):
 return shlex.split(subprocess.check_output(['ps','-ww','-p',str(pid),'-o','command='],text=True))
coordinator=argv(b['pid']);controller=str(Path({manifest[owner]['controller']['service']!r}).with_name('controller.json'))
assert coordinator[-3:]==[{entry['code']+'/live_timing.py'!r},'coordinator',controller]
r=dict(status=s,configuration=digest(c),coordinator_argv=coordinator)
if b['phase']=='leader':
 ready=json.loads(Path({str(Path(service['database']).parent/'ha-service-ready.json')!r}).read_text());rb=ready['body'];worker=rb['public_timing']['worker']
 assert rb['grant']['point']==b['grant']['point'] and birth(rb['pid'])==rb['birth']
 writer=argv(rb['pid']);assert writer[-3:]==[{entry['code']+'/live_timing.py'!r},'writer',str(p/'ha-service.json')]
 assert writer==b['service']['argv'] and os.getpgid(rb['pid'])==b['service']['pgid']
 assert birth(worker['pid'])==worker['birth'] and os.getpgid(worker['pid'])==b['service']['pgid']
 command=argv(worker['pid'])
 assert command==worker['argv']==w['command'] and command[-1]=='public';r.update(ready=ready,writer_argv=writer)
print(json.dumps(r))
'''
        value=json.loads(deploy.execute(member,script,manifest,90))
        status=verify(public_key(manifest['owners'][owner]),'ha-coordinator',value['status'])
        auth.require(status['configuration']==digest(manifest[owner]['controller']) and time.time()-status['at']<25,'DONOR_RUNTIME_CURRENT_CANDIDATE')
        if 'ready' in value:verify(public_key(service['registry']['server']),'ha-service-ready',value['ready'])
        candidates[owner]=value
    auth.require(sum(v['status']['body']['phase']=='leader' for v in candidates.values())==1,'DONOR_RUNTIME_ONE_WRITER')
    report=dict(voters=states,candidates=candidates);save(work/'runtime-independent.json',report);return report


def final(box,work,paid,full=False,check_main=False):
    actual=verify_actual(box,work,paid,collect=False);deploy=module('donor_final_transport','public-donor-live-deploy.py')
    manifest=deploy.load(box/'ha/deployment.json');rows=deploy.load(work/'actual/events.json');oldhome=deploy.arrival.location(box)
    historical=deploy.load(oldhome/'final-check.json');integration=deploy.load(oldhome/'integration.json')
    auth.require(historical['exit']==0 and historical['main_verified'] and historical['events']==77 and
        historical['head']==rows[76][2] and integration['exit']==0,'DONOR_HISTORICAL_ACCEPTED_PREFIX')
    privacy_integration=deploy.load(oldhome/'privacy-universal/main-integration.json')
    historical_commit=privacy_integration['commit']
    subprocess.run(['git','merge-base','--is-ancestor',integration['commit'],historical_commit],cwd=ROOT,check=True)
    subprocess.run(['git','merge-base','--is-ancestor',historical_commit,'refs/heads/main'],cwd=ROOT,check=True)
    for name,wanted in historical['inputs'].items():
        raw=subprocess.check_output(['git','show',historical_commit+':'+name],cwd=ROOT)
        auth.require(__import__('hashlib').sha256(raw).hexdigest()==wanted,'DONOR_HISTORICAL_SOURCE:'+name)
    material=module('donor_lossless_wire_consumer','public-donor-wire-check.py')
    wire=material.wire(box,manifest,work,rows,rows[:77],expected_events=13)
    directory=work/'actual';owner=deploy.load(directory/'owner-accepted.json')
    auth.require(owner['exit']==0 and owner['events']==90 and owner['head']==rows[-1][2] and
        owner['binding']['events']==auth.sha(directory/'events.json') and owner['binding']['closed']==auth.sha(directory/'closed.json') and
        owner['binding']['input']==digest(deploy.load(paid/'request.json')) and owner['binding']['source_sha256']==auth.sha(Path(__file__).with_name('public-donor-live-owner-source.lean')),
        'DONOR_FINAL_CLOSED_OWNER_BINDING')
    coverage=module('donor_original_inventory_consumer','public-arrival-live-check.py');coverage.closed_inventory_evidence(work,manifest)
    module('donor_registered_root_consumer','public-donor-live-inventory.py').verify_closed(box,work,manifest,deploy.NETWORK)
    private={}
    auth.require(set(owner['branches'])=={'private-one','private-two'},'DONOR_FINAL_BOTH_BRANCHES')
    for branch,frame in [('private-one','33'),('private-two','32')]:
        path=directory/(branch+'.json');receipt=deploy.load(directory/(branch+'-exit.json'));value=deploy.load(path)
        started=deploy.load(directory/(branch+'-started.json'))
        auth.require(auth.sha(path)==owner['branches'][branch]==receipt['output'] and receipt['exit']==0 and
            receipt['binding']==started['binding']==owner['binding'] and started['at']<=receipt['at'], 'DONOR_FINAL_PRIVATE_BRANCH')
        auth.require(value['old']==[json.loads(r[3])['body']['native'] for r in rows[69:77]] and
            value['output']==[json.loads(r[3])['body']['native'] for r in rows[78:]],'DONOR_FINAL_PRIVATE_REPLIES')
        auth.require(value['ownFrame']==frame and value['nativeSlots']==24 and value['nativeOutstanding']=='0' and
            value['spent'] and value['attempts']==4 and value['source']['available']=='0','DONOR_FINAL_PRIVATE_ACCOUNT')
        auth.require(len(value['origins'])==24 and value['origins'][:21]==deploy.load(oldhome/'actual'/(branch+'.json'))['origins'],'DONOR_FINAL_ORIGINAL_ORIGINS')
        private[branch]=value
    auth.require(private['private-one']['origins']==private['private-two']['origins'],'DONOR_FINAL_COMMON_ORIGINS')
    auth.require(deploy.load(directory/'resumed.json')['head']==rows[-1][2],'DONOR_FINAL_RESTORED_HEAD')
    runtime(box,work,manifest,rows)
    resumed=module('donor_restored_wire_consumer','public-donor-live-resume.py').check(box,work)
    if full:
        result=subprocess.run([sys.executable,str(ROOT/'.agents/tmp/public-autonomous-origin-20261101/final-audit/verify.py')],cwd=ROOT,capture_output=True,text=True)
        (work/'full-cost.log').write_text(result.stdout+result.stderr)
        auth.require(result.returncode==0,'DONOR_FULL_COST_AUDIT');print(result.stdout,end='',flush=True)
    names=[str(Path(__file__).relative_to(ROOT)),*[str(Path(__file__).with_name('public-donor-live-'+n).relative_to(ROOT)) for n in ('actual.py','deploy.py','close.py','retire.py','resume.py','owner-source.lean','check.py')]]
    names+=['Verification/public-audit/network/'+n for n in manifest['protocol']]
    names+=['Lean/scripts/verification/public-ha-check.py','Lean/scripts/verification/public-donor-live-inventory.py']
    names+=['Lean/scripts/verification/public-donor-wire-check.py']
    inputs={n:auth.sha(ROOT/n) for n in names}
    if check_main:
        for name,wanted in inputs.items():
            raw=subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)
            auth.require(__import__('hashlib').sha256(raw).hexdigest()==wanted,'DONOR_MAIN_SOURCE:'+name)
    report=dict(exit=0,events=90,head=rows[-1][2],original_events=77,actual=actual,wire=wire,closed_owner=owner,
        resumed=resumed,inputs=inputs,full=full,main_verified=check_main,combined_timing_acceptance=True)
    save(work/'final-check.json',report)
    print('INDEPENDENT DONOR LIVE PASS: original77+control+12; closed dual execution; four original voters; restored TLS; pending0',flush=True)
    return report


if __name__=='__main__':
    sys.dont_write_bytecode=True
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);p.add_argument('--partial',action='store_true');p.add_argument('--collect',action='store_true')
    p.add_argument('--final',action='store_true');p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true')
    p.add_argument('--box',type=Path,default=ROOT/'.agents/tmp/public-recovery-20261103/live');p.add_argument('--admission-work',type=Path,default=Path('runtime/retained/iqa-actual77-donor-admission-20261106'))
    a=p.parse_args()
    if a.final:final(a.box.resolve(),a.work.resolve(),a.admission_work.resolve(),a.full,a.check_main)
    else:verify_actual(a.box.resolve(),a.work.resolve(),a.admission_work.resolve(),a.partial,a.collect)
