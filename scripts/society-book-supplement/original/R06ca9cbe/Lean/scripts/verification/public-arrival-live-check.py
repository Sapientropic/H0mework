"""Independently consume the admitted arrival, its original journal and paid delivery."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from copy import deepcopy
from fractions import Fraction as Q
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import ledger_hash,public_key
from crypto import canonical,digest,verify
from recovery_loop import save
from quorum import verify_certificate
from cryptography.exceptions import InvalidSignature
from service import Store
import arrival_extension,arrival_regeneration,arrival_readiness


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


deploy=module('arrival_live_deploy','public-arrival-deploy.py')
prior=module('arrival_material_check','public-material-check.py')
native=module('arrival_productive_arithmetic','public-productive-check.py')
load,sha=deploy.load,deploy.sha


def trace(argument,output,baseline):
    arrival_readiness.validate_probe_result(argument,output)
    current=native.state(baseline);initial=deepcopy(current);dual=0
    births=settlements=fuel=0
    for i,row in enumerate(output):
        assert native.state(row['before'])==current
        if row['status']=='ARRIVED':
            assert current['stock']['audit:0','feed']==0
            current['stock']['audit:0','feed']+=3
            current['clock']+=6;current['round']+=6
        elif row['status'] in {'OPENED','DELIVERED'}:
            service=row['service'];current['clock']+=1;current['round']+=1
            for index,item in enumerate(service['rows']):
                assert item['index']==index and item['accepted'] is True
                action=item['request'];op=action['operation'];kind=op['kind']
                assert not action['consents']
                gate={'kind':'audit','base':'revision','query':None}
                assert action['gates']==([gate] if kind=='revise' else
                    [{'kind':'audit','base':'machine','query':None}] if kind=='use' and action['signer']=='audit:1' else [])
                debit=[];credit=[]
                if kind=='produce':
                    assert op==dict(kind='produce',actor='provider:0')
                    signer='provider:0';debit=[[signer,'feed','1'],[signer,'labor','1']]
                    credit=[[signer,'energy','2'],[signer,'labor','3']];fuel+=1
                elif kind=='transfer':
                    signer=op['from'];allowed={('audit:0','provider:0'):[['feed','1']],
                        ('audit:3','audit:0'):[['energy','4']],('audit:3','audit:1'):[['energy','2']]}
                    assert op['bundle']==allowed[signer,op['to']]
                    debit=[[signer,g,n] for g,n in op['bundle']]
                    credit=[[op['to'],g,n] for g,n in op['bundle']]
                elif kind in {'issue','settle'}:
                    signer='provider:0';key=('delivery',signer,'audit:3')
                    assert op==dict(kind=kind,instrument='delivery',debtor=signer,creditor='audit:3',quantity='2')
                    if kind=='issue':
                        assert current['claims'][key]==0;current['claims'][key]+=2;births+=1
                    else:
                        assert current['claims'][key]==2;current['claims'][key]-=2;settlements+=1
                        debit=[[signer,'energy','2']];credit=[['audit:3','energy','2']]
                elif kind=='revise':
                    signer=op['actor'];assert signer in {'audit:0','audit:1'}
                    assert op['technology']['audit']['version']==current['technology']['audit']['version']+1
                    debit=[[signer,'energy','1']];current['technology']=deepcopy(op['technology'])
                elif kind=='use':
                    signer=op['actor'];assert signer in {'audit:0','audit:1'}
                    assert op['purpose']=='external' and op['bundle']==[['energy','1']]
                    debit=[[signer,'energy','1']]
                else:raise AssertionError('ARRIVAL_UNEXPECTED_RECIPE')
                assert action['signer']==signer
                assert native.amounts(item['debit'])==native.amounts(debit)
                assert native.amounts(item['credit'])==native.amounts(credit)
                for key,n in native.amounts(debit).items():
                    assert n>=0 and current['stock'][key]>=n;current['stock'][key]-=n
                for key,n in native.amounts(credit).items():
                    assert n>=0;current['stock'][key]+=n
            current['clock']+=1;current['round']+=1
            assert native.state(service['next'])==current
            for packet in service['packets']:
                for evidence in packet:
                    assert prior.old.privacy.original._dual.payment_scan(evidence['slot'],evidence)=='verified'
                    assert prior.old.privacy.original._dual.lifecycle_replay(evidence['slot'],evidence)=='verified';dual+=2
        assert native.state(row['next'])==current
        assert current['claims']==initial['claims']
        if i and i!=2:assert row['scope']==row['nextScope']
    assert fuel==births==settlements==3 and dual==12
    assert current['stock']['audit:0','feed']==0
    assert current['stock']['provider:0','labor']==initial['stock']['provider:0','labor']+6
    return dict(source_feed=3,source_steps=6,source_remaining=20,fuel=fuel,births=births,
                settlements=settlements,new_windows=1,delivered_slots=6,dual_checks=dual,
                original_origins=18,final_origins=21,outstanding='0')


def ready_word(home,cfg):
    prepared=load(home/'prepared.json');certificate=load(home/'admission.json')['certificate']
    arrival_extension.admission(cfg,certificate)
    argument=arrival_readiness.probe(cfg,load(home/'original-before.json')['rows'])
    outputs=[]
    for member in 'abcd':
        ready=load(home/('ready-'+member+'.json'));entry=prepared['nodes'][member]
        body=verify(public_key(cfg['ha']['trust']['members'][member]),arrival_extension.READY,ready['vote']['receipt'])
        assert ready['acceptance']['exit']==0 and ready['acceptance']['probe']==body['probe']
        assert ready['revision']==prepared['revision'] and body['point']==certificate['point']
        path=home/('replayed-'+member+'.json')
        if not path.exists():
            raw=deploy.execute(member,'from pathlib import Path\nprint(Path('+repr(ready['evidence']+'/output.json')+').read_text(),end="")',load(home/'online-before.json'),90)
            path.write_text(raw)
        output=load(path);assert body['probe']==dict(input=digest(argument),output=digest(output))
        outputs.append(output)
    assert all(value==outputs[0] for value in outputs)
    return argument,outputs[0]


def closed_replay(box):
    home=deploy.location(box);directory=home/'actual'
    manifest=prior.old.old.live.public_closed(box,directory);cfg=manifest['mac']['service']
    closed_inventory_evidence(home,manifest)
    rows=load(directory/'events.json');argument,_,_=arrival_regeneration.context(cfg,rows)
    assert argument==load(directory/'source-input.json')
    expected=[json.loads(row[3])['body']['native'] for row in rows[69:]]
    script=ROOT/'Lean/scripts/verification/public-arrival-owner-source.lean'
    env=os.environ.copy();env['LEAN_PATH']=cfg['arrival']['lean_path'];answers={}
    for branch in ('private-one','private-two'):
        path=directory/(branch+'.json');receipt=directory/(branch+'-exit.json')
        binding=dict(source=sha(script),input=digest(argument),closed=sha(directory/'closed.json'))
        if receipt.exists():
            assert load(receipt)['binding']==binding and load(receipt)['exit']==0
        else:
            command=[cfg['arrival']['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',str(script),branch]
            result=subprocess.run(command,cwd=ROOT/'Lean',env=env,input=canonical(argument)+b'\n',stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=600)
            path.write_bytes(result.stdout);(directory/(branch+'.stderr')).write_bytes(result.stderr)
            assert result.returncode==0 and not result.stderr,(result.returncode,result.stderr[-1200:])
            save(receipt,dict(exit=0,binding=binding,output=sha(path)))
        answer=load(path);assert answer['output']==expected
        assert answer['nativeSlots']==21 and answer['nativeOutstanding']=='0'
        assert len(answer['initialOrigins'])==18 and len(answer['origins'])==21
        assert answer['origins'][:18]==answer['initialOrigins']
        assert answer['ownFrame']==('39' if branch=='private-one' else '38')
        assert answer['spent'] and answer['restartBefore']==answer['restartNext']
        assert answer['source']==answer['sourceNext'] and answer['source']['available']=='0'
        answers[branch]=answer
    assert answers['private-one']['output']==answers['private-two']['output']
    assert answers['private-one']['origins']==answers['private-two']['origins']
    save(directory/'owner-accepted.json',dict(exit=0,events=sha(directory/'events.json'),
        closed=sha(directory/'closed.json'),input=digest(argument),source=sha(script),
        branches={k:sha(directory/(k+'.json')) for k in answers},frames=['39','38'],
        native_slots=21,native_outstanding='0',replies=8))
    print('INDEPENDENT CLOSED ARRIVAL PASS: exact eight replies; own frames39/38; 18+3 native origins; zero outstanding; spent restart unchanged',flush=True)


def closed_inventory_evidence(home,manifest):
    raw=load(home/'actual/raw-inventories.json');normalized=load(home/'actual/inventories.json')
    closed=load(home/'actual/closed.json');assert len(raw)==len(normalized)==1 and set(closed)==set('abcd')
    actual=module('arrival_process_classifier','public-arrival-actual.py')
    for member in 'abcd':
        key=public_key(manifest['trust']['members'][member])
        original=verify(key,'public-epoch-inventory',raw[0][member])
        inventory=verify(key,'public-epoch-inventory',normalized[0][member])
        report=verify(key,'public-epoch-closed',closed[member])
        assert original['member']==inventory['member']==report['member']==member
        assert original['source']==inventory['source']==report['source']==manifest['source']
        assert inventory['original_inventory']==report['original_inventory']==digest(raw[0][member])
        assert inventory['processes']==[p for p in original['processes'] if p['birth']]
        assert report['processes']==inventory['processes'] and not report['remaining']
        excluded=inventory['non_executable'];assert report['non_executable']==excluded
        assert [v['process'] for v in excluded]==[p for p in original['processes'] if not p['birth']]
        for value in excluded:
            assert actual.non_executable(value['stat'],value['status'])==value['classification']


def journals(box,manifest,rows,home):
    prepared=load(home/'prepared.json');path=home/'replicas.json'
    def consume(member):
        entry=prepared['nodes'][member]
        config=str(box/'local-anchor/config.json') if member=='a' else manifest['nodes'][member]['home']+'/config.json'
        code=f'''import json,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
from source_readiness import snapshot
from crypto import app_private,sign,digest
c=json.loads(Path({config!r}).read_text());m,rows,prefix=snapshot(c);assert m=={member!r}
print(json.dumps(sign(app_private(Path(c['pki'])/'anchor'),'native-arrival-final-journal',
 dict(member=m,rows=rows,prefix=prefix,descriptor=c['arrival']['descriptor'],original_admission=digest(c['native_admission'])))))
'''
        signed=json.loads(deploy.execute(member,code,manifest,180))
        print('INDEPENDENT ARRIVAL JOURNAL',member,len(rows),flush=True)
        return member,signed
    if not path.exists():
        with ThreadPoolExecutor(max_workers=4) as pool:save(path,dict(pool.map(consume,'abcd')))
    reports=load(path);assert set(reports)==set('abcd')
    for member,signed in reports.items():
        report=verify(public_key(manifest['trust']['members'][member]),'native-arrival-final-journal',signed)
        assert [row[:4] for row in report['rows']]==rows
        assert report['prefix']==dict(seq=len(rows),head=rows[-1][2])
        assert report['descriptor']==manifest['arrival']['descriptor']
        assert report['original_admission']==digest(manifest['native_admission'])
    return {member:len(rows) for member in reports}


def runtime(box,manifest,home):
    from ha_quorum import Quorum
    quorum=Quorum(manifest['mac']['service'])
    with ThreadPoolExecutor(max_workers=4) as pool:
        jobs={member:pool.submit(node.call,'semantic-status') for member,node in quorum.nodes.items()}
        states={member:job.result() for member,job in jobs.items()}
    assert set(states)==set('abcd')
    prefix=load(home/'actual/after.json')['rows'][-1]
    assert all(v['prefix']==dict(seq=prefix[0],head=prefix[2]) and v['backend'] and not v['warm_error'] for v in states.values())
    results={};prepared=load(home/'prepared.json')
    for owner,member in [('mac','a'),('spark','c')]:
        entry=prepared['nodes'][member];cfg=manifest[owner]['service'];code=entry['code']
        state=str(box/'runtime') if member=='a' else manifest['nodes'][member]['home']+'/ha/runtime'
        script=f'''import hashlib,json,os,shlex,subprocess,sys
from pathlib import Path
sys.path.insert(0,{code!r})
from crypto import digest
from recovery_loop import birth,boot_identity
from ha_timing import public_configuration
p=Path({state!r});c=json.loads(Path({manifest[owner]['controller']['service']!r}).read_text())
assert digest(c)=={digest(cfg)!r};public_configuration(c)
w=c['online_privacy']['worker'];assert w['contract']=='original-source-arrival-public/v1'
assert w['lean_path']==c['arrival']['lean_path'] and w['cwd']==c['arrival']['cwd']
assert (Path(w['cwd'])/w['command'][-2])==Path(c['arrival']['exporter'])
assert hashlib.sha256(Path(c['arrival']['exporter']).read_bytes()).hexdigest()==c['arrival']['descriptor']['exporter_sha256']
assert {{n:hashlib.sha256((Path({code!r})/n).read_bytes()).hexdigest() for n in {list(manifest['protocol'])!r}}}=={manifest['protocol']!r}
s=json.loads((p/'ha-status.json').read_text());b=s['body'];assert birth(b['pid'])==b['birth'] and b['boot']==boot_identity()
r=dict(status=s,configuration=digest(c))
if b['phase']=='leader':
 ready=json.loads(Path({str(Path(cfg['database']).parent/'ha-service-ready.json')!r}).read_text());rb=ready['body'];worker=rb['public_timing']['worker']
 assert rb['grant']['point']==b['grant']['point'] and birth(rb['pid'])==rb['birth']
 assert birth(worker['pid'])==worker['birth'] and os.getpgid(worker['pid'])==b['service']['pgid']
 argv=shlex.split(subprocess.check_output(['ps','-ww','-p',str(worker['pid']),'-o','command='],text=True))
 assert argv==worker['argv']==w['command'] and argv[-1]=='public';r['ready']=ready
print(json.dumps(r))
'''
        value=json.loads(deploy.execute(member,script,manifest,90))
        status=verify(public_key(manifest['owners'][owner]),'ha-coordinator',value['status'])
        assert status['configuration']==digest(manifest[owner]['controller']) and time.time()-status['at']<25
        if 'ready' in value:verify(public_key(cfg['registry']['server']),'ha-service-ready',value['ready'])
        results[owner]=value
    assert sum(v['status']['body']['phase']=='leader' for v in results.values())==1
    save(home/'runtime-independent.json',dict(voters=states,candidates=results))
    print('CONTINUOUS ORIGINAL SERVICE PASS: four live semantic voters; two candidates; one public writer; admitted arrival worker',flush=True)


def run(box,full=False,check_main=False):
    home=deploy.location(box);directory=home/'actual';manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service']
    rows=[list(r) for r in deploy.roll.spare.rows(cfg['database'])];before=load(home/'original-before.json')['rows']
    assert len(rows)==77 and rows[:68]==before==load(directory/'before.json')
    assert rows==load(directory/'events.json')
    previous=load(home/'online-before.json');assert manifest['native_admission']==previous['native_admission']
    assert cfg['productive_extension']==previous['mac']['service']['productive_extension']
    historical=load(home.parents[1]/'final-check.json');assert historical['exit']==0 and historical['events']==68 and historical['head']==before[-1][2]
    commit=load(home.parents[1]/'integration.json')['commit']
    subprocess.run(['git','merge-base','--is-ancestor',commit,'refs/heads/main'],cwd=ROOT,check=True)
    for path,wanted in historical['inputs'].items():
        raw=subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT)
        assert __import__('hashlib').sha256(raw).hexdigest()==wanted
    activated,certificate=arrival_extension.require(cfg,rows);assert activated==69
    assert certificate==load(home/'admission.json')['certificate']
    argument,expected=ready_word(home,cfg)
    events=[json.loads(row[3])['body'] for row in rows[69:]]
    assert [event['native'] for event in events]==expected
    actual,scope,current=arrival_regeneration.context(cfg,rows)
    assert actual==load(directory/'source-input.json') and {**actual,'mode':'arrival-replay'}==argument
    for row in rows[68:]:
        event=json.loads(row[3])['body'];prefix=rows[:row[0]-1]
        if event['type']==arrival_extension.EVENT:arrival_extension.expected(cfg,prefix,event)
        else:arrival_regeneration.expected(cfg,prefix,event,native=False)
    material=trace(argument,expected,json.loads(before[-1][3])['body']['native']['next'])
    checker=object.__new__(Store);checker.config=cfg;checker.anchor=object()
    checker.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:checker.validate_anchor_receipts()
    finally:checker.database.close()
    prior_head='0'*64;sequences={};used=set();keys={cfg['registry'][n]['actor']:cfg['registry'][n] for n in ('auditor1','auditor2')}
    for sequence,prev,head,text in rows:
        signed=json.loads(text);event=verify(public_key(cfg['registry']['server']),'ledger',signed);req=event['request'];body=req['body']
        assert sequence==sum(sequences.values())+1 and prev==prior_head and ledger_hash(prev,signed)==head
        assert verify(public_key(keys[body['actor']]),req['kind'],req)==body
        assert body['seq']==sequences.get(body['actor'],0)+1
        assert body['nonce'] not in used and body['request_id'] not in used
        used.update((body['nonce'],body['request_id']));sequences[body['actor']]=body['seq'];prior_head=head
        if event['type']=='rotation':keys[body['actor']]=event['new']
    negative=[]
    for name in ('free-fuel','second-source-credit','erased-debt','source-budget','packet-payment'):
        changed=deepcopy(expected)
        if name=='free-fuel':changed[2]['service']['rows'][2]['debit']=[]
        elif name=='second-source-credit':changed[3]['credit']=[['audit:0','feed','3']]
        elif name=='erased-debt':changed[4]['next']['claims'][0][3]='1'
        elif name=='source-budget':changed[1]['sourceRows'][-1]['remainingAfter']=21
        else:changed[4]['service']['packets'][0][0]['payment']['available']='0'
        try:trace(argument,changed,json.loads(before[-1][3])['body']['native']['next'])
        except (AssertionError,ValueError,KeyError):negative.append(name)
        else:raise AssertionError('ARRIVAL_MUTATION_ACCEPTED:'+name)
    for name,mutate in [('parent',lambda c:c['point'].update(parent='0'*64)),('missing-vote',lambda c:c['votes'].pop()),('source-root',lambda c:c['point']['descriptor'].update(source_root='invented'))]:
        changed=deepcopy(certificate);mutate(changed)
        try:arrival_extension.admission(cfg,changed)
        except (AssertionError,ValueError,InvalidSignature):negative.append(name)
        else:raise AssertionError('ARRIVAL_ADMISSION_MUTATION_ACCEPTED:'+name)
    transport=prior.wire(box,manifest,home,rows,before,expected_events=9)
    owner=load(directory/'owner-accepted.json');assert owner['exit']==0 and owner['events']==sha(directory/'events.json')
    closed_inventory_evidence(home,manifest)
    assert owner['closed']==sha(directory/'closed.json') and owner['source']==sha(ROOT/'Lean/scripts/verification/public-arrival-owner-source.lean')
    assert owner['input']==digest(actual)
    for name,wanted in owner['branches'].items():assert sha(directory/(name+'.json'))==wanted
    replicas=journals(box,manifest,rows,home);runtime(box,manifest,home)
    resumed=module('arrival_resumed_consumer','public-arrival-resume.py').check(box)
    privacy=module('arrival_universal_privacy','public-arrival-privacy-check.py').verify(box,check_main)
    if full:
        result=subprocess.run([sys.executable,str(ROOT/'.agents/tmp/public-autonomous-origin-20261101/final-audit/verify.py')],cwd=ROOT,capture_output=True,text=True)
        (home/'full-cost.log').write_text(result.stdout+result.stderr);assert result.returncode==0,result.stdout[-1400:]+result.stderr[-1000:]
        print(result.stdout,end='',flush=True)
    axioms=load(home/'axioms.json');assert axioms['exit']==0 and axioms['mouths']==6
    assert set(axioms['axioms'])<=set(['propext','Classical.choice','Quot.sound'])
    assert sha(home/'axioms.log')==axioms['log_sha256']
    assert load(home/'history-exit.json')['exit']==load(home/'wire-exit.json')['exit']==load(home/'owner-compile.json')['exit']==0
    paths=[Path(__file__),Path(__file__).with_name('public-ha-check.py'),*[Path(__file__).with_name('public-arrival-'+n) for n in ('deploy.py','actual.py','resume.py','network-source.lean','owner-source.lean')],*[NETWORK/n for n in manifest['protocol']]]
    origin=load(home.parent/'independent.json');assert origin['exit']==0 and origin['main_verified']
    empty=load(home.parent/'empty-kernel.json')
    assert empty['exit']==0 and empty['roots']>=27 and empty['axioms']==['Classical.choice','Quot.sound','propext']
    assert sha(home.parent/'empty-kernel.log')==empty['log_sha256']
    assert sha(home.parent/'empty-kernel-setup.json')==empty['setup_sha256']
    assert sha(ROOT/'Lean/scripts/verification/public-external-arrival-kernel.lean')==empty['source_sha256']
    inputs={path:sha(ROOT/path) for path in historical['inputs']}
    inputs.update({str(p.relative_to(ROOT)):sha(p) for p in paths});inputs.update(axioms['sources']);inputs.update(origin['inputs'])
    inputs.update(privacy['inputs'])
    for path,wanted in inputs.items():
        assert sha(ROOT/path)==wanted
        if check_main:assert __import__('hashlib').sha256(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT)).hexdigest()==wanted,('MAIN_SOURCE_CHANGED',path)
    report=dict(exit=0,events=77,head=rows[-1][2],original_events=68,arrival=material,wire=transport,
        replicas=replicas,scope=scope,current=current,resumed=resumed,universal_privacy=privacy,
        negative_controls=negative,inputs=inputs,full=full,main_verified=check_main)
    save(home/'final-check.json',report)
    print('INDEPENDENT ARRIVAL LIVE AUDIT PASS '+json.dumps({k:report[k] for k in ('events','arrival','wire','replicas','main_verified')},sort_keys=True),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--closed',action='store_true');p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    if a.closed:closed_replay(a.box.resolve())
    else:run(a.box.resolve(),a.full,a.check_main)
