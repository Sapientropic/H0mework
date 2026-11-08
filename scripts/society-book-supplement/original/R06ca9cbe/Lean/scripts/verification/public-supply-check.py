"""Independent original-ledger, full-output, material and closed-owner supply audit."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
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

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from crypto import canonical,digest,verify
from online_privacy import source_input
from online_privacy_check import tls_streams
from quorum import verify_certificate
from recovery_loop import save
from service import Store
from source_semantics import Engine
import energy,governance,regeneration,source_extension


def module(name,filename):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


deploy=module('supply_check_deploy','public-supply-deploy.py')
old=module('supply_check_continuous','public-continuous-check.py')
privacy=module('supply_check_material','public-supply-privacy-check.py')
load,sha=deploy.load,deploy.sha


def public_material(events,reference):
    assert len(events)==13
    dual=0
    for index,(event,expected) in enumerate(zip(events,reference,strict=True)):
        value=event['native'];request=event['request']['body']
        assert value['metadata']==dict(query=request['query'],mode=request['mode'],metadata=request),'EXACT_COMMAND_METADATA'
        assert value['history']==index+1 and value['opening']==expected['opening'],'OWN_HISTORY'
        assert privacy.public_state(value['next'])==privacy.original.state(expected['next']),'ACTUAL_MATERIAL_OR_CLAIMS'
        assert len(value['rows'])==len(expected['rows'])
        assert value['packets']==expected['evidence'],'ORIGINAL_SERVICE_EVIDENCE'
        for item,before_after in zip(value['rows'],expected['rows'],strict=True):
            assert set(item)=={'index','request','accepted','debit','credit'}
            assert item['index']==before_after['index'] and item['accepted']==before_after['accepted']
            assert item['request']['signer']==before_after['action']['signer']
            assert item['request']['operation']['kind']==before_after['action']['op']['kind']
            before=privacy.original.state(before_after['before']);stock=dict(before['stock'])
            if not item['accepted']:assert item['debit']==item['credit']==[],'REFUSAL_IS_NOT_PAYMENT'
            for factor,flow in [(-1,item['debit']),(1,item['credit'])]:
                for party,good,amount in flow:
                    assert Q(amount)>=0;stock[party,good]+=factor*Q(amount)
            assert stock==privacy.original.state(before_after['after'])['stock'],'PAID_FLOW'
        for packet in value['packets']:
            for evidence in packet:
                outcomes=[privacy.original._dual.payment_scan(evidence['slot'],evidence),
                          privacy.original._dual.lifecycle_replay(evidence['slot'],evidence)]
                assert all(x in ('verified','insufficient') for x in outcomes),'MISSING_EVIDENCE_IS_NOT_A_VIOLATION'
                dual+=2
    assert events[0]['native']['status']=='BLOCKED'
    assert sum(e['native']['opening'] for e in events)==3
    assert sum(bool(e['native']['packets']) for e in events)==3
    return dual


def observations(box,manifest,directory,rows,before):
    config=manifest['mac']['service'];server=public_key(config['registry']['server'])
    boundaries,wire=old.wires(directory,config)
    additions=rows[len(before):];lookups={row[0]:0 for row in additions};observed=0;unknown=[];primary=set();matched=set()
    paths=sorted(directory.glob('*-observation.json'))
    for row in additions:
        event=json.loads(row[3])['body'];raw=source_input(config,rows[:row[0]-1],event)
        assert any(b['phase']=='before-intent' and b['seq']==row[0] and b['event']==digest(event)
            and b['input']==raw and b['native']==digest(event['native']) for b in boundaries),'ORIGINAL_PUBLIC_GATE'
    for path in paths:
        signed=load(path);actor=signed['body']['request']['body']['actor']
        key=public_key(config['registry']['auditor'+actor]);value=verify(key,'online-client-observation',signed)
        assert value['peer']['uri']=='urn:public-audit:server'
        assert all(value['peer'][k]==config['registry']['server'][k] for k in ('fingerprint','app'))
        challenge=verify(server,'challenge',value['challenge']);request=value['request'];body=verify(key,request['kind'],request)
        assert all(body[k]==challenge[k] for k in ('source','stream','actor','nonce','seq','cut','epoch','expires'))
        times=[value['times'][k] for k in ('connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns')]
        assert times==sorted(times) and all(type(t) is int for t in times)
        response=value['response']
        if 'transport_error' in response:
            assert response['transport_error'] in {'EOFError','TimeoutError','SSLEOFError','ConnectionResetError'}
            assert request['kind'] in {source_extension.EVENT,regeneration.KIND}
            committed=[row for row in additions if json.loads(row[3])['body']['request']==request]
            assert len(committed)==1,'UNKNOWN_MUST_RECOVER_ITS_ORIGINAL_EVENT'
            partial=[v for _,v,sent,received in wire if sent and sent[0]==value['challenge'] and received==[request]]
            assert len(partial)<=1
            # An EOF may clear SSL.version() on the client. Retain that None;
            # the matching signed server occurrence supplies the TLS fact.
            assert value['tls'] in ('TLSv1.3',None)
            if value['tls'] is None:assert partial and partial[0]['tls']=='TLSv1.3'
            late=[sent[1] for _,v,sent,received in wire if digest(v) in {digest(p) for p in partial} and len(sent)==2]
            for message in late:
                reply=verify(server,message['kind'],message)
                if message['kind']=='response':assert reply['ledger']==json.loads(committed[0][3])
                else:assert message['kind']=='error'
            matched.update(digest(v) for v in partial)
            primary.add(committed[0][0]);unknown.append(dict(request=digest(request),event=committed[0][0],
                status='insufficient-reply',transport=response['transport_error']))
            continue
        envelope=verify(server,response['kind'],response)
        if request['kind']=='lookup':
            assert response['kind']=='lookup-response' and envelope['request']==digest(request)
            result=envelope['result'];lookups[result['anchor']['body']['seq']]+=1
            assert result['event']['request']['body']['request_id']==body['lookup_id']
        else:
            assert request['kind'] in {source_extension.EVENT,regeneration.KIND} and response['kind']=='response'
            result=envelope;assert result['event']['request']==request
            primary.add(result['anchor']['body']['seq'])
        row=rows[result['anchor']['body']['seq']-1]
        assert result['ledger']==json.loads(row[3]) and result['event']==result['ledger']['body']
        assert result['head']==row[2] and result['request']==digest(result['event']['request'])
        verify_certificate(manifest['trust'],result['anchor'],source=config['source'],stream='recovery',
            seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
        assert value['tls']=='TLSv1.3'
        matching=[v for owner,v,sent,received in wire if sent==[value['challenge'],response] and received==[request]]
        assert len(matching)==1,'SIGNED_SERVER_AND_CLIENT_WIRE'
        matched.add(digest(matching[0]))
        observed+=1
    assert primary==set(lookups) and all(n>=2 for n in lookups.values()),'ORIGINAL_ID_RETRIES'
    unsubmitted=[]
    # Monotonic clocks belong to their physical owner. Never compare the Mac
    # observer's counter with a Spark server counter to select this epoch.
    windows={}
    for owner,value,_,_ in wire:
        if digest(value) in matched:
            first,last=windows.get(owner,(value['started_ns'],value['finished_ns']))
            windows[owner]=(min(first,value['started_ns']),max(last,value['finished_ns']))
    for owner,value,sent,received in wire:
        if (owner not in windows or not windows[owner][0]<=value['started_ns']<=windows[owner][1]
                or digest(value) in matched):continue
        assert not received and 1<=len(sent)<=2,'UNACCOUNTED_SUBMITTED_REQUEST'
        challenge=verify(server,'challenge',sent[0])
        assert challenge['source']==config['source'] and challenge['stream']=='recovery'
        identity=next(entry for entry in config['registry'].values()
            if entry.get('fingerprint')==value['peer']['fingerprint'] and entry.get('app')==value['peer']['app'])
        assert challenge['actor']==identity['actor'] and value['tls']=='TLSv1.3'
        if len(sent)==2:verify(server,'error',sent[1])
        unsubmitted.append(dict(challenge=digest(sent[0]),status='no-submitted-command',server_observation=digest(value)))
    captures={}
    for path in directory.glob('tls-*.jsonl.gz'):
        with gzip.open(path,'rt') as stream:
            for line in stream:
                item=json.loads(line);key=(path.name,item['connection'])
                if item['direction']=='client' and item['phase']=='received':
                    captures[key]=min(captures.get(key,item['at_ns']),item['at_ns'])
    intervals=[load(path)['body']['times'] for path in paths]
    orphan=[(key,at) for key,at in captures.items() if not any(
        span['connect_start_ns']<=at<=span['response_received_ns'] for span in intervals)]
    # Keep a failed pre-send attempt as insufficient application evidence. Its
    # raw bytes, stale original authorization and same-observer interval stay
    # bound; it is never promoted to a fictitious signed client observation.
    unused=[]
    for path in directory.glob('*-unsubmitted-owner-*.json'):
        label=path.name.split('-unsubmitted-owner-')[0];ordinal=int(label.split('-')[-1])
        proof=load(path);body=proof['body'];registration=next(e for e in governance.registered(rows)
            if e['result']['key']==body['executor'])
        who=registration['proof']['body']['owner']
        assert verify(public_key(config['ha']['owners'][who]),'native-energy-regeneration',proof)==body
        assert body['parent']['head']==rows[body['parent']['seq']-1][2]
        assert json.loads(rows[body['parent']['seq']][3])['body']['request']['body']['execution']==proof
        assert load(directory/(label+'-request.json'))['body']['execution']!=proof
        prior=load(directory/('supply-'+str(ordinal-1)+'-lookup-1-observation.json'))['body']['times']['response_received_ns']
        later=load(directory/(label+'-observation.json'))['body']['times']['connect_start_ns']
        matches=[key for key,at in orphan if prior<=at<=later]
        assert len(matches)==1,'UNATTRIBUTED_TLS_ATTEMPT'
        unused.append(matches[0]);unsubmitted.append(dict(capture=list(matches[0]),authorization=digest(proof),
            status='insufficient-application-evidence'))
    assert set(unused)=={key for key,_ in orphan} and len(unused)==len(orphan)
    assert len(captures)==observed+len(unknown)+len(unsubmitted)
    streams=tls_streams(directory,expected_connections=len(captures))
    return dict(observations=observed,lookups=sum(lookups.values()),tls_streams=len(streams),unknown=unknown,unsubmitted=unsubmitted)


def closed_replay(box):
    home=deploy.location(box);directory=home/'actual'
    manifest=old.live.public_closed(box,directory);cfg=manifest['mac']['service']
    rows=load(directory/'events.json');point=source_extension.require(cfg,rows)
    # Reconstruct the original source input from the actual signed old journal.
    argument,_,_=regeneration.context(cfg,rows)
    assert argument==load(directory/'source-input.json')
    script=ROOT/'Lean/scripts/verification/public-supply-owner-source.lean'
    env=os.environ.copy();env['LEAN_PATH']=cfg['regeneration']['lean_path'];answers={}
    for lane in ('private-one','private-two'):
        command=[cfg['regeneration']['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',
                 '--run',str(script),lane]
        run=subprocess.run(command,cwd=ROOT/'Lean',env=env,input=canonical(argument)+b'\n',
            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=300)
        (directory/(lane+'.json')).write_bytes(run.stdout);(directory/(lane+'.stderr')).write_bytes(run.stderr)
        assert run.returncode==0 and not run.stderr,(run.returncode,run.stderr[-1600:])
        answer=json.loads(run.stdout);answers[lane]=answer
        actual=[json.loads(row[3])['body']['native'] for row in rows[point[0]:]]
        assert answer['output']==actual,'DEFAULT_OUTPUT_MUST_BE_ITS_ACTUAL_BRANCH'
        assert answer['history']==13 and answer['nativeSlots']==9 and answer['nativeOutstanding']=='0'
        assert answer['ownFrame']==('39' if lane=='private-one' else '38')
    assert answers['private-one']['output']==answers['private-two']['output']
    save(directory/'owner-accepted.json',dict(closed=sha(directory/'closed.json'),events=sha(directory/'events.json'),
        source=sha(script),input=digest(argument),branches={k:sha(directory/(k+'.json')) for k in answers},
        replies=26,frames=['39','38'],native_slots=9,native_outstanding='0'))
    print('INDEPENDENT CLOSED SUPPLY PASS: 26 exact replies; own private frames39/38; persistent9 native slots fully settled',flush=True)


def replicas(box,manifest,rows,home=None,source_key='regeneration'):
    home=deploy.location(box) if home is None else home
    descriptor=manifest['productive' if source_key=='productive' else 'material' if source_key=='refeed' else 'regeneration']['descriptor']
    saved=home/'replicas.json'
    if saved.exists():
        reports=load(saved);assert set(reports)==set('abcd')
        for member,signed in reports.items():
            value=verify(public_key(manifest['trust']['members'][member]),'native-supply-final-replay',signed)
            assert value['member']==member and value['rows']==rows
            assert value['prefix']==dict(seq=len(rows),head=rows[-1][2])
            assert value['descriptor']==descriptor
            assert value['original_admission']==digest(manifest['native_admission'])
        print('PAID INDEPENDENT JOURNALS VERIFIED: four signed exact'+str(len(rows))+' replays retained',flush=True)
        return {m:len(v['body']['rows']) for m,v in reports.items()}
    def consume(member):
        entry=load(home/'prepared.json')['nodes'][member]
        configpath=str(box/'local-anchor/config.json') if member=='a' else manifest['nodes'][member]['home']+'/config.json'
        code=f'''import json,sqlite3,sys
from pathlib import Path
sys.path.insert(0,{entry['code']!r})
from crypto import app_private,canonical,digest,sign
from source_semantics import Engine
from source_readiness import close_all
c=json.loads(Path({configpath!r}).read_text())
with sqlite3.connect(Path(c['database']).as_uri()+'?mode=ro',uri=True) as db:
 rows=db.execute('SELECT seq,previous,hash,message FROM entries WHERE stream=? ORDER BY seq',('recovery',)).fetchall()
 original=db.execute('SELECT value FROM native_admission').fetchall()
 assert original==[(canonical(c['native_admission']).decode(),)]
Engine(c[{source_key!r}])
e=Engine({{**c['semantic'],'error_log':{entry['root']+'/final-independent-'+member+'.log'!r}}})
try:
 e.sync(rows,__import__('time').monotonic()+300);status=e.status()
 assert status['prefix']=={{'seq':len(rows),'head':rows[-1][2]}}
 print(json.dumps(sign(app_private(Path(c['pki'])/'anchor'),'native-supply-final-replay',
  dict(member={member!r},rows=rows,prefix=status['prefix'],original_admission=digest(c['native_admission']),
   source_backend=status['backend'],descriptor=c[{source_key!r}]['descriptor']))))
finally:close_all(e)
'''
        # Productive prefixes are full source calls; retain one replay rather
        # than cutting it off at the older short-history transport budget.
        seconds=700
        if source_key=='productive':
            seconds+=len(rows)*entry['config'][source_key].get('native_call_seconds',30)
        signed=json.loads(deploy.execute(member,code,manifest,seconds))
        report=verify(public_key(manifest['trust']['members'][member]),'native-supply-final-replay',signed)
        assert report['member']==member
        assert report['rows']==rows
        assert report['original_admission']==digest(manifest['native_admission'])
        print('INDEPENDENT ORIGINAL JOURNAL PASS',member,len(rows),flush=True)
        return member,signed
    with ThreadPoolExecutor(max_workers=4) as pool:reports=dict(pool.map(consume,'abcd'))
    save(home/'replicas.json',reports)
    return {m:len(v['body']['rows']) for m,v in reports.items()}


def current_runtime(box,manifest,rows,home=None):
    result={}
    for owner,member in [('mac','a'),('spark','c')]:
        cfg=manifest[owner]['service']
        state=str(box/'runtime') if member=='a' else manifest['nodes'][member]['home']+'/ha/runtime'
        receipts=manifest.get('application_receipts')
        codepath=(receipts['candidates'][owner]['code'] if receipts else
                  str(NETWORK) if member=='a' else manifest['nodes'][member]['code'])
        protocol=receipts['protocol'] if receipts else manifest['protocol']
        source_key='productive' if 'productive' in manifest else 'refeed' if 'material' in manifest else 'regeneration'
        worker_contract='complete-default-productive-privacy/v1' if source_key=='productive' else 'complete-default-material-privacy/v1' if source_key=='refeed' else 'complete-default-supply-privacy/v1'
        script=f'''import hashlib,json,os,shlex,subprocess,sys
from pathlib import Path
sys.path.insert(0,{codepath!r})
from crypto import digest
from recovery_loop import birth,boot_identity
from ha_timing import public_configuration
from source_semantics import Engine
p=Path({state!r})
configuration=json.loads(Path({manifest[owner]['controller']['service']!r}).read_text())
assert digest(configuration)=={digest(cfg)!r}
public_configuration(configuration);source=configuration[{source_key!r}];Engine(source)
worker=configuration['online_privacy']['worker'];closure=json.loads(Path(source['closure']).read_text())
assert worker['contract']=={worker_contract!r}
assert worker['lean_path']==source['lean_path'] and worker['cwd']==source['cwd']
assert Path(worker['cwd'])/worker['command'][-2]==Path(source['exporter'])
assert hashlib.sha256(Path(worker['command'][0]).read_bytes()).hexdigest()==worker['compiler_sha256']
inputs={{source['exporter']:source['descriptor']['exporter_sha256'],source['closure']:source['descriptor']['closure_sha256']}}
inputs.update({{source['lean_path']+'/'+n:wanted for n,wanted in closure.items()}})
assert configuration['online_privacy']['source_inputs']==inputs
assert {{n:hashlib.sha256((Path({codepath!r})/n).read_bytes()).hexdigest() for n in {list(protocol)!r}}}=={protocol!r}
# Full closure verification can outlive a heartbeat. Sample liveness afterwards.
status=json.loads((p/'ha-status.json').read_text());body=status['body']
assert birth(body['pid'])==body['birth'] and body['boot']==boot_identity()
actual=shlex.split(subprocess.check_output(['ps','-ww','-p',str(body['pid']),'-o','command='],text=True))
assert actual[-3:]==[{codepath+'/live_timing.py'!r},'coordinator',{manifest[owner]['controller']['service'].replace('/service.json','/controller.json')!r}]
result=dict(status=status,argv=actual,configuration=digest(configuration))
if body['phase']=='leader':
 ready=json.loads(Path({str(Path(cfg['database']).parent/'ha-service-ready.json')!r}).read_text());rb=ready['body'];public=rb['public_timing']
 assert rb['grant']['point']==body['grant']['point'] and birth(rb['pid'])==rb['birth']
 w=public['worker'];assert birth(w['pid'])==w['birth'] and os.getpgid(w['pid'])==body['service']['pgid']
 assert public['entrypoint']=='live_timing.py'
 child=json.loads((p/'ha-service.json').read_text());child['recover_from_anchor']=True
 assert public['configuration']==digest(child)
 argv=shlex.split(subprocess.check_output(['ps','-ww','-p',str(w['pid']),'-o','command='],text=True))
 assert argv==w['argv']==worker['command'] and argv[-1]=='public'
 result['ready']=ready
print(json.dumps(result))
'''
        value=json.loads(deploy.execute(member,script,manifest,240))
        status=verify(public_key(manifest['owners'][owner]),'ha-coordinator',value['status'])
        assert status['configuration']==digest(manifest[owner]['controller']) and time.time()-status['at']<20
        if 'ready' in value:
            ready=verify(public_key(cfg['registry']['server']),'ha-service-ready',value['ready'])
            assert ready['head'] in {row[2] for row in rows}
        result[owner]=value
    assert sum(v['status']['body']['phase']=='leader' for v in result.values())==1
    save((deploy.location(box) if home is None else home)/'runtime-independent.json',result)
    print('CURRENT ORIGINAL RUNTIME PASS: two owned candidates; one public writer; exact new source view',flush=True)


def run(box,full=False,check_main=False):
    home=deploy.location(box);directory=home/'actual';manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service']
    rows=[list(r) for r in deploy.roll.spare.rows(cfg['database'])];before=load(directory/'before.json')
    kernel=load(home/'kernel.json')
    assert kernel['exit']==0 and kernel['mouths']==89
    assert set(kernel['axioms'])=={'Classical.choice','Quot.sound','propext'}
    assert kernel['log_sha256']==sha(home/'kernel.log')
    production=load(home.parent/'supply/production.json')
    assert production['literal_sha256']==sha(home.parent/'supply/production-actual.jsonl')
    for path,wanted in production['source_sha256'].items():assert sha(ROOT/path)==wanted
    certified=load(home.parent/'supply/privacy/certify.json')
    for path,wanted in certified['source_sha256'].items():
        if path.endswith('public-supply-network-source.lean'):continue
        assert sha(ROOT/path)==wanted
    for path,wanted in certified['artifact_sha256'].items():
        assert sha(home.parent/'supply/privacy'/path)==wanted
    assert sha(ROOT/'Lean/scripts/verification/public-supply-network-source.lean')==manifest['regeneration']['descriptor']['exporter_sha256']
    assert rows[:len(before)]==before and len(rows)==len(before)+14
    previous=load(box/'ha/continuous/final-check.json');integration=load(box/'ha/continuous/main-verified.json')
    assert previous['exit']==0 and previous['main_verified'] and previous['full'] and previous['events']==len(before)
    assert previous['head']==before[-1][2]
    subprocess.run(['git','merge-base','--is-ancestor',integration['commit'],'refs/heads/main'],cwd=ROOT,check=True)
    for path,wanted in previous['source_inputs'].items():
        assert sha_bytes(subprocess.check_output(['git','show',integration['commit']+':'+path],cwd=ROOT))==wanted
    activated,certificate=source_extension.require(cfg,rows)
    assert activated==len(before)+1 and certificate==load(home/'admission.json')
    assert manifest['native_admission']==load(home/'before.json')['native_admission']
    checker=object.__new__(Store);checker.config=cfg;checker.anchor=object()
    class Signer:
        def public_key(self):return public_key(cfg['registry']['server'])
    checker.key=Signer();checker.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:checker.validate_ledger();checker.validate_anchor_receipts()
    finally:checker.database.close();old.release_readers()
    events=[json.loads(r[3])['body'] for r in rows[activated:]]
    reference=privacy.reference_groups(home.parent/'supply/production-actual.jsonl')['withhold-fuel']
    dual=public_material(events,reference);negative=[]
    for label in ('metadata','fee','private-disclosure','packet','history'):
        bad=deepcopy(events);native=bad[0]['native']
        if label=='metadata':native['metadata']['metadata']['actor']='permanent-seat'
        elif label=='fee':
            paid=next(item for event in bad for item in event['native']['rows'] if item['debit'])
            paid['debit'][0][2]=str(Q(paid['debit'][0][2])+1)
        elif label=='private-disclosure':native['next']['stock'].append(['audit:3','feed','39'])
        elif label=='packet':next(event for event in bad if event['native']['packets'])['native']['packets'][0][0]['payment']=None
        else:native['history']+=1
        try:public_material(bad,reference)
        except AssertionError:negative.append(label)
        else:raise AssertionError('LIVE_MUTATION_ACCEPTED:'+label)
    wire=observations(box,manifest,directory,rows,before)
    accepted=load(directory/'owner-accepted.json')
    assert accepted['closed']==sha(directory/'closed.json') and accepted['events']==sha(directory/'events.json')
    assert accepted['source']==sha(ROOT/'Lean/scripts/verification/public-supply-owner-source.lean')
    for lane,wanted in accepted['branches'].items():
        assert sha(directory/(lane+'.json'))==wanted
        answer=load(directory/(lane+'.json'));assert answer['output']==[e['native'] for e in events]
        assert answer['nativeSlots']==9 and answer['nativeOutstanding']=='0'
    counts=replicas(box,manifest,rows)
    current_runtime(box,manifest,rows)
    application=None
    if manifest.get('application_receipts'):
        application=module('current_application_receipts','public-application-check.py').check(box,check_main)
    if full:
        run=subprocess.run([sys.executable,str(ROOT/'.agents/tmp/public-autonomous-origin-20261101/final-audit/verify.py')],
            cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (home/'full-cost.log').write_text(run.stdout);assert run.returncode==0,run.stdout[-1600:]
        print(run.stdout,end='',flush=True)
    inputs={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),
        *[Path(__file__).with_name('public-supply-'+s) for s in ('deploy.py','actual.py','network-source.lean','owner-source.lean')],
        *[NETWORK/n for n in load(home/'prepared.json')['protocol']],NETWORK/'online_privacy_check.py']}
    inputs.update(old.source_inputs(box/'ha/continuous'))
    proof=ROOT/'Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Privacy'
    inputs.update({str(p.relative_to(ROOT)):sha(p) for p in proof.glob('*.lean')})
    if check_main:
        for p,wanted in inputs.items():assert sha_bytes(subprocess.check_output(['git','show','refs/heads/main:'+p],cwd=ROOT))==wanted,('MAIN_SOURCE_CHANGED',p)
    assert [list(r) for r in deploy.roll.spare.rows(cfg['database'])]==rows,'JOURNAL_CHANGED_DURING_AUDIT'
    result=dict(exit=0,events=len(rows),head=rows[-1][2],original_events=len(before),admission=activated,
        supply_requests=13,new_windows=3,paid_deliveries=3,replicas=counts,dual_checks=dual,wire=wire,
        negative_controls=negative,closed_owner=accepted,inputs=inputs,full=full,main_verified=check_main)
    if application is not None:result['application_receipts']=application
    save(home/'final-check.json',result)
    print('INDEPENDENT ONLINE SUPPLY AUDIT PASS '+json.dumps({k:result[k] for k in ('events','replicas','supply_requests','new_windows','paid_deliveries','wire','main_verified')},sort_keys=True),flush=True)


def sha_bytes(value):
    return __import__('hashlib').sha256(value).hexdigest()


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path)
    parser.add_argument('--closed',action='store_true');parser.add_argument('--full',action='store_true');parser.add_argument('--check-main',action='store_true')
    args=parser.parse_args()
    if args.closed:closed_replay(args.box.resolve())
    else:run(args.box.resolve(),args.full,args.check_main)
