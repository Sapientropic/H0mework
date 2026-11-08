"""Independent material, financial, TLS and own-successor replay of the original line."""
import argparse
import base64
from copy import deepcopy
from fractions import Fraction as Q
import importlib.util
import json
import os
from pathlib import Path
import sqlite3
import subprocess
import sys
from cryptography.exceptions import InvalidSignature

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from application_receipt_check import replay
from crypto import canonical,digest,verify
from online_privacy import source_input
from online_privacy_check import frames,tls_streams
from quorum import verify_certificate
from recovery_loop import save
from service import Store
import material_extension,material_regeneration

def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
deploy=module('material_check_deploy','public-material-deploy.py')
old=module('material_check_supply','public-supply-check.py')
load,sha=deploy.load,deploy.sha


def state(value):
    result=deepcopy(value);result['clock']=Q(result['clock'])
    assert len(result['stock'])==48 and len(result['claims'])==147
    result['stock']={(a,g):Q(n) for a,g,n in result['stock']}
    result['claims']={(i,p,q):Q(n) for i,p,q,n in result['claims']}
    assert len(result['stock'])==48 and len(result['claims'])==147
    assert ('audit:3','feed') not in result['stock']
    return result


def material(parent,events):
    assert len(events)==7
    assert [e['request']['body']['mode'] for e in events]==['deny-recycling']*4+['refeed','normal','normal']
    assert all(e['request']['body']['query']==dict(slots=63,fields=3) for e in events)
    initial=state(parent);current=deepcopy(initial);production=recycling=deliveries=openings=dual=0
    births=settlements=0;refusals=[]
    for index,event in enumerate(events):
        result=event['native'];body=event['request']['body']
        assert result['metadata']==dict(query=body['query'],mode=body['mode'],metadata=body)
        assert result['history']==14+index
        current['clock']+=1;current['round']+=1
        for ordinal,item in enumerate(result['rows']):
            assert item['index']==ordinal
            request=item['request'];op=request['operation'];kind=op['kind']
            debit=[];credit=[];expected=deepcopy(current)
            if not item['accepted']:
                assert ordinal==len(result['rows'])-1 and item['debit']==item['credit']==[]
                refusals.append((index,kind,request['signer']));continue
            def flow(actor,good,n):return [actor,good,str(Q(n))]
            if kind=='produce':
                actor=op['actor'];assert request['signer']==actor
                if actor=='provider:0':
                    debit=[flow(actor,'feed',1),flow(actor,'labor',1)]
                    credit=[flow(actor,'energy',2),flow(actor,'labor',3)];production+=1
                elif actor=='provider:2':
                    debit=[flow(actor,'waste',1),flow(actor,'energy',1),flow(actor,'labor',1)]
                    credit=[flow(actor,'feed',1)];recycling+=1
                else:raise AssertionError('UNKNOWN_PRODUCTION_SOURCE')
                assert request['purpose']==dict(kind='provider',base='reserve',owner=int(actor.split(':')[1]))
            elif kind=='transfer':
                assert request['signer']==op['from']
                debit=[flow(op['from'],g,n) for g,n in op['bundle']]
                credit=[flow(op['to'],g,n) for g,n in op['bundle']]
            elif kind=='use':
                assert request['signer']==op['actor']
                debit=[flow(op['actor'],g,n) for g,n in op['bundle']]
            elif kind=='revise':
                assert request['signer']==op['actor'] and op['actor'].startswith('audit:')
                debit=[flow(op['actor'],'energy',1)];expected['technology']=deepcopy(op['technology'])
            elif kind in ('issue','settle'):
                assert op['instrument']=='delivery' and op['debtor']=='provider:0' and op['creditor']=='audit:3'
                assert request['signer']==op['debtor'] and Q(op['quantity'])>0
                key=('delivery','provider:0','audit:3');n=Q(op['quantity'])
                if kind=='issue':
                    assert expected['claims'][key]==0 and n==2
                    expected['claims'][key]+=n;births+=1
                else:
                    assert expected['claims'][key]>=n
                    expected['claims'][key]-=n;debit=[flow(op['debtor'],'energy',n)];credit=[flow(op['creditor'],'energy',n)];settlements+=1
            else:raise AssertionError('UNKNOWN_MATERIAL_OPERATION')
            def amounts(entries):
                out={}
                for a,g,n in entries:out[a,g]=out.get((a,g),Q(0))+Q(n)
                return {k:v for k,v in out.items() if v}
            assert amounts(item['debit'])==amounts(debit) and amounts(item['credit'])==amounts(credit),'RECIPE_OR_FEE_CHANGED'
            for (a,g),n in amounts(debit).items():
                assert n>=0 and current['stock'][a,g]>=n;expected['stock'][a,g]-=n
            for (a,g),n in amounts(credit).items():assert n>=0;expected['stock'][a,g]+=n
            current=expected
        current['clock']+=1;current['round']+=1
        assert state(result['next'])==current,'COMPLETE_MATERIAL_SUCCESSOR'
        for key,n in initial['claims'].items():
            if key[0]!='delivery':assert current['claims'][key]==n,'ORIGINAL_CLAIM_CHANGED'
        openings+=result['opening'];deliveries+=bool(result['packets'])
        for packet in result['packets']:
            assert [e['slot'] for e in packet]==list(range(6))
            for e in packet:
                assert old.privacy.original._dual.payment_scan(e['slot'],e)=='verified'
                assert old.privacy.original._dual.lifecycle_replay(e['slot'],e)=='verified';dual+=2
    assert production==4 and recycling==1 and births==settlements==3
    assert openings==deliveries==1 and current['claims']['delivery','provider:0','audit:3']==0
    assert current['stock']['audit:0','feed']==initial['stock']['audit:0','feed']-3
    assert current['stock']['provider:1','waste']==initial['stock']['provider:1','waste']-1
    assert current['stock']['provider:0','labor']==initial['stock']['provider:0','labor']+6
    assert current['stock']['provider:2','energy']==current['stock']['provider:2','labor']==1
    # The denied recycler's actual worker payment is consumed before another funding stage.
    assert events[3]['native']['rows'][-1]['request']['signer']=='audit:0'
    first=events[4]['native']['rows'][:2]
    assert [r['request']['operation']['kind'] for r in first]==['produce','transfer']
    assert first[0]['request']['operation']['actor']=='provider:2'
    return dict(production=production,recycling=recycling,new_windows=openings,deliveries=deliveries,
                births=births,settlements=settlements,dual_checks=dual,refusals=refusals,feed_left=str(current['stock']['audit:0','feed']))


def records(path):return [json.loads(line) for line in Path(path).read_text().splitlines()]


def wire(box,manifest,home,rows,before,expected_events=8):
    cfg=manifest['mac']['service'];directory=home/'actual';server=public_key(cfg['registry']['server'])
    client=replay(records(directory/'applications.jsonl'),public_key(cfg['registry']['auditor2']),cfg['source'],'recovery','client',cfg['registry'])
    counterparts={};boundaries=[];legacy=[]
    for owner in ('mac','spark'):
        counterparts.update(replay(records(directory/(owner+'-applications.jsonl')),server,cfg['source'],'recovery','server',cfg['registry']))
        for signed in records(directory/(owner+'-boundary.jsonl')):
            if signed['kind']=='online-privacy-boundary':boundaries.append(verify(server,signed['kind'],signed))
            elif signed['kind']=='online-wire-observation':legacy.append(verify(server,signed['kind'],signed))
    incomplete=[];matched=[];lookups=0;direct=0;direct_ids=set();lookup_ids={};recoveries=[]
    for identity,value in client.items():
        peers=[v for v in counterparts.values() if v['challenge']==value['challenge']]
        assert len(peers)==1;peer=peers[0];matched.append(peer)
        assert value['tls']['tls']==peer['tls']['tls']=='TLSv1.3'
        candidates=[]
        for w in legacy:
            data={'sent':b'','received':b''}
            for op in w['operations']:data[op['direction']]+=base64.b64decode(op['bytes'],validate=True)
            sent=frames(data['sent'])
            if sent and sent[0]==value['challenge']:candidates.append(data)
        assert candidates==[peer['io']],'APPLICATION_AND_WIRE_BYTES'
        if value['intended'] is None:
            assert value['status']=='insufficient'
            outcome=peer['status']
            if outcome!='verified-no-command':
                # The server may time out before the stopped client writes
                # anything. Retain the missing client evidence as insufficient.
                assert outcome=='verified' and peer['request'] is None and peer['io']['received']==b''
                assert peer['response']['kind']=='error' and verify(server,'error',peer['response'])=={'code':'TimeoutError'}
                outcome='verified-pre-command-timeout'
            incomplete.append(dict(attempt=identity,observation='insufficient',outcome=outcome,support=peer['tail']))
            continue
        assert value['status']==peer['status']=='verified' and value['response']==peer['response']
        request=value['intended'];response=value['response'];body=verify(server,response['kind'],response)
        if response['kind']=='error':
            assert body['code'] in {'ANCHOR_RECONCILIATION_REQUIRED','ANCHOR_COMMITTED_RECOVERY_REQUIRED'}
            assert request['kind']!='lookup'
            original_id=request['body']['request_id']
            economic=[r for r in rows if json.loads(r[3])['body'].get('request')==request]
            assert len(economic)==1,'RECOVERY_ERROR_REQUIRES_ORIGINAL_COMMITTED_EVENT'
            recoveries.append(dict(attempt=identity,observation='verified-error',code=body['code'],request_id=original_id,seq=economic[0][0],outcome='verified-original-id-recovery'))
            continue
        result=body['result'] if response['kind']=='lookup-response' else body
        seq=result['anchor']['body']['seq'];row=rows[seq-1]
        assert result['ledger']==json.loads(row[3]) and result['event']==result['ledger']['body']
        verify_certificate(manifest['trust'],result['anchor'],source=cfg['source'],stream='recovery',seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
        if request['kind']=='lookup':
            assert request['body']['lookup_id']==result['event']['request']['body']['request_id'];lookups+=1
            original_id=request['body']['lookup_id'];lookup_ids.setdefault(original_id,[]).append(dict(attempt=identity,seq=seq))
        else:
            assert result['event']['request']==request;direct+=1;direct_ids.add(request['body']['request_id'])
    recovered_ids={r['request_id'] for r in recoveries}
    assert direct_ids.isdisjoint(recovered_ids) and len(direct_ids|recovered_ids)==expected_events
    assert lookups==2*expected_events+len(recoveries)
    for r in recoveries:
        matches=[v for v in lookup_ids.get(r['request_id'],[]) if v['seq']==r['seq']]
        assert len(matches)>=3,'RECOVERY_MUST_LINK_A_SIGNED_LOOKUP_AND_THE_TWO_IDEMPOTENCE_LOOKUPS'
        r['lookup_attempts']=[v['attempt'] for v in matches]
    for identity in direct_ids:assert len(lookup_ids.get(identity,[]))==2
    streams=tls_streams(directory,expected_connections=len(client))
    for row in rows[len(before):]:
        event=json.loads(row[3])['body'];argument=source_input(cfg,rows[:row[0]-1],event)
        assert any(b['phase']=='before-intent' and b['seq']==row[0] and b['event']==digest(event) and b['input']==argument and b['native']==digest(event['native']) for b in boundaries)
    return dict(attempts=len(client),direct=direct,lookups=lookups,dual_literal_replays=len(matched),tls_streams=len(streams),dispositions=incomplete,recovered=recoveries,pending=0)


def closed_replay(box):
    home=deploy.location(box);directory=home/'actual';manifest=old.old.live.public_closed(box,directory)
    cfg=manifest['mac']['service'];rows=load(directory/'events.json');argument,_,_=material_regeneration.context(cfg,rows)
    assert argument==load(directory/'source-input.json')
    expected=[json.loads(r[3])['body']['native'] for r in rows if json.loads(r[3])['body']['type'] in {'energy-regeneration','energy-material'}]
    script=ROOT/'Lean/scripts/verification/public-material-owner-source.lean';env=os.environ.copy();env['LEAN_PATH']=cfg['refeed']['lean_path'];answers={}
    for branch in ('private-one','private-two'):
        command=[cfg['refeed']['backend'][0],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',str(script),branch]
        run=subprocess.run(command,cwd=ROOT/'Lean',env=env,input=canonical(argument)+b'\n',stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=300)
        (directory/(branch+'.json')).write_bytes(run.stdout);(directory/(branch+'.stderr')).write_bytes(run.stderr)
        assert run.returncode==0 and not run.stderr,(run.returncode,run.stderr[-1500:])
        answer=json.loads(run.stdout);assert answer['output']==expected and answer['history']==20
        assert answer['nativeSlots']==12 and answer['nativeOutstanding']=='0'
        assert answer['ownFrame']==('39' if branch=='private-one' else '38');answers[branch]=answer
    assert answers['private-one']['output']==answers['private-two']['output']
    save(directory/'owner-accepted.json',dict(events=sha(directory/'events.json'),closed=sha(directory/'closed.json'),input=digest(argument),source=sha(script),
        branches={k:sha(directory/(k+'.json')) for k in answers},replies=40,frames=['39','38'],native_slots=12,native_outstanding='0'))
    print('INDEPENDENT CLOSED MATERIAL PASS: 40 exact replies; own frames39/38; original9 +new3 native slots; zero outstanding',flush=True)


def run(box,full=False,check_main=False):
    home=deploy.location(box);directory=home/'actual';manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service']
    rows=[list(r) for r in deploy.roll.spare.rows(cfg['database'])];before=load(directory/'before.json')
    assert before==load(home/'parent-rows.json') and rows[:len(before)]==before and len(rows)==53
    activated,certificate=material_extension.committed(cfg,rows);assert activated==46 and certificate==load(home/'admission.json')
    assert manifest['native_admission']==load(home/'online-before.json')['native_admission']
    historical=home.parent/'online';prior=load(historical/'final-check.json');assert prior['exit']==0 and prior['main_verified'] and prior['events']==45 and prior['head']==before[-1][2]
    commit=load(historical/'applications/integration.json')['commit']
    subprocess.run(['git','merge-base','--is-ancestor',commit,'refs/heads/main'],cwd=ROOT,check=True)
    for path,wanted in prior['inputs'].items():assert old.sha_bytes(subprocess.check_output(['git','show',commit+':'+path],cwd=ROOT))==wanted
    old_events=[json.loads(r[3])['body'] for r in before if json.loads(r[3])['body']['type']=='energy-regeneration']
    old.public_material(old_events,old.privacy.reference_groups(home.parent/'supply/production-actual.jsonl')['withhold-fuel'])
    checker=object.__new__(Store);checker.config=cfg;checker.anchor=object()
    class Signer:
        def public_key(self):return public_key(cfg['registry']['server'])
    checker.key=Signer();checker.database=sqlite3.connect(Path(cfg['database']).as_uri()+'?mode=ro',uri=True)
    try:checker.validate_ledger();checker.validate_anchor_receipts()
    finally:checker.database.close();old.old.release_readers()
    kernel=load(home/'kernel.json');assert kernel['exit']==0 and kernel['axioms']==['Classical.choice','Quot.sound','propext']
    events=[json.loads(r[3])['body'] for r in rows[activated:]];parent=json.loads(before[-1][3])['body']['native']['next']
    result=material(parent,events);negative=[]
    for label in ('invent-feed','free-recycling','erase-debt','repeat-worker-payment','private-disclosure'):
        changed=deepcopy(events)
        if label=='invent-feed':next(x for x in changed[-1]['native']['next']['stock'] if x[:2]==['audit:0','feed'])[2]='99'
        elif label=='free-recycling':next(x for e in changed for x in e['native']['rows'] if x['accepted'] and x['request']['operation']==dict(kind='produce',actor='provider:2'))['debit']=[]
        elif label=='erase-debt':next(x for x in changed[3]['native']['next']['claims'] if x[:3]==['delivery','provider:0','audit:3'])[3]='0'
        elif label=='repeat-worker-payment':
            changed[4]['native']['rows'][0]=deepcopy(changed[3]['native']['rows'][3]);changed[4]['native']['rows'][0]['index']=0
        else:changed[-1]['native']['next']['stock'].append(['audit:3','feed','39'])
        try:material(parent,changed)
        except (AssertionError,KeyError):negative.append(label)
        else:raise AssertionError('MATERIAL_MUTATION_ACCEPTED:'+label)
    for label,change in [('parent',lambda c:c['point'].update(parent='0'*64)),('missing-vote',lambda c:c['votes'].pop()),('descriptor',lambda c:c['point']['descriptor'].update(exporter_sha256='0'*64))]:
        changed=deepcopy(certificate);change(changed)
        try:material_extension.admission(cfg,changed)
        except (ValueError,InvalidSignature):negative.append(label)
        else:raise AssertionError('MATERIAL_ADMISSION_MUTATION_ACCEPTED')
    transport=wire(box,manifest,home,rows,before)
    accepted=load(directory/'owner-accepted.json');assert accepted['events']==sha(directory/'events.json') and accepted['closed']==sha(directory/'closed.json')
    assert accepted['source']==sha(ROOT/'Lean/scripts/verification/public-material-owner-source.lean')
    for branch,wanted in accepted['branches'].items():assert wanted==sha(directory/(branch+'.json'))
    counts=old.replicas(box,manifest,rows,home,'refeed');old.current_runtime(box,manifest,rows,home)
    application=module('historical_application','public-application-check.py').check(box,check_main)
    if full:
        audit=subprocess.run([sys.executable,str(ROOT/'.agents/tmp/public-autonomous-origin-20261101/final-audit/verify.py')],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (home/'full-cost.log').write_text(audit.stdout);assert audit.returncode==0,audit.stdout[-1600:];print(audit.stdout,end='',flush=True)
    compiled=load(home/'compiled.json');inputs={}
    for name,wanted in compiled['sources'].items():
        path='Lean/'+name.replace('.','/')+'.lean';assert sha(ROOT/path)==wanted;inputs[path]=wanted
    files=[Path(__file__),*[Path(__file__).with_name('public-material-'+n) for n in ('deploy.py','actual.py','network-source.lean','owner-source.lean')],
        *[Path(__file__).with_name(n) for n in ('public-ha-check.py','public-supply-check.py','public-supply-actual.py','public-application-check.py')],*[NETWORK/n for n in manifest['protocol']]]
    proof=ROOT/'Lean/SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Regeneration/Supply/Material/Refeed/Consumption.lean'
    assert sha(proof)==kernel['consumption_source'];files.append(proof)
    inputs.update({str(p.relative_to(ROOT)):sha(p) for p in files})
    if check_main:
        for path,wanted in inputs.items():assert old.sha_bytes(subprocess.check_output(['git','show','refs/heads/main:'+path],cwd=ROOT))==wanted,('MAIN_SOURCE_CHANGED',path)
    assert [list(r) for r in deploy.roll.spare.rows(cfg['database'])]==rows
    report=dict(exit=0,events=len(rows),head=rows[-1][2],original_events=45,material=result,wire=transport,replicas=counts,
                kernel=kernel,application_receipts=application,negative_controls=negative,inputs=inputs,full=full,main_verified=check_main)
    save(home/'final-check.json',report)
    print('INDEPENDENT MATERIAL AUDIT PASS '+json.dumps({k:report[k] for k in ('events','material','wire','replicas','main_verified')},sort_keys=True),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--full',action='store_true');p.add_argument('--check-main',action='store_true');p.add_argument('--closed',action='store_true');a=p.parse_args()
    if a.closed:closed_replay(a.box.resolve())
    else:run(a.box.resolve(),a.full,a.check_main)
