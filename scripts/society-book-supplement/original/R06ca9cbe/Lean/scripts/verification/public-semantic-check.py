"""Read-only consumer of actual pre-vote comparisons and canonical source continuation."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import ledger_hash,public_key
from crypto import canonical,digest,verify
from ha_anchor import verify_quorum
from ha_quorum import Quorum
from recovery_loop import birth,boot_identity,save
from verify import verify_disclosure

spec=importlib.util.spec_from_file_location('semantic_audit_base',Path(__file__).with_name('public-ha-check.py'))
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
require=base.require;load=base.load


def rpc(config,member,value):
    request=verify(base.rpc_key(config,member),'anchor-request',value['request'])
    response=verify(public_key(config['anchors']['trust']['members'][member]),'anchor-response',value['response'])
    require(response['request']==digest(value['request']) and response['nonce']==request['nonce'],'semantic RPC freshness/binding differs')
    return request,response


def dispositions(box,manifest,config,literal,current,attack):
    home=box/'ha/semantic/orphan-01';before=load(home/'before.json');after=load(home/'after.json')
    owner=public_key(manifest['owners']['spark']);server=public_key(config['registry']['server'])
    old=verify(owner,'ha-coordinator',before['source']['coordinator']);new=verify(owner,'ha-coordinator',after['source']['coordinator'])
    ready=verify(server,'ha-service-ready',before['source']['ready']);renewed=verify(server,'ha-service-ready',after['source']['ready'])
    injection=load(home/'injection.json')
    require(all(old[k]==new[k] for k in ('pid','birth','boot')) and old['grant']['point']==new['grant']['point'] and
            old['head']['seq']==new['head']['seq']==13 and old['phase']==new['phase']=='leader' and
            injection=={**ready['backend'],'boot':ready['boot'],'pgid':old['service']['pgid']} and
            renewed['backend']['pid']!=ready['backend']['pid'],'default same-owner recovery did not rebuild the exact failed source worker')
    require(set(before['anchors'])==set(after['anchors'])==set('abcd') and
            all(v['head']['seq']==13 for v in before['anchors'].values()) and
            before['anchors']['d']['intents']==[{'seq':14,'previous':literal[12][2],'message':before['message']}] and
            all(v['head']['seq']==13 and not v['intents'] for v in after['anchors'].values()),'default recovery lost, committed or retained the false minority intent')
    invalid=before['message'];verify(server,'ledger',invalid);expected=json.loads(literal[13][3])['body']['record']
    require(invalid!=attack['message'],'the failed first attempt was overwritten by the successful attack')
    def comparison(votes,message):
        members=[v['member'] for v in votes]
        require(members==sorted(set(members)) and 3<=len(members)<=4,'rejection comparison duplicated/omitted a member')
        for vote in votes:
            value=verify(public_key(manifest['trust']['members'][vote['member']]),'source-semantic-decision',vote['receipt'])
            require(value=={'classification':'invalid','source':config['source'],'stream':'recovery',
                'prefix':{'seq':13,'head':literal[12][2]},'event':digest(message),'expected':expected,
                'actual':message['body']['record'],'descriptor':manifest['semantic']['descriptor']},'persisted rejection did not compare this original source/prefix/message')
    rejected={};superseded={}
    for member,snapshot in current.items():
        key=public_key(manifest['trust']['members'][member])
        for seq,previous,head,text in snapshot['intents']:
            require(seq<=len(literal) and (previous,head,text)==literal[seq-1][1:],'unresolved or silently hidden false intent remains in the database')
        require(len(snapshot['rejected'])==1,'exact rejected proposal inventory differs')
        for seq,head,text,proof in snapshot['rejected']:
            message=json.loads(text);value=verify(key,'ha-intent-rejection',json.loads(proof))
            require(seq==14 and message==invalid and head==ledger_hash(literal[12][2],invalid) and
                    all(value[k]==v for k,v in dict(source=config['source'],stream='recovery',seq=14,
                    previous=literal[12][2],head=head,message=digest(message),disposition='source-invalid').items()),'rejected intent was deleted without its exact durable disposition')
            comparison(value['comparison']['votes'],message);rejected[member]=digest(json.loads(proof))
        require(len(snapshot['superseded'])==(1 if member=='d' else 0),'minority supersession inventory differs')
        for seq,head,text,proof in snapshot['superseded']:
            value=verify(key,'ha-intent-supersession',json.loads(proof));message=json.loads(text);canonical_event=json.loads(literal[13][3])
            require(seq==14 and message==attack['message']==value['message'] and
                    head==value['head']==ledger_hash(literal[12][2],message) and
                    value['committed']==canonical_event and value['previous']==literal[12][2] and
                    value['source']==config['source'] and value['stream']=='recovery','canonical commit lost the minority proposal or substituted its effect')
            point=dict(token=value['grant']['point'],seq=14,previous=literal[12][2],head=literal[13][2],
                message=digest(canonical_event),operation_id=canonical_event['body']['request']['body']['request_id'])
            verify_quorum({'ha':{'trust':manifest['trust']}},value['grant'],'ha-grant',value['grant']['point'])
            verify_quorum({'ha':{'trust':manifest['trust']}},value['intent'],'ha-intent',point)
            base.original_check.certificate(config,load(box/'ha/semantic'/load(box/'ha/semantic/actual.json')['case']/'correct-result.json')['anchor'],
                                             base.original_check.point(config,literal[13]))
            require(verify(key,'anchor-commit',value['receipt'])==base.original_check.point(config,literal[13]),'supersession lacks the actual canonical commit')
            superseded[member]=digest(json.loads(proof))
    print('INDEPENDENT DEFAULT RECOVERY PASS: exact executor rebuilt; source13/payment unchanged; 4 durable three-comparison rejections; minority supersession preserved; no hidden false intent',flush=True)
    return {'rejected':rejected,'superseded':superseded}


def check(box,manifest,config,literal,current):
    home=box/'ha/semantic';case=home/load(home/'actual.json')['case'];old=load(home/'baseline.json');before=load(case/'before.json')
    require(len(literal)>=14 and literal[:13]==[tuple(r) for r in old['rows']]==[tuple(r) for r in before['rows']],
            'semantic gate changed the paid thirteen-event prefix')
    require(old['final']['exit']==0 and old['final']['source_events']==13,'missing original independent thirteen-event acceptance')
    controls=load(Path(manifest['semantic'].get('controls',box.parent/'semantic-local-10/acceptance.json')))
    expected_controls=16 if manifest.get('energy') else 14
    require(len(controls['tests'])==expected_controls and controls['descriptor']==manifest['semantic']['descriptor'],'semantic positive/negative controls differ')
    require(controls['inputs']=={name:base.sha(ROOT/name) for name in controls['inputs']},'semantic control source bytes changed')
    attack=load(case/'attack.json');server=public_key(config['registry']['server']);bad=verify(server,'ledger',attack['message'])
    request=verify(public_key(config['registry']['auditor2']),'audit',attack['request'])
    challenge=verify(server,'challenge',attack['challenge'])
    require(bad['request']==attack['request'] and request['query']==bad['record']['query'] and
            all(request[k]==v for k,v in challenge.items()) and request['actor']=='2' and request['source']==config['source'] and
            bad['stream']==request['stream']=='recovery','false proposal was not the original actor/connection request')
    require(verify_disclosure(bad['record'])['access']=='admitted','negative control was not schema-valid')
    correct=verify(server,'ledger',json.loads(literal[13][3]));expected=correct['record']
    require(correct['request']==attack['request'] and expected==before['expected'] and expected!=bad['record'] and
            expected['access']=='unfunded' and expected['labor']=='0','canonical source did not process the same actual request accurately')
    require(verify(server,'response',load(case/'source-response.json'))['ledger']==json.loads(literal[13][3]),'actual source response differs')
    require(load(case/'correct-result.json')['ledger']==json.loads(literal[13][3]) and
            [tuple(r) for r in load(case/'after.json')['rows']]==literal[:14],'actual source endpoint/rows differ')
    native=before['native_members'];refusals=load(case/'refusals.json');votes=[]
    require(native==''.join(sorted(set(native))) and set(native)<=set('abcd') and len(set(native))>=3 and
            set(refusals)==set('abcd'),'semantic quorum coverage differs')
    for member,proof in refusals.items():
        body,response=rpc(config,member,proof['refusal']);identity=public_key(manifest['trust']['members'][member])
        require(body['op']=='ha-stage' and body['message']==attack['message'] and body['seq']==14 and
                body['previous']==literal[12][2] and body['head']==ledger_hash(literal[12][2],attack['message']),
                'actual false proposal binding differs: '+member)
        point={k:body[k] for k in ('epoch','owner','lease_id')}|{'source':config['source'],'stream':'recovery','cluster':digest(manifest['trust'])}
        verify_quorum({'ha':{'trust':manifest['trust']}},body['grant'],'ha-grant',point)
        owner_body={k:v for k,v in body.items() if k!='owner_proof'}
        require(verify(public_key(manifest['owners'][body['owner']]),'ha-owner-request',body['owner_proof'])=={'request':digest(owner_body)},'attack lacked the actual owner key')
        _,state=rpc(config,member,proof['after']);state=state['result']
        require(state['head']['seq']==13,'false result advanced a physical anchor')
        if member in native:
            require(response.get('error')=='SEMANTIC_VIOLATION' and not state['intents'] and proof['vote'] is None,'false result received a source-gated vote')
            decision=verify(identity,'source-semantic-decision',proof['decision'])
            require(decision=={'classification':'invalid','source':config['source'],'stream':'recovery',
                    'prefix':{'seq':13,'head':literal[12][2]},'event':digest(attack['message']),
                    'expected':expected,'actual':bad['record'],'descriptor':manifest['semantic']['descriptor']},'false-result comparison was not exact canonical source output')
        else:
            vote=verify(identity,'ha-intent',proof['vote']);votes.append(member)
            require(response['result']==proof['vote'] and vote['point']==dict(token=point,seq=14,previous=body['previous'],head=body['head'],
                    message=digest(attack['message']),operation_id=request['request_id']) and
                    state['intents']==[{'seq':14,'previous':body['previous'],'message':attack['message']}],
                    'old signature-only control did not sign the same false proposal')
    require(len(votes)<3,'false result acquired a quorum')
    print('INDEPENDENT PRE-VOTE PASS: valid actor/writer/owner signatures; exact false-result mismatch; '+str(len(votes))+'/3 votes cannot commit; canonical same-request event14',flush=True)
    disposition=dispositions(box,manifest,config,literal,current,attack)
    q=Quorum(manifest['mac']['service']);runtime={};installed=manifest['semantic']['native_members']
    require(installed==''.join(sorted(set(installed))) and set(installed)<=set('abcd') and set(native)<=set(installed),
            'installed source gate coverage regressed')
    if manifest.get('native_admission'):
        checker = base.module('native_spare_independent', 'public-native-spare-check.py')
        cases = checker.actual(box)
        audited = checker.runtime(box, manifest)
        return {'native_members': installed, 'attack_native_members': native, 'old_control_votes': votes,
                'events': len(literal), 'head': literal[-1][2], 'dispositions': disposition,
                'admission': audited, 'physical_spare_cases': cases}
    for member in installed:
        client=q.nodes[member];state=client.call('semantic-status')
        require(state['descriptor']==manifest['semantic']['descriptor'] and state['backend'] and
                state['prefix']['seq'] in range(13,len(literal)+1) and
                state['prefix']['head']==literal[state['prefix']['seq']-1][2],'native checker lost original prefix')
        cfg=manifest['semantic']['configurations'][member];worker=state['backend']
        code=f'''import hashlib,json,os,subprocess
from pathlib import Path
import sys
sys.path.insert(0,NETWORK)
from recovery_loop import birth,boot_identity
c={cfg!r};w={worker!r};inventory=json.loads(Path(c['closure']).read_text())
assert w['boot']==boot_identity() and w['birth']==birth(w['pid']) and os.getpgid(w['pid'])==w['pgid']==w['pid']
assert hashlib.sha256(Path(c['closure']).read_bytes()).hexdigest()==c['descriptor']['closure_sha256']
assert all(hashlib.sha256((Path(c['lean_path'])/n).read_bytes()).hexdigest()==wanted for n,wanted in inventory.items())
assert hashlib.sha256(Path(c['exporter']).read_bytes()).hexdigest()==c['descriptor']['exporter_sha256']
assert subprocess.check_output([c['backend'][0],'--githash'],text=True).strip()==c['descriptor']['compiler']
assert c['backend'][1:]==['--trust=0','-j1','--run',c['exporter'],'private-one']
argv=subprocess.check_output(['ps','-ww','-p',str(w['pid']),'-o','command='],text=True).strip()
import shlex
assert shlex.split(argv)==c['backend'],argv
print(json.dumps({{'files':len(inventory),'backend':w,'command':argv,'complete':True}}))
'''
        if member=='a':
            code=code.replace('NETWORK',repr(str(NETWORK)))
            value=json.loads(subprocess.check_output([sys.executable,'-c',code],text=True,cwd=ROOT))
            anchor_cfg=load(box/'local-anchor/config.json');coordinator=base.status(manifest,'mac',load(box/'runtime/ha-status.json'))
            require(coordinator['configuration']==digest(manifest['mac']['controller']),'Mac controller configuration differs')
            anchor_process=coordinator['members']['a'];entrypoint=str(NETWORK/'semantic_anchor.py')
            require(base.sha(Path(anchor_process['argv'][1]))==manifest['protocol']['semantic_anchor.py'],'Mac actual gate bytes differ')
        else:
            item=manifest['nodes'][member];code=code.replace('NETWORK',repr(item['code']))
            value=json.loads(base.transport.remote(member,code,timeout=60,python=item['python']))
            anchor_cfg=current[member]['config'];host=verify(public_key(manifest['trust']['members'][member]),'recovery-host-status',current[member]['status'])
            require(host['entrypoint']=='semantic_anchor.py','native manager selected another anchor entrypoint')
            anchor_process=host['process'];entrypoint=item['code']+'/semantic_anchor.py'
        require(value['complete'] and value['files']==5206 and anchor_cfg['semantic']==cfg and
                anchor_cfg['anchor_entrypoint']=='semantic_anchor.py' and anchor_process['argv'][1]==entrypoint and
                anchor_process['argv'][2]==(str(box/'local-anchor/config.json') if member=='a' else manifest['nodes'][member]['home']+'/config.json'),
                'native source checker was not installed in the actual voting process')
        runtime[member]={'state':state,'native':value}
    save(home/'current-independent.json',runtime)
    print('INDEPENDENT NATIVE GATES PASS: '+installed+'; exact 5206 artifacts, compiler/exporter/argv, live private workers and original signing processes',flush=True)
    return {'native_members':installed,'attack_native_members':native,'old_control_votes':votes,'events':len(literal),'head':literal[-1][2],
            'dispositions':disposition}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path);args=parser.parse_args()
    base.run(args.box.resolve(),False,False)
