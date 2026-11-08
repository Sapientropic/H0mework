"""Commit supplier funding and a new energy-priced audit epoch on the original journal."""
import argparse
import importlib.util
import json
from pathlib import Path
import secrets
import sqlite3
import sys
import time

ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from client import check_result
from crypto import app_private,connect,digest,peer,receive,send,sign,verify
import governance
import energy
from ha_quorum import Quorum
from recovery_loop import save
spec=importlib.util.spec_from_file_location('governance_actual_transport',Path(__file__).with_name('public-ha-deploy.py'))
transport=importlib.util.module_from_spec(spec);spec.loader.exec_module(transport)


def load(path):return json.loads(path.read_text())
def rows(config):
    with sqlite3.connect(Path(config['database']).as_uri()+'?mode=ro',uri=True) as db:return governance.rows_of(db)


def authorize(box,cfg,prefix):
    manifest=load(box/'ha/deployment.json');case=box/'ha/energy/actual-01'
    case.mkdir(mode=0o700,exist_ok=True)
    assert len(prefix)==16
    parent={'seq':16,'head':prefix[-1][2]};origin=governance.member(cfg,prefix,'1')
    entry=governance.registered(prefix)[0];executor=entry['result']['key'];who=entry['proof']['body']['owner']
    body=dict(source=cfg['source'],stream='recovery',parent=parent,executor=executor,
              member=origin,candidate=1,unit='energy',cut=22,epoch=6,query={'slots':63,'fields':3},
              scope=energy.scope_id(cfg,parent,1))
    path=case/'owner-proof.json'
    if path.exists():
        proof=load(path)
        if proof['body']==body:
            assert verify(public_key(manifest['owners'][who]),'native-energy-renewal',proof)==body
            return proof
        assert not (case/'renewal-request.json').exists(),'an already submitted request must be recovered unchanged'
        save(case/('superseded-authorization-'+digest(proof)+'.json'),proof)
    if who=='mac':proof=sign(app_private(Path(cfg['ha']['owner_profile'])),'native-energy-renewal',body)
    else:
        item=manifest['nodes']['c']
        code=f"import json,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom crypto import app_private,sign\nprint(json.dumps(sign(app_private(Path({item['home']+'/ha/owner'!r})),'native-energy-renewal',{body!r})))"
        proof=json.loads(transport.remote('c',code,python=item['python']))
    assert verify(public_key(manifest['owners'][who]),'native-energy-renewal',proof)==body
    save(path,proof);return proof


def run(box):
    case=box/'ha/energy/actual-01';case.mkdir(mode=0o700,exist_ok=True)
    manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service'];original=load(box/'service.json')
    before=rows(original)
    if not (case/'before.json').exists():
        assert len(before)==16;save(case/'before.json',{'rows':before,'at':time.time()})
    else:assert before[:16]==[tuple(r) for r in load(case/'before.json')['rows']]
    def leader():
        mac=load(box/'runtime/ha-status.json');item=manifest['nodes']['c']
        spark=json.loads(transport.remote('c',f"from pathlib import Path\nprint(Path({item['home']+'/ha/runtime/ha-status.json'!r}).read_text())",python=item['python']))
        states=[(name,verify(public_key(manifest['owners'][name]),'ha-coordinator',value)) for name,value in [('mac',mac),('spark',spark)]]
        candidates=[(name,state) for name,state in states if state['phase']=='leader' and time.time()-state['at']<15]
        assert len(candidates)==1,[(name,state['phase'],state['error']) for name,state in states]
        owner,state=candidates[0];return owner,load(box/'ha/addresses.json')['a' if owner=='mac' else 'c']
    def exchange(tag,actor,make):
        owner,host=leader();profile=Path(original['pki'])/('auditor'+actor)
        prefix=rows(original)
        with connect(profile,original['port'],host=host,hostname='audit.local') as connection:
            assert peer(connection)[0]=='urn:public-audit:server';key=peer(connection)[2]
            challenge=receive(connection);body=verify(key,'challenge',challenge)
            request_path=case/(tag+'-request.json')
            if request_path.exists():
                old=load(request_path);message=sign(app_private(profile),'lookup',{**body,'request_id':secrets.token_hex(16),'lookup_id':old['body']['request_id']})
                send(connection,message);reply=receive(connection);save(case/(tag+'-lookup.json'),reply)
                envelope=verify(key,'lookup-response',reply);assert envelope['request']==digest(message)
                result=envelope['result'];message=old;recovered=True
                prefix=prefix[:result['anchor']['body']['seq']-1]
            else:
                kind,extra=make(owner,body,prefix)
                message=sign(app_private(profile),kind,{**body,'request_id':secrets.token_hex(16),**extra})
                save(request_path,message);send(connection,message)
                reply=receive(connection);save(case/(tag+'-response.json'),reply)
                if reply['kind']=='error':raise ValueError(reply['body']['code'])
                result=verify(key,'response',reply);recovered=False
            checked=check_result(result,message,key,profile,expected_stream='recovery',recovered=recovered,native_config=cfg,prefix=prefix)
            save(case/(tag+'-result.json'),checked);return checked
    def renewal(owner,challenge,prefix):
        assert len(prefix)==16 and (challenge['cut'],challenge['epoch'])==(22,6)
        parent={'seq':16,'head':prefix[-1][2]};origin=governance.member(cfg,prefix,'1')
        entry=governance.registered(prefix)[0];executor=entry['result']['key']
        executor_owner=entry['proof']['body']['owner'];query={'slots':63,'fields':3}
        scope=energy.scope_id(cfg,parent,1)
        proof=authorize(box,cfg,prefix)
        return 'energy-renewal',dict(parent=parent,member=origin,executor=executor,execution=proof,
                                     candidate=1,unit='energy',query=query)
    first=exchange('renewal','1',renewal)
    assert first['anchor']['body']['seq']==17
    assert first['event']['native']['epoch']['next']['energy']==['8','1','0','6']
    def audit(owner,challenge,prefix):
        assert len(prefix)==17 and (challenge['cut'],challenge['epoch'])==(25,8)
        return 'energy-audit',dict(parent={'seq':17,'head':prefix[-1][2]},scope=first['event']['scope'],
                                    unit='energy',query={'slots':1,'fields':3})
    second=exchange('audit','1',audit)
    assert second['anchor']['body']['seq']==18
    assert second['event']['native']['epoch']['next']['energy']==['7','0','0','6']
    assert exchange('renewal','1',renewal)['ledger']==first['ledger']
    assert exchange('audit','1',audit)['ledger']==second['ledger']
    q=Quorum(cfg);end=time.monotonic()+60
    while time.monotonic()<end:
        states=q.collect('status');after=rows(original)
        if len(after)==18 and set(states)==set('abcd') and all(s['head']['seq']==18 for s in states.values()):break
        time.sleep(.3)
    else:raise TimeoutError('energy epoch not yet reconciled across four original journals')
    save(case/'after.json',{'rows':after,'states':states,'at':time.time()})
    save(box/'ha/energy/actual.json',{'case':'actual-01','events':18,'renewal':17,'audit':18,'head':after[-1][2]})
    print('LIVE ENERGY EPOCH PASS: original16 preserved; supplier energy6; application1 + authorization2 + queries/deliveries4; four anchors18; labor remains0; original deadline22',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);a=p.parse_args()
    try:run(a.box.resolve())
    finally:governance.close_readers();energy.close_readers()
