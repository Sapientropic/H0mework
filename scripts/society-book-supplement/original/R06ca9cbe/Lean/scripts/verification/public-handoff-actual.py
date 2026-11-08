"""Append and recover original signed different-auditor handoff requests."""
import argparse
import importlib.util
import json
from pathlib import Path
import secrets
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from client import check_result
from crypto import app_private,connect,digest,peer,receive,send,sign,verify
from ha_quorum import Quorum
from recovery_loop import save
import continuation
import handoff
import energy
import governance
spec=importlib.util.spec_from_file_location('continuation_transport',Path(__file__).with_name('public-continuation-actual.py'))
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
transport=old.transport
load=old.load
rows=old.rows


def authorize(box,cfg,prefix,op,query,case,tag,actor):
    manifest=load(box/'ha/deployment.json')
    _,scope,current=handoff.context(cfg,prefix)
    entry=governance.registered(prefix)[0]
    body=dict(source=cfg['source'],stream='recovery',parent=dict(seq=len(prefix),head=prefix[-1][2]),
              member=governance.member(cfg,prefix,actor),executor=entry['result']['key'],
              cut=current['cut'],epoch=current['version'],op=op,query=query,unit='energy',scope=scope,actor=actor)
    wanted=handoff.authorization(cfg,body)
    path=case/(tag+'-owner.json')
    if path.exists():
        proof=load(path)
        assert proof['body']==wanted,'recover the original authorization without replacing its parent'
    else:
        who=entry['proof']['body']['owner']
        if who=='mac':proof=sign(app_private(Path(cfg['ha']['owner_profile'])),'native-energy-handoff',wanted)
        else:
            item=manifest['nodes']['c']
            code=f"import json,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom crypto import app_private,sign\nprint(json.dumps(sign(app_private(Path({item['home']+'/ha/owner'!r})),'native-energy-handoff',{wanted!r})))"
            proof=json.loads(transport.remote('c',code,python=item['python']))
        save(path,proof)
    body['execution']=proof
    return body


def leader(box,manifest):
    item=manifest['nodes']['c']
    values=[('mac',load(box/'runtime/ha-status.json')),
            ('spark',json.loads(transport.remote('c',f"from pathlib import Path\nprint(Path({item['home']+'/ha/runtime/ha-status.json'!r}).read_text())",python=item['python'])))]
    states=[(name,verify(public_key(manifest['owners'][name]),'ha-coordinator',value)) for name,value in values]
    live=[(name,state) for name,state in states if state['phase']=='leader' and time.time()-state['at']<15]
    assert len(live)==1,[(n,s['phase'],s['error']) for n,s in states]
    owner,state=live[0]
    return load(box/'ha/addresses.json')['a' if owner=='mac' else 'c']


def exchange(box,cfg,case,tag,actor,op,query):
    manifest=load(box/'ha/deployment.json');original=load(box/'service.json')
    profile=Path(original['pki'])/('auditor'+actor);request_path=case/(tag+'-request.json')
    retry=False
    with connect(profile,original['port'],host=leader(box,manifest),hostname='audit.local') as connection:
        assert peer(connection)[0]=='urn:public-audit:server'
        key=peer(connection)[2];challenge=receive(connection);challenge_body=verify(key,'challenge',challenge)
        if request_path.exists():
            message=load(request_path)
            lookup=sign(app_private(profile),'lookup',{**challenge_body,'request_id':secrets.token_hex(16),
                                                      'lookup_id':message['body']['request_id']})
            send(connection,lookup);reply=receive(connection);save(case/(tag+'-lookup.json'),reply)
            if reply['kind']=='error':
                code=verify(key,'error',reply)['code'];prior_path=case/(tag+'-response.json')
                prior=load(prior_path) if prior_path.exists() else None
                # Only an authenticated rejection before BEGIN/stage may refresh
                # its envelope. Unknown outcomes keep the exact original intent.
                if (code=='REQUEST_NOT_COMMITTED' and prior and prior['kind']=='error' and
                        verify(public_key(cfg['registry']['server']),'error',prior)['code'] in
                        {'CHALLENGE_BINDING','CHALLENGE_EXPIRED'}):
                    identity=message['body']['request_id']
                    save(case/(tag+'-request-id.json'),{'request_id':identity,'reason':'authenticated pre-stage rejection and original lookup not committed'})
                    for suffix in ('request','owner','response'):
                        path=case/(tag+'-'+suffix+'.json')
                        if path.exists():
                            value=load(path);path.rename(case/(tag+'-rejected-'+suffix+'-'+digest(value)+'.json'))
                    retry=True
                else:raise ValueError(code)
            else:
                envelope=verify(key,'lookup-response',reply);assert envelope['request']==digest(lookup)
                result=envelope['result'];recovered=True
                prefix=rows(original)[:result['anchor']['body']['seq']-1]
        else:
            end=time.monotonic()+10
            while True:
                prefix=rows(original);_,_,current=handoff.context(cfg,prefix)
                if (current['cut'],current['version'])==(challenge_body['cut'],challenge_body['epoch']):break
                if time.monotonic()>end:raise TimeoutError('local signed prefix has not reached the issuer challenge; request not submitted')
                time.sleep(.1)
            body=authorize(box,cfg,prefix,op,query,case,tag,actor)
            identity_path=case/(tag+'-request-id.json')
            identity=load(identity_path)['request_id'] if identity_path.exists() else secrets.token_hex(16)
            message=sign(app_private(profile),handoff.KIND,{**challenge_body,**body,'request_id':identity})
            save(request_path,message);send(connection,message);reply=receive(connection);save(case/(tag+'-response.json'),reply)
            if reply['kind']=='error':raise ValueError(verify(key,'error',reply)['code'])
            result=verify(key,'response',reply);recovered=False
        if not retry:
            checked=check_result(result,message,key,profile,expected_stream='recovery',recovered=recovered,native_config=cfg,prefix=prefix)
            save(case/(tag+'-result.json'),checked)
            return checked
    return exchange(box,cfg,case,tag,actor,op,query)


def run(box):
    cfg=load(box/'ha/deployment.json')['mac']['service'];original=load(box/'service.json')
    case=box/'ha/handoff/actual-01';case.mkdir(mode=0o700,exist_ok=True)
    prefix=rows(original)
    if not (case/'before.json').exists():
        assert len(prefix)==24;save(case/'before.json',{'rows':prefix,'at':time.time()})
    assert prefix[:24]==[tuple(r) for r in load(case/'before.json')['rows']]
    schedule=[('replace','2','replace',dict(slots=63,fields=3)),
              ('old-denied','1','read',dict(slots=1,fields=3)),('new-unfunded','2','read',dict(slots=1,fields=3))]
    results=[]
    for tag,actor,op,query in schedule:
        result=exchange(box,cfg,case,tag,actor,op,query);results.append(result);native=result['event']['native']
        print('ACTUAL '+tag+': seq='+str(result['anchor']['body']['seq'])+' clock='+native['next']['clock']+
              ' holder='+str(native['next']['holder'])+' reason='+native['reason']+' energy='+str(native['next']['energy']),flush=True)
    first=results[0]['event']['native']
    assert first['before']['clock']=='36' and first['next']['clock']=='37'
    assert first['next']['energy']==['0']*4 and first['next']['holder']==2 and first['next']['version']==14
    assert len(first['rows'])==7 and all(row['accepted'] for row in first['rows'])
    assert results[1]['event']['native']['reason']=='UNAUTHORIZED'
    assert results[2]['event']['native']['reason']=='UNFUNDED'
    for (tag,actor,op,query),result in zip(schedule,results):
        assert exchange(box,cfg,case,tag,actor,op,query)['ledger']==result['ledger']
    q=Quorum(cfg);end=time.monotonic()+90
    while time.monotonic()<end:
        states=q.collect('status');after=rows(original)
        if len(after)==27 and set(states)==set('abcd') and all(state['head']['seq']==27 for state in states.values()):break
        time.sleep(.3)
    else:raise TimeoutError('handoff not yet reconciled across the original four journals')
    save(case/'after.json',{'rows':after,'states':states,'at':time.time()})
    save(box/'ha/handoff/actual.json',{'case':'actual-01','events':27,'head':after[-1][2],
                                    'tags':[row[0] for row in schedule]})
    print('LIVE DISTINCT AUDITOR HANDOFF PASS: original24; source-selected2; exact deficit transfers1+2; paid revoke/proposal/acceptance/query/delivery5; old1 signed refusal; new2 signed unfunded; four anchors27; three lookups without duplicate payment',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);a=p.parse_args()
    try:run(a.box.resolve())
    finally:governance.close_readers();energy.close_readers()
