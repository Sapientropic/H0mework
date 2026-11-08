"""Append and recover original signed recursive supply/window requests."""
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
import energy
import governance
spec=importlib.util.spec_from_file_location('continuation_transport',Path(__file__).with_name('public-energy-actual.py'))
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
transport=old.transport
load=old.load
rows=old.rows


def authorize(box,cfg,prefix,op,query,case,tag):
    manifest=load(box/'ha/deployment.json')
    _,_,scope,current=continuation.context(cfg,prefix)
    entry=governance.registered(prefix)[0]
    body=dict(source=cfg['source'],stream='recovery',parent=dict(seq=len(prefix),head=prefix[-1][2]),
              member=governance.member(cfg,prefix,'1'),executor=entry['result']['key'],
              cut=current['cut'],epoch=current['version'],op=op,query=query,unit='energy',scope=scope,actor='1')
    wanted=continuation.authorization(cfg,body,scope)
    path=case/(tag+'-owner.json')
    if path.exists():
        proof=load(path)
        assert proof['body']==wanted,'recover the original authorization without replacing its parent'
    else:
        who=entry['proof']['body']['owner']
        if who=='mac':proof=sign(app_private(Path(cfg['ha']['owner_profile'])),'native-energy-continuation',wanted)
        else:
            item=manifest['nodes']['c']
            code=f"import json,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom crypto import app_private,sign\nprint(json.dumps(sign(app_private(Path({item['home']+'/ha/owner'!r})),'native-energy-continuation',{wanted!r})))"
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


def exchange(box,cfg,case,tag,op,query):
    manifest=load(box/'ha/deployment.json');original=load(box/'service.json')
    prefix=rows(original);profile=Path(original['pki'])/'auditor1'
    request_path=case/(tag+'-request.json')
    with connect(profile,original['port'],host=leader(box,manifest),hostname='audit.local') as connection:
        assert peer(connection)[0]=='urn:public-audit:server'
        key=peer(connection)[2];challenge=receive(connection);challenge_body=verify(key,'challenge',challenge)
        if request_path.exists():
            message=load(request_path)
            lookup=sign(app_private(profile),'lookup',{**challenge_body,'request_id':secrets.token_hex(16),
                                                      'lookup_id':message['body']['request_id']})
            send(connection,lookup);reply=receive(connection);save(case/(tag+'-lookup.json'),reply)
            if reply['kind']=='error':raise ValueError(reply['body']['code'])
            envelope=verify(key,'lookup-response',reply);assert envelope['request']==digest(lookup)
            result=envelope['result'];recovered=True
            prefix=prefix[:result['anchor']['body']['seq']-1]
        else:
            body=authorize(box,cfg,prefix,op,query,case,tag)
            message=sign(app_private(profile),continuation.KIND,{**challenge_body,**body,'request_id':secrets.token_hex(16)})
            save(request_path,message);send(connection,message);reply=receive(connection);save(case/(tag+'-response.json'),reply)
            if reply['kind']=='error':raise ValueError(reply['body']['code'])
            result=verify(key,'response',reply);recovered=False
        checked=check_result(result,message,key,profile,expected_stream='recovery',recovered=recovered,native_config=cfg,prefix=prefix)
        save(case/(tag+'-result.json'),checked)
        return checked


def run(box):
    cfg=load(box/'ha/deployment.json')['mac']['service'];original=load(box/'service.json')
    case=box/'ha/continuation/actual-01';case.mkdir(mode=0o700,exist_ok=True)
    prefix=rows(original)
    if not (case/'before.json').exists():
        assert len(prefix)==18;save(case/'before.json',{'rows':prefix,'at':time.time()})
    assert prefix[:18]==[tuple(r) for r in load(case/'before.json')['rows']]
    schedule=[('repair','repair'),('revoke','revoke'),('early-open','open'),('deadline-open','open'),
              ('reopen','open'),('new-grant','grant')]
    results=[]
    for tag,op in schedule:
        result=exchange(box,cfg,case,tag,op,dict(slots=1,fields=3));results.append(result)
        native=result['event']['native']
        print('ACTUAL '+tag+': seq='+str(result['anchor']['body']['seq'])+' clock='+native['next']['clock']+
              ' reason='+native['reason']+' energy='+str(native['next']['energy']),flush=True)
    assert results[-1]['anchor']['body']['seq']==24
    assert results[-1]['event']['native']['scope']['earliest']=='35'
    assert results[-1]['event']['native']['next']['energy']==['2','0','0','3']
    for (tag,op),result in zip(schedule,results):
        assert exchange(box,cfg,case,tag,op,dict(slots=1,fields=3))['ledger']==result['ledger']
    q=Quorum(cfg);end=time.monotonic()+90
    while time.monotonic()<end:
        states=q.collect('status');after=rows(original)
        if len(after)==24 and set(states)==set('abcd') and all(s['head']['seq']==24 for s in states.values()):break
        time.sleep(.3)
    else:raise TimeoutError('recursive requests not yet reconciled across original four journals')
    save(case/'after.json',{'rows':after,'states':states,'at':time.time()})
    save(box/'ha/continuation/actual.json',{'case':'actual-01','events':24,'head':after[-1][2],
                                         'tags':[tag for tag,_ in schedule]})
    print('LIVE RECURSIVE SUPPLY PASS: original18; refusal+transfer3+retry; paid revoke; two no-charge early openings; actual next window35-41; paid grant/read; four anchors24; six lookups without duplicate payment',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);a=p.parse_args()
    try:run(a.box.resolve())
    finally:governance.close_readers();energy.close_readers()
