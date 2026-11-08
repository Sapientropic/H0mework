"""Read the paid arrival delivery from the resumed original TLS service."""
import argparse
import base64
import fcntl
import importlib.util
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
from anchor import public_key
from application_receipt_check import replay
from crypto import digest,verify
from continuous_capture import Tap
from online_privacy_check import frames,tls_streams
from quorum import verify_certificate
from recovery_loop import save

s=importlib.util.spec_from_file_location('arrival_resumed_actual',Path(__file__).with_name('public-arrival-actual.py'))
actual=importlib.util.module_from_spec(s);s.loader.exec_module(actual)
load=actual.load


def run(box):
    manifest=load(box/'ha/deployment.json');home=actual.deploy.location(box)/'resume-probe';home.mkdir(exist_ok=True)
    if (home/'captured.json').exists():return
    owner,_=actual.runtime_observer.wait_runtime(box,manifest)
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        before=actual.continuous.rows(manifest);assert len(before)==77
        delivered=next(row for row in reversed(before) if json.loads(row[3])['body'].get('type')=='energy-arrival'
                       and json.loads(row[3])['body']['native']['status']=='DELIVERED')
        request=json.loads(delivered[3])['body']['request']['body']['request_id']
        if (home/'before.json').exists():assert load(home/'before.json')==before
        else:save(home/'before.json',before)
        if not (home/'restored-delivery-observation.json').exists():
            relay,thread=actual.relay_for(box,manifest,owner)
            tap=Tap(relay.server_address[1],home/('tls-'+str(len(list(home.glob('tls-*.jsonl.gz')))+1)+'.jsonl.gz'),timeout=actual.response_timeout(manifest[owner]['service']))
            try:actual.observe(box,manifest,home,tap.port,'restored-delivery',lookup=request)
            finally:tap.close();relay.shutdown();relay.server_close();thread.join(3)
        cfg=manifest[owner]['service'];member='a' if owner=='mac' else 'c';journal=cfg['online_privacy']['journal']
        for name,path in [('boundary',journal),('applications',journal+'.applications.jsonl')]:
            raw=actual.deploy.execute(member,'from pathlib import Path\nprint(Path('+repr(path)+').read_text(),end="")',manifest,120)
            target=home/('server-'+name+'.jsonl')
            if not target.exists():target.write_text(raw)
        after=actual.continuous.rows(manifest);assert after==before;save(home/'after.json',after)
        save(home/'captured.json',dict(owner=owner,events=77,seq=delivered[0],head=before[-1][2],lookup_id=request))
    print('ACTUAL RESTORED ARRIVAL DELIVERY RETURNED: original77; zero new economic events',flush=True)


def check(box):
    manifest=load(box/'ha/deployment.json');home=actual.deploy.location(box)/'resume-probe';cfg=manifest['mac']['service']
    rows=load(home/'before.json');assert rows==load(home/'after.json')==actual.continuous.rows(manifest) and len(rows)==77
    assert rows==load(home.parent/'actual/events.json')
    def records(name):return [json.loads(v) for v in (home/name).read_text().splitlines()]
    client=replay(records('applications.jsonl'),public_key(cfg['registry']['auditor2']),cfg['source'],'recovery','client',cfg['registry'])
    key=public_key(cfg['registry']['server']);server=replay(records('server-applications.jsonl'),key,cfg['source'],'recovery','server',cfg['registry'])
    assert len(client)==1;value=next(iter(client.values()));counterparts=[v for v in server.values() if v['challenge']==value['challenge']]
    assert len(counterparts)==1;peer=counterparts[0]
    assert value['status']==peer['status']=='verified' and value['response']==peer['response']
    assert value['tls']['tls']==peer['tls']['tls']=='TLSv1.3'
    request=value['intended'];assert request['kind']=='lookup'
    challenge=verify(key,'challenge',value['challenge']);assert all(request['body'][k]==v for k,v in challenge.items())
    envelope=verify(key,'lookup-response',value['response']);result=envelope['result'];seq=result['anchor']['body']['seq'];row=rows[seq-1]
    assert envelope['request']==digest(request) and result['ledger']==json.loads(row[3])
    assert request['body']['lookup_id']==result['event']['request']['body']['request_id']
    assert result['event']['type']=='energy-arrival' and result['event']['native']['status']=='DELIVERED'
    verify_certificate(manifest['trust'],result['anchor'],source=cfg['source'],stream='recovery',seq=seq,previous=row[1],head=row[2],message=result['ledger'])
    matched=[]
    for signed in records('server-boundary.jsonl'):
        if signed['kind']!='online-wire-observation':continue
        wire=verify(key,signed['kind'],signed);data={'sent':b'','received':b''}
        for op in wire['operations']:data[op['direction']]+=base64.b64decode(op['bytes'],validate=True)
        sent=frames(data['sent'])
        if sent and sent[0]==value['challenge']:
            assert sent==[value['challenge'],value['response']] and frames(data['received'])==[request]
            assert data==peer['io'];matched.append(digest(signed))
    streams=tls_streams(home,expected_connections=1)
    assert len(matched)==1 and len(streams)==2 and all(v['forwarded']==v['bytes'] for v in streams.values())
    report=dict(exit=0,events=77,delivery_seq=seq,new_economic_events=0,application_replays=1,tls_streams=2,
                head=rows[-1][2],pending=0,source=actual.deploy.sha(Path(__file__)),events_sha256=actual.deploy.sha(home.parent/'actual/events.json'))
    save(home/'accepted.json',report)
    print('INDEPENDENT RESTORED ARRIVAL TLS PASS: exact application/wire; six-slot delivery; 2 complete TLS streams; zero new payment',flush=True)
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--actual',action='store_true');a=p.parse_args()
    if a.actual:run(a.box.resolve())
    else:check(a.box.resolve())
