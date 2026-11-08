"""Read the already-paid donor delivery from the restored original TLS service."""
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
from donor_result_codec import enabled as codec_enabled,decode_body


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


actual=module('donor_resume_client','public-donor-live-actual.py');original=actual.original;load=actual.load


def run(box,work):
    manifest=load(box/'ha/deployment.json');home=work/'resume-probe';home.mkdir(exist_ok=True)
    if (home/'captured.json').exists():return
    owner,_=original.runtime_observer.wait_runtime(box,manifest)
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        before=original.continuous.rows(manifest);assert before==load(work/'actual/events.json') and len(before)==90
        assert load(work/'actual/resumed.json')['head']==before[-1][2]
        delivered=next(row for row in reversed(before) if json.loads(row[3])['body'].get('type')=='energy-donor'
                       and json.loads(row[3])['body']['native']['status']=='DELIVERED')
        request=json.loads(delivered[3])['body']['request']['body']['request_id']
        if (home/'before.json').exists():assert load(home/'before.json')==before
        else:save(home/'before.json',before)
        if not (home/'restored-delivery-observation.json').exists():
            relay,thread=original.relay_for(box,manifest,owner)
            tap=Tap(relay.server_address[1],home/('tls-'+str(len(list(home.glob('tls-*.jsonl.gz')))+1)+'.jsonl.gz'),timeout=original.response_timeout(manifest[owner]['service']))
            try:original.observe(box,manifest,home,tap.port,'restored-delivery',lookup=request)
            finally:tap.close();relay.shutdown();relay.server_close();thread.join(3)
        cfg=manifest[owner]['service'];member='a' if owner=='mac' else 'c';journal=cfg['online_privacy']['journal']
        for name,path in [('boundary',journal),('applications',journal+'.applications.jsonl')]:
            raw=original.deploy.execute(member,'from pathlib import Path\nprint(Path('+repr(path)+').read_text(),end="")',manifest,120)
            target=home/('server-'+name+'.jsonl')
            if not target.exists():target.write_text(raw)
        after=original.continuous.rows(manifest);assert after==before;save(home/'after.json',after)
        save(home/'captured.json',dict(owner=owner,events=90,seq=delivered[0],head=before[-1][2],lookup_id=request))
    print('RESTORED DONOR DELIVERY RETURNED: original90; zero new economic events',flush=True)


def check(box,work):
    manifest=load(box/'ha/deployment.json');home=work/'resume-probe';cfg=manifest['mac']['service']
    rows=load(home/'before.json');assert rows==load(home/'after.json')==original.continuous.rows(manifest)==load(work/'actual/events.json') and len(rows)==90
    def records(name):return [json.loads(v) for v in (home/name).read_text().splitlines()]
    client=replay(records('applications.jsonl'),public_key(cfg['registry']['auditor2']),cfg['source'],'recovery','client',cfg['registry'])
    key=public_key(cfg['registry']['server']);server=replay(records('server-applications.jsonl'),key,cfg['source'],'recovery','server',cfg['registry'])
    assert len(client)==1;value=next(iter(client.values()));counterparts=[v for v in server.values() if v['challenge']==value['challenge']]
    assert len(counterparts)==1;peer=counterparts[0]
    assert value['status']==peer['status']=='verified' and value['response']==peer['response']
    assert value['tls']['tls']==peer['tls']['tls']=='TLSv1.3'
    request=value['intended'];assert request['kind']=='lookup'
    challenge=verify(key,'challenge',value['challenge']);assert all(request['body'][k]==v for k,v in challenge.items())
    envelope=decode_body('lookup-response',verify(key,'lookup-response',value['response']),admitted=codec_enabled(cfg));result=envelope['result'];seq=result['anchor']['body']['seq'];row=rows[seq-1]
    assert envelope['request']==digest(request) and result['ledger']==json.loads(row[3])
    assert request['body']['lookup_id']==result['event']['request']['body']['request_id']
    assert result['event']['type']=='energy-donor' and result['event']['native']['status']=='DELIVERED'
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
    report=dict(exit=0,events=90,delivery_seq=seq,new_economic_events=0,application_replays=1,tls_streams=2,
                head=rows[-1][2],pending=0,source=__import__('hashlib').sha256(Path(__file__).read_bytes()).hexdigest())
    save(home/'accepted.json',report)
    print('INDEPENDENT RESTORED DONOR TLS PASS: exact application/wire; six-slot delivery; 2 complete TLS streams; zero new payment',flush=True)
    return report


if __name__=='__main__':
    sys.dont_write_bytecode=True
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);p.add_argument('--actual',action='store_true')
    p.add_argument('--box',type=Path,default=ROOT/'.agents/tmp/public-recovery-20261103/live');a=p.parse_args()
    (run if a.actual else check)(a.box.resolve(),a.work.resolve())
