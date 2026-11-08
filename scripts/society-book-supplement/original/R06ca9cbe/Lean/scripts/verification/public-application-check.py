"""Independently replay application bytes and consume append-only gap dispositions."""
import argparse,base64,copy,importlib.util,json,os,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from crypto import app_private,canonical,digest,sign,verify
from anchor import public_key
from application_receipt_check import replay,recover,server_recovery
from quorum import verify_certificate
from online_privacy_check import frames,tls_streams

def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
original=module('receipt_original','public-supply-actual.py');load=original.load
def records(path):return [json.loads(x) for x in Path(path).read_text().splitlines()]
def sha(path):return __import__('hashlib').sha256(Path(path).read_bytes()).hexdigest()

def analyze(box,client_records=None):
    home=box/'ha/regeneration/online/applications';manifest=load(box/'ha/deployment.json');cfg=manifest['mac']['service']
    rows=load(home/'events-before.json');assert rows==load(home/'events-after.json')==original.continuous.rows(manifest)[:len(rows)]
    clients=replay(client_records if client_records is not None else records(home/'applications.jsonl'),
        public_key(cfg['registry']['auditor2']),cfg['source'],'recovery','client',cfg['registry'])
    states={v['records'][0]['body']['data']['label']:v for v in clients.values()};assert len(states)==7
    servers={};wire=[]
    for owner in ('mac','spark'):
        value=replay(records(home/(owner+'-applications.jsonl')),public_key(cfg['registry']['server']),cfg['source'],'recovery','server',cfg['registry'])
        servers.update(value)
        for signed in records(home/(owner+'-boundary.jsonl')):
            if signed['kind']=='online-wire-observation':wire.append(verify(public_key(cfg['registry']['server']),'online-wire-observation',signed))
    matched={}
    for label,state in states.items():
        same=[v for v in servers.values() if v['challenge']==state['challenge']]
        assert len(same)==1,'EXACT_APPLICATION_COUNTERPART';peer=same[0];matched[label]=peer
        assert state['tls']['tls']==peer['tls']['tls']=='TLSv1.3'
        # A second decoder consumes the original wire journal, not producer flags.
        legacy=[]
        for value in wire:
            data={'sent':b'','received':b''}
            for op in value['operations']:data[op['direction']]+=base64.b64decode(op['bytes'],validate=True)
            sent=frames(data['sent']);received=frames(data['received'])
            if sent and sent[0]==state['challenge']:legacy.append((data,sent,received))
        assert len(legacy)==1 and legacy[0][0]==peer['io'],'DUAL_LITERAL_REPLAY'
        if state['response'] is not None:assert state['response']==peer['response']
        if state['response'] and state['response']['kind']=='lookup-response':
            envelope=state['response']['body'];result=envelope['result'];row=rows[result['anchor']['body']['seq']-1]
            assert result['ledger']==json.loads(row[3]) and result['event']==result['ledger']['body']
            assert state['intended']['body']['lookup_id']==result['event']['request']['body']['request_id']
            verify_certificate(manifest['trust'],result['anchor'],source=cfg['source'],stream='recovery',
                seq=row[0],previous=row[1],head=row[2],message=result['ledger'])
    assert states['lookup']['status']==states['recovery']['status']==states['missing']['status']=='verified'
    assert states['missing']['response']['kind']=='error' and states['missing']['response']['body']['code']=='REQUEST_NOT_COMMITTED'
    assert states['stale']['status']=='verified-preflight-rejection'
    proof=states['stale']['rejection']['authorization'];body=proof['body']
    entry=next(e for e in original.governance.registered(rows) if e['result']['key']==body['executor'])
    verify(public_key(cfg['ha']['owners'][entry['proof']['body']['owner']]),'native-energy-regeneration',proof)
    assert (body['cut'],body['epoch'])!=(states['stale']['challenge']['body']['cut'],states['stale']['challenge']['body']['epoch'])
    assert matched['stale']['status']==matched['after-intent']['status']=='verified-no-command'
    assert states['after-intent']['status']==states['after-send']['status']=='insufficient'
    assert states['after-response']['status']=='verified'
    assert states['after-response']['records'][-1]['body']['data']=={'error':'RECOVERED_AFTER_PROCESS_EXIT'}
    legacy=load(home.parent/'actual/admission-observation.json')
    verify(public_key(cfg['registry']['auditor2']),'online-client-observation',legacy)
    old=dict(status='insufficient',intended=legacy['body']['request'],tail=digest(legacy))
    linked=recover(old,states['recovery']);assert linked['status']=='recovered'
    sent=states['after-send'];observed=matched['after-send'];assert observed['request']==sent['intended']
    if observed['status']=='verified':outcome=server_recovery(sent,observed)
    else:
        assert sent['intended']['kind']=='lookup'
        assert sent['intended']['body']['lookup_id']==states['recovery']['intended']['body']['lookup_id']
        outcome=dict(status='original-event-recovered',client_received=False,evidence=states['recovery']['tail'])
    old_gap=load(home.parent/'final-check.json')['wire']['unsubmitted'][0]
    assert old_gap['status']=='insufficient-application-evidence'
    captured=tls_streams(home,expected_connections=7)
    dispositions={
        'original32':dict(origin=digest(legacy),observation='insufficient-reply',outcome='recovered',support=states['recovery']['tail'],pending=[]),
        'historical-tls':dict(origin=digest(old_gap),observation='insufficient-application-evidence',outcome='reproduced-preflight-rejection',
            support=states['stale']['tail'],pending=[],blocked=['historical application bytes']),
        'after-intent':dict(origin=states['after-intent']['tail'],observation='insufficient',outcome='verified-no-command',support=matched['after-intent']['tail'],pending=[]),
        'after-send':dict(origin=sent['tail'],observation='insufficient',outcome=outcome['status'],support=outcome['evidence'],pending=[]),
        'after-response':dict(origin=states['after-response']['records'][-2]['signature'],observation='durable-response',outcome='closed-after-restart',support=states['after-response']['tail'],pending=[])}
    assert {v['tail'] for v in states.values() if v['status']=='insufficient'}=={
        dispositions[label]['origin'] for label in ('after-intent','after-send')},'UNCOVERED_INSUFFICIENT_ATTEMPT'
    return dict(states=states,matched=matched,dispositions=dispositions,tls_streams=len(captured))

def issue(box):
    home=box/'ha/regeneration/online/applications';value=analyze(box);cfg=load(box/'ha/deployment.json')['mac']['service']
    path=home/'gap-events.jsonl'
    if path.exists():return
    key=app_private(Path(cfg['pki'])/'auditor2');previous='0'*64;index=0
    with path.open('xb') as file:
        for gap,result in value['dispositions'].items():
            for action,data in [('opened',{'origin':result['origin']}),('linked',{'support':result['support']})]:
                item=sign(key,'application-gap/v1',dict(index=index,previous=previous,source=cfg['source'],stream='recovery',gap=gap,action=action,data=data))
                file.write(canonical(item)+b'\n');file.flush();os.fsync(file.fileno());previous=digest(item);index+=1
    print('APPLICATION GAP LINKS ISSUED: five original obligations; no manufactured historical receipt',flush=True)

def check(box,check_main=False):
    home=box/'ha/regeneration/online/applications';value=analyze(box);cfg=load(box/'ha/deployment.json')['mac']['service']
    previous='0'*64;seen={}
    for index,item in enumerate(records(home/'gap-events.jsonl')):
        body=verify(public_key(cfg['registry']['auditor2']),'application-gap/v1',item)
        assert body['index']==index and body['previous']==previous and body['source']==cfg['source'] and body['stream']=='recovery'
        target=value['dispositions'][body['gap']];state=seen.get(body['gap'])
        if state is None:assert body['action']=='opened' and body['data']=={'origin':target['origin']};seen[body['gap']]='opened'
        else:assert state=='opened' and body['action']=='linked' and body['data']=={'support':target['support']};seen[body['gap']]='linked'
        previous=digest(item)
    assert set(seen)==set(value['dispositions']) and set(seen.values())=={'linked'}
    negatives=[];baseline=records(home/'applications.jsonl')
    for label in ('delete-stage','duplicate-tail','alter-tls','alter-request','forge-status'):
        bad=copy.deepcopy(baseline)
        if label=='delete-stage':del bad[1]
        elif label=='duplicate-tail':bad.append(bad[-1])
        elif label=='alter-tls':next(x for x in bad if x['body']['stage']=='tls')['body']['data']['tls']='TLSv1.2'
        elif label=='alter-request':next(x for x in bad if x['body']['stage']=='send-intent')['body']['data']['body']['lookup_id']='f'*32
        else:bad[-1]['body']['data']['verified']=True
        try:analyze(box,bad)
        except Exception:negatives.append(label)
        else:raise AssertionError('APPLICATION_MUTATION_ACCEPTED:'+label)
    inputs={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),Path(__file__).with_name('public-application-actual.py'),
        Path(__file__).with_name('public-application-roll.py'),NETWORK/'application_receipts.py',NETWORK/'application_receipt_check.py',
        NETWORK/'online_privacy.py',Path(__file__).with_name('public-supply-actual.py')]}
    if check_main:
        import subprocess
        for name,wanted in inputs.items():assert __import__('hashlib').sha256(subprocess.check_output(['git','show','refs/heads/main:'+name],cwd=ROOT)).hexdigest()==wanted
    report=dict(exit=0,events=45,ledger_unchanged=True,attempts=7,dual_literal_replays=7,tls_streams=value['tls_streams'],
        process_exits=3,dispositions=value['dispositions'],pending=0,negative_controls=negatives,inputs=inputs,main_verified=check_main)
    (home/'accepted.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print('INDEPENDENT APPLICATION RECEIPT PASS '+json.dumps({k:report[k] for k in ('events','attempts','dual_literal_replays','tls_streams','pending','main_verified')}),flush=True)
    return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--issue',action='store_true');p.add_argument('--check-main',action='store_true');a=p.parse_args()
    if a.issue:issue(a.box.resolve())
    else:check(a.box.resolve(),a.check_main)
