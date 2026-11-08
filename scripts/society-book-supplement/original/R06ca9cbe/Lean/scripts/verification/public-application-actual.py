"""Exercise durable receipts against the existing live service without advancing its ledger."""
import argparse,importlib.util,json,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from crypto import app_private,canonical,digest,sign
from application_receipts import Journal,Attempt
from recovery_loop import save

def module(name,file):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value
original=module('application_original','public-supply-actual.py');load=original.load

def worker(box,home,port,label,fault):
    manifest=load(box/'ha/deployment.json');request=load(home.parent/'actual/admission-request.json')
    original.observe(box,manifest,home,port,label,'2',lookup=request['body']['request_id'],fault=fault)

def run(box):
    home=box/'ha/regeneration/online/applications';manifest=load(box/'ha/deployment.json')
    before=original.continuous.rows(manifest)
    if not (home/'events-before.json').exists():save(home/'events-before.json',before)
    assert before==load(home/'events-before.json') and len(before)==45
    owner,_=original.continuous.epoch.wait_leader(box,manifest)
    relay,thread=original.relay_for(box,manifest,owner)
    number=len(list(home.glob('tls-*.jsonl.gz')))+1;tap=original.Tap(relay.server_address[1],home/('tls-'+str(number)+'.jsonl.gz'),timeout=240)
    old=load(home.parent/'actual/admission-request.json');stale=next((home.parent/'actual').glob('supply-2-unsubmitted-owner-*.json'))
    try:
        if not (home/'lookup-observation.json').exists():original.observe(box,manifest,home,tap.port,'lookup','2',lookup=old['body']['request_id'])
        if not (home/'stale-complete.json').exists():
            try:original.observe(box,manifest,home,tap.port,'stale','2',stale=load(stale))
            except ValueError as error:
                assert str(error)=='STALE_AUTHORIZATION';save(home/'stale-complete.json',dict(exception=str(error)))
            else:raise AssertionError('STALE_AUTHORIZATION_WAS_NOT_REJECTED')
        for fault in ('after-intent','after-send','after-response'):
            path=home/(fault+'-exit.json')
            if not path.exists():
                run=subprocess.run([sys.executable,str(Path(__file__).resolve()),str(box),'--worker',fault,'--port',str(tap.port)],timeout=240)
                assert run.returncode==73;save(path,dict(exit=73,stage=fault))
        if not (home/'recovery-observation.json').exists():original.observe(box,manifest,home,tap.port,'recovery','2',lookup=old['body']['request_id'])
        if not (home/'missing-observation.json').exists():original.observe(box,manifest,home,tap.port,'missing','2',lookup='0'*32)
    finally:tap.close();relay.shutdown();relay.server_close();thread.join(3)
    profile=Path(manifest['mac']['service']['pki'])/'auditor2';journal=Journal(home/'applications.jsonl',app_private(profile),manifest['source'],'recovery','client')
    records=[json.loads(line) for line in (home/'applications.jsonl').read_text().splitlines()]
    target=next(v['body']['attempt'] for v in records if v['body']['stage']=='opened' and v['body']['data']['label']=='after-response')
    if not any(v['body']['attempt']==target and v['body']['stage']=='closed' for v in records):Attempt(journal,target).close('RECOVERED_AFTER_PROCESS_EXIT')
    time.sleep(.5)
    for who,member in [('mac','a'),('spark','c')]:
        path=manifest[who]['service']['online_privacy']['journal']
        code='from pathlib import Path\nimport json\np=Path('+repr(path+'.applications.jsonl')+');q=Path('+repr(path)+')\nprint(json.dumps(dict(application=p.read_text() if p.exists() else "",wire=q.read_text())))'
        content=json.loads(original.deploy.execute(member,code,manifest,60))
        (home/(who+'-applications.jsonl')).write_text(content['application']);(home/(who+'-boundary.jsonl')).write_text(content['wire'])
    after=original.continuous.rows(manifest);assert after==before
    save(home/'events-after.json',after);save(home/'actual-complete.json',dict(owner=owner,events=45,ledger_unchanged=True,
        scenarios=['lookup','stale','after-intent','after-send','after-response','recovery','missing'],reboots=0))
    print('LIVE APPLICATION RECEIPTS PASS: 7 actual attempts; 3 process exits73; original45 unchanged',flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('box',type=Path);p.add_argument('--worker');p.add_argument('--port',type=int)
    a=p.parse_args()
    if a.worker:worker(a.box.resolve(),a.box.resolve()/'ha/regeneration/online/applications',a.port,a.worker,a.worker)
    else:run(a.box.resolve())
