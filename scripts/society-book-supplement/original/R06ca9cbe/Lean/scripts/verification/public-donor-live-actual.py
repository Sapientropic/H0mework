"""Submit the authorized donor word once through the original TLS/HA client."""
import argparse
import fcntl
import importlib.util
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'Verification/public-audit/network'))
import donor_arrival_live as donor
import donor_arrival_admission as auth
from donor_result_codec import enabled as codec_enabled,decode_body
from anchor import ledger_hash,public_key
from crypto import canonical,digest,verify
from quorum import verify_certificate
from recovery_loop import save


def module(name,file):
    s=importlib.util.spec_from_file_location(name,Path(__file__).with_name(file));m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


original=module('donor_original_client','public-arrival-actual.py')
load=original.load


def wait_prefix(box,manifest,rows):
    from ha_quorum import Quorum
    q=Quorum(manifest['mac']['service']);end=time.monotonic()+1800
    while time.monotonic()<end:
        try:states={member:node.call('semantic-status') for member,node in q.nodes.items()}
        except (OSError,ValueError,EOFError):states={}
        if original.continuous.rows(manifest)==rows and set(states)==set('abcd') and all(
            s['prefix']==donor.prefix(rows) and s['backend'] and not s['warm_error'] for s in states.values()):return
        time.sleep(2)
    raise TimeoutError('DONOR_ORIGINAL_FOUR_PREFIX_NOT_READY')


def current(config,rows,kind):
    if kind==donor.CONTROL:return config['donor_admission']['point']['current']
    return donor.context(config,rows)[2]


def authorize(box,manifest,rows,kind,command,directory,label):
    config=manifest['mac']['service'];point=config['donor_admission']['point'];state=current(config,rows,kind)
    body=dict(source=point['source'],stream='recovery',actor='2',parent=donor.prefix(rows),
        member=donor.governance.member(config,rows,'2'),executor=point['executor'],cut=state['cut'],epoch=state['version'],
        certificate=digest(config['donor_admission']))
    if kind==donor.ACTION:
        value,scope,_,plan=donor.context(config,rows);index=len(value['commands'])
        auth.require(command==plan['commands'][index],'DONOR_CLIENT_AUTHORIZED_WORD')
        body.update(command=command,index=index,scope=scope,unit='energy',source_root=auth.ORIGIN)
    return body


def run(box,work,paid,limit):
    directory=work/'actual';directory.mkdir(exist_ok=True)
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        manifest=load(box/'ha/deployment.json');config=manifest['mac']['service'];initial=load(work/'original.json')['rows']
        admitted=codec_enabled(config)
        original.verify=lambda key,kind,message:decode_body(kind,verify(key,kind,message),admitted=admitted)
        auth.require(manifest['donor']['admission']==digest(load(work/'certificate.json')),'DONOR_CLIENT_INSTALLED_SOURCE')
        point=config['donor_admission']['point'];plan=load(paid/'request.json')['commands']
        outputs=load(paid/'evidence-a.json')['output']['left']['output']
        def check(result,message,key,profile,*,recovered,native_config,prefix):
            body=message['body'];event=result['event'];signed=verify(key,'ledger',result['ledger'])
            auth.require(signed==event and event['request']==message and event['type']==message['kind'] and
                all(result[k]==body[k] for k in ('source','stream','request_id','seq','cut','epoch')) and
                result['request']==digest(message),'DONOR_CLIENT_RESPONSE_BINDING')
            receipt=result['anchor'];p=receipt['body']
            verify_certificate(manifest['trust'],receipt,source=body['source'],stream='recovery',seq=p['seq'],
                               previous=p['previous'],head=result['head'],message=result['ledger'])
            auth.require(p['seq']==len(prefix)+1 and p['previous']==prefix[-1][2] and
                ledger_hash(p['previous'],result['ledger'])==result['head'],'DONOR_CLIENT_COMMIT_PARENT')
            from cryptography import x509
            from cryptography.hazmat.primitives import hashes
            fingerprint=x509.load_pem_x509_certificate((profile/'cert.pem').read_bytes()).fingerprint(hashes.SHA256()).hex()
            auth.require(recovered or event['peer']==fingerprint,'DONOR_CLIENT_EVENT_PEER')
            donor.governance.registration_bound(event)
            donor.expected(native_config,prefix,event,native=False)
            if message['kind']==donor.ACTION:
                auth.require(event['native']==outputs[body['index']],'DONOR_CLIENT_PAID_SOURCE_OUTPUT')
            return result
        # Reuse the original client transactions, TLS transcript and original-ID recovery.
        original.current_state=current;original.authorize=authorize;original.check_arrival_result=check
        owner,_=original.runtime_observer.wait_runtime(box,manifest)
        relay,thread=original.relay_for(box,manifest,owner)
        tap=original.Tap(relay.server_address[1],directory/('tls-'+str(len(list(directory.glob('tls-*.jsonl.gz')))+1)+'.jsonl.gz'),timeout=original.response_timeout(config))
        rows=initial;results=[]
        try:
            word=[('donor-control',donor.CONTROL,None)]+[('donor-'+str(i),donor.ACTION,c) for i,c in enumerate(plan)]
            for label,kind,command in word[:limit]:
                visible=original.continuous.rows(manifest)
                auth.require(visible[:len(rows)]==rows and len(visible)<=90,'DONOR_CLIENT_UNEXPECTED_SUFFIX')
                result,row=original.submit(box,manifest,directory,tap.port,label,kind,command,rows)
                rows.append(row);results.append(result)
                visible=original.continuous.rows(manifest)
                auth.require(visible[:len(rows)]==rows[:len(visible)],'DONOR_CLIENT_PAID_PREFIX_CHANGED')
                # Retained results can precede an already committed suffix on resume.
                if len(visible)<=len(rows):wait_prefix(box,manifest,rows)
                save(directory/'progress.json',dict(events=len(rows),head=rows[-1][2],committed=len(results),
                    source_status=result['event']['native'].get('status','CONTROL'),original_ids_retained=True))
                print('DONOR ORIGINAL COMMIT',len(rows),kind,result['event']['native'].get('status','CONTROL'),flush=True)
            save(directory/'events.json',rows)
            if limit==13:
                save(directory/'public-complete.json',dict(events=len(rows),head=rows[-1][2],original_events=77,
                    original_source_prefix=digest(initial),commands=12,control=1,lookup_repeats=26,
                    statuses=[v['event']['native']['status'] for v in results[1:]],new_source_requests=13,retried_economic_requests=0,
                    prior_preflight_reused=True,private_replays=0,at=time.time()))
        finally:
            tap.close();relay.shutdown();relay.server_close();thread.join(3)


if __name__=='__main__':
    sys.dont_write_bytecode=True
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);p.add_argument('--limit',type=int,default=13)
    p.add_argument('--box',type=Path,default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    p.add_argument('--admission-work',type=Path,default=Path('runtime/retained/iqa-actual77-donor-admission-20261106'))
    a=p.parse_args();assert 1<=a.limit<=13;run(a.box.resolve(),a.work.resolve(),a.admission_work.resolve(),a.limit)
