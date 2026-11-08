"""Commit the source admission, then restore supply through the original online writer."""
import argparse
import fcntl
import importlib.util
import json
from pathlib import Path
import secrets
import selectors
import socket
import socketserver
import sys
import threading
import time

ROOT=Path(__file__).resolve().parents[3];NETWORK=ROOT/'Verification/public-audit/network'
sys.path.insert(0,str(NETWORK))
from anchor import public_key
from client import check_result
from crypto import app_private,canonical,connect,digest,peer,receive,send,sign,verify
from continuous_capture import Tap
import productive_extension,productive_regeneration
from application_receipts import Journal as ApplicationJournal
from recovery_loop import save
import energy,governance,handoff,regeneration,source_extension
import material_extension,material_regeneration


def module(name,filename):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(filename))
    value=importlib.util.module_from_spec(spec);spec.loader.exec_module(value);return value


deploy=module('supply_deploy','public-supply-deploy.py')
continuous=module('supply_original_continuous','public-continuous-actual.py')
load=deploy.load


def response_timeout(config):
    if 'productive' not in config:return 180
    from ha_quorum import vote_timeout
    # Production, public replay, stage and append each retain their own deadline.
    return max(180, 2*config['productive'].get('native_call_seconds',30)+2*vote_timeout(config,'ha-stage')+10)


class SupplyRelayHandler(socketserver.BaseRequestHandler):
    def handle(self):
        try:
            with socket.create_connection(self.server.target,timeout=10) as remote:
                timeout=self.server.response_timeout
                self.request.settimeout(timeout);remote.settimeout(timeout)
                with selectors.DefaultSelector() as selector:
                    selector.register(self.request,selectors.EVENT_READ,remote)
                    selector.register(remote,selectors.EVENT_READ,self.request)
                    while True:
                        ready=selector.select(timeout)
                        if not ready:return
                        for key,_ in ready:
                            data=key.fileobj.recv(65536)
                            if not data:return
                            key.data.sendall(data)
        except (OSError,EOFError):return


def relay_for(box,manifest,owner):
    relay=continuous.Relay(('127.0.0.1',0),SupplyRelayHandler)
    relay.response_timeout=response_timeout(manifest[owner]['service'])
    relay.target=(load(box/'ha/addresses.json')['a' if owner=='mac' else 'c'],manifest[owner]['service']['port'])
    thread=threading.Thread(target=relay.serve_forever,kwargs={'poll_interval':.1},daemon=True);thread.start()
    return relay,thread


def authorize(box,manifest,prefix,kind,actor,mode,directory,label):
    cfg=manifest['mac']['service'];entry=governance.registered(prefix)[0]
    if kind==source_extension.EVENT:
        _,_,current=handoff.context(cfg,prefix)
    elif kind==material_extension.EVENT:
        _,_,current=regeneration.context(cfg,prefix)
    elif kind==productive_extension.EVENT:
        _,_,current=material_regeneration.context(cfg,prefix)
    elif kind==productive_regeneration.KIND:
        _,scope,current=productive_regeneration.context(cfg,prefix)
    elif kind==material_regeneration.KIND:
        _,scope,current=material_regeneration.context(cfg,prefix)
    else:_,scope,current=regeneration.context(cfg,prefix)
    body=dict(source=manifest['source'],stream='recovery',actor=actor,
        parent=dict(seq=len(prefix),head=prefix[-1][2]),member=governance.member(cfg,prefix,actor),
        executor=entry['result']['key'],cut=current['cut'],epoch=current['version'])
    if kind==source_extension.EVENT:
        body.update(feature=source_extension.FEATURE,certificate=digest(cfg['source_extension']))
        wanted=source_extension.authorization(body);domain='native-source-extension'
    elif kind==material_extension.EVENT:
        body.update(feature=material_extension.FEATURE,certificate=digest(cfg['material_extension']))
        wanted=material_extension.authorization(body);domain='native-material-extension'
    elif kind==productive_extension.EVENT:
        body.update(feature=productive_extension.FEATURE,certificate=digest(cfg['productive_extension']))
        wanted=productive_extension.authorization(body);domain='native-productive-extension'
    elif kind==productive_regeneration.KIND:
        body.update(command=mode,scope=scope,unit='energy')
        wanted=productive_regeneration.authorization(cfg,body);domain='native-productive-regeneration'
    elif kind==material_regeneration.KIND:
        body.update(query=dict(slots=63,fields=3),mode=mode,scope=scope,unit='energy')
        wanted=material_regeneration.authorization(cfg,body);domain='native-material-regeneration'
    else:
        body.update(query=dict(slots=63,fields=3),mode=mode,scope=scope,unit='energy')
        wanted=regeneration.authorization(cfg,body);domain='native-energy-regeneration'
    path=directory/(label+'-owner.json')
    if path.exists():
        proof=load(path)
        if proof['body']!=wanted:
            if (directory/(label+'-request.json')).exists():raise ValueError('RETAIN_ORIGINAL_OWNER_AUTHORIZATION')
            path.rename(directory/(label+'-unsubmitted-owner-'+digest(proof)+'.json'))
    if not path.exists():
        owner=entry['proof']['body']['owner']
        if owner=='mac':proof=sign(app_private(Path(cfg['ha']['owner_profile'])),domain,wanted)
        else:
            item=manifest['nodes']['c']
            code=f"import json,sys\nfrom pathlib import Path\nsys.path.insert(0,{item['code']!r})\nfrom crypto import app_private,sign\nprint(json.dumps(sign(app_private(Path({item['home']+'/ha/owner'!r})),{domain!r},{wanted!r})))"
            proof=json.loads(deploy.execute('c',code,manifest,60))
        save(path,proof)
    return {**body,'execution':proof}


def observe(box,manifest,directory,port,label,actor,kind=None,mode='normal',lookup=None,stale=None,fault=None):
    cfg=manifest['mac']['service'];profile=Path(cfg['pki'])/('auditor'+actor)
    journal=ApplicationJournal(directory/'applications.jsonl',app_private(profile),cfg['source'],cfg['stream'],'client')
    attempt=journal.start(dict(label=label,actor=actor,lookup=lookup))
    times=dict(connect_start_ns=time.monotonic_ns());problem=None
    try:
        with connect(profile,port) as connection:
            connection.settimeout(response_timeout(cfg));times['connected_ns']=time.monotonic_ns()
            uri,fingerprint,key=peer(connection)
            if uri!='urn:public-audit:server' or fingerprint!=cfg['registry']['server']['fingerprint']:
                raise ValueError('SUPPLY_SERVER_IDENTITY')
            initial_tls=connection.version();initial_cipher=connection.cipher()[0]
            attempt.add('tls',dict(peer=dict(uri=uri,fingerprint=fingerprint,app=key.public_bytes_raw().hex()),tls=initial_tls,cipher=initial_cipher))
            challenge=receive(connection);issued=verify(key,'challenge',challenge)
            attempt.add('challenge',challenge)
            times['challenge_received_ns']=time.monotonic_ns()
            if stale is not None:
                if (stale['body']['cut'],stale['body']['epoch'])==(issued['cut'],issued['epoch']):raise ValueError('STALE_TEST_REQUIRES_CHANGED_CURRENT')
                attempt.add('preflight-rejected',dict(code='STALE_AUTHORIZATION',authorization=stale))
                raise ValueError('STALE_AUTHORIZATION')
            if lookup:
                request=sign(app_private(profile),'lookup',{**issued,'lookup_id':lookup,'request_id':secrets.token_hex(16)})
            else:
                path=directory/(label+'-request.json')
                if path.exists():raise ValueError('RECOVER_ORIGINAL_REQUEST_BY_LOOKUP')
                end=time.monotonic()+20
                while True:
                    prefix=continuous.rows(manifest)
                    try:
                        if kind==source_extension.EVENT:_,_,current=handoff.context(cfg,prefix)
                        elif kind==material_extension.EVENT:_,_,current=regeneration.context(cfg,prefix)
                        elif kind==productive_extension.EVENT:_,_,current=material_regeneration.context(cfg,prefix)
                        elif kind==productive_regeneration.KIND:_,_,current=productive_regeneration.context(cfg,prefix)
                        elif kind==material_regeneration.KIND:_,_,current=material_regeneration.context(cfg,prefix)
                        else:_,_,current=regeneration.context(cfg,prefix)
                    except ValueError as error:
                        if str(error) not in {'MATERIAL_NOT_COMMITTED','PRODUCTIVE_NOT_COMMITTED'} or time.monotonic()>=end:raise
                        time.sleep(.1)
                        continue
                    if (current['cut'],current['version'])==(issued['cut'],issued['epoch']):break
                    if time.monotonic()>=end:raise ValueError('SUPPLY_HEAD_NOT_READY')
                    time.sleep(.1)
                body=authorize(box,manifest,prefix,kind,actor,mode,directory,label)
                if (body['cut'],body['epoch'])!=(issued['cut'],issued['epoch']):raise ValueError('SUPPLY_HEAD_NOT_READY')
                request=sign(app_private(profile),kind,{**issued,**body,'request_id':secrets.token_hex(16)})
            save(directory/(label+'-request.json'),request);save(directory/(label+'-challenge.json'),challenge)
            times['request_sent_ns']=time.monotonic_ns();attempt.add('send-intent',request)
            if fault=='after-intent':__import__('os')._exit(73)
            send(connection,request);attempt.add('sent',dict(request=digest(request)))
            if fault=='after-send':__import__('os')._exit(73)
            try:
                response=receive(connection);verify(key,response['kind'],response)
                attempt.add('response',response)
                if fault=='after-response':__import__('os')._exit(73)
            except (OSError,EOFError) as error:
                response={'transport_error':type(error).__name__};attempt.add('transport-error',response)
            times['response_received_ns']=time.monotonic_ns()
            value=sign(app_private(profile),'online-client-observation',dict(peer=dict(uri=uri,fingerprint=fingerprint,
                app=key.public_bytes_raw().hex()),tls=initial_tls,cipher=initial_cipher,
                challenge=challenge,request=request,response=response,times=times))
            save(directory/(label+'-observation.json'),value)
            return value
    except BaseException as error:
        problem=type(error).__name__;raise
    finally:attempt.close(problem)


def submit(box,manifest,directory,port,label,actor,kind,mode):
    cfg=manifest['mac']['service'];path=directory/(label+'-request.json')
    paid=directory/(label+'-result.json')
    if paid.exists() and all((directory/(label+'-lookup-'+str(n)+'-observation.json')).exists() for n in range(2)):
        result=load(paid);request=load(path)
        row=continuous.rows(manifest)[result['anchor']['body']['seq']-1]
        if result['event']['request']!=request or result['ledger']!=json.loads(row[3]):raise ValueError('PAID_RESULT_CHANGED')
        return result
    if not path.exists():
        observation=observe(box,manifest,directory,port,label,actor,kind,mode)
    else:
        original=load(path)
        observation=observe(box,manifest,directory,port,label+'-recover-'+secrets.token_hex(4),actor,
                            lookup=original['body']['request_id'])
    request=load(path);response=observation['body']['response'];key=public_key(cfg['registry']['server'])
    if response.get('kind')=='response':result=verify(key,'response',response);recovered=False
    elif response.get('kind')=='lookup-response':result=verify(key,'lookup-response',response)['result'];recovered=True
    elif response.get('kind')=='error':raise ValueError('SIGNED_SUPPLY_REJECTION:'+verify(key,'error',response)['code'])
    else:raise ValueError('SUPPLY_RESULT_UNKNOWN_RETAIN_ORIGINAL_REQUEST')
    prefix=continuous.rows(manifest)[:result['anchor']['body']['seq']-1]
    checked=check_result(result,request,key,Path(cfg['pki'])/('auditor'+actor),expected_stream='recovery',
        recovered=recovered,native_config=cfg,prefix=prefix)
    save(directory/(label+'-result.json'),checked)
    for n in range(2):
        target=directory/(label+'-lookup-'+str(n)+'-observation.json')
        if target.exists():value=load(target)
        else:value=observe(box,manifest,directory,port,label+'-lookup-'+str(n),actor,lookup=request['body']['request_id'])
        reply=verify(key,'lookup-response',value['body']['response'])
        if reply['result']['ledger']!=result['ledger']:raise ValueError('SUPPLY_IDEMPOTENCE')
    print('ACTUAL SUPPLY',label,'seq',result['anchor']['body']['seq'],
          'status',result['event']['native'].get('status','ADMITTED'),flush=True)
    return result


def finalize(box,manifest,directory,results,owner):
    original=load(directory/'before.json')
    expected=continuous.rows(manifest);continuous.wait_prefix(box,manifest,expected)
    additions=[r['event'] for r in results[1:]]
    if len(expected)!=len(original)+14:raise ValueError('DUPLICATE_OR_MISSING_SUPPLY_EVENT')
    if sum(e['native']['opening'] for e in additions)!=3:raise ValueError('THREE_REAL_WINDOWS_REQUIRED')
    if sum(bool(e['native']['packets']) for e in additions)!=3:raise ValueError('THREE_REAL_DELIVERIES_REQUIRED')
    if additions[0]['native']['status']!='BLOCKED':raise ValueError('FIRST_FUEL_REFUSAL_REQUIRED')
    argument,scope,current=regeneration.context(manifest['mac']['service'],expected)
    save(directory/'source-input.json',argument);save(directory/'after.json',dict(rows=expected,current=current,scope=scope))
    save(directory/'public-complete.json',dict(events=len(expected),head=expected[-1][2],
        actual_supply_requests=13,new_windows=3,deliveries=3,lookups=sum(load(p)["body"]["request"]["kind"]=="lookup" for p in directory.glob("*-observation.json")),owner=owner,physical_reboots=0))
    print('ORIGINAL ONLINE SUPPLY PASS: admission +13 own successors; 3 windows; 3 paid deliveries; all original-ID lookups',flush=True)


def run(box):
    lock=(box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=deploy.location(box);manifest=load(box/'ha/deployment.json')
    directory=home/'actual';directory.mkdir(exist_ok=True)
    before=continuous.rows(manifest)
    if not (directory/'before.json').exists():
        if dict(seq=len(before),head=before[-1][2])!=load(home/'admission.json')['point']['prefix']:
            raise ValueError('SUPPLY_ACTIVATION_PARENT_MOVED')
        save(directory/'before.json',before)
    original=load(directory/'before.json')
    if [list(r) for r in before[:len(original)]]!=original:raise ValueError('ORIGINAL_PREFIX_CHANGED')
    owner,state=continuous.epoch.wait_leader(box,manifest)
    labels=['admission']+['supply-'+str(n) for n in range(13)]
    if all(all((directory/(label+suffix)).exists() for suffix in
            ['-result.json','-lookup-0-observation.json','-lookup-1-observation.json']) for label in labels):
        results=[submit(box,manifest,directory,0,label,'2',source_extension.EVENT if label=='admission' else regeneration.KIND,'normal') for label in labels]
        try:finalize(box,manifest,directory,results,owner)
        finally:governance.close_readers();energy.close_readers()
        return
    relay,thread=relay_for(box,manifest,owner)
    attempt=len(list(directory.glob('tls-*.jsonl.gz')))+1
    tap=Tap(relay.server_address[1],directory/('tls-'+str(attempt)+'.jsonl.gz'),timeout=240)
    try:
        results=[submit(box,manifest,directory,tap.port,'admission','2',source_extension.EVENT,'normal')]
        for n in range(13):
            results.append(submit(box,manifest,directory,tap.port,'supply-'+str(n),'2',regeneration.KIND,
                                  'withhold-fuel' if n==0 else 'normal'))
        finalize(box,manifest,directory,results,owner)
    finally:
        tap.close();relay.shutdown();relay.server_close();thread.join(3)
        governance.close_readers();energy.close_readers()


def close_and_audit(box):
    lock=(box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=deploy.location(box);directory=home/'actual';manifest=load(box/'ha/deployment.json')
    if (directory/'owner-accepted.json').exists():
        continuous.resume_runtime(box,manifest)
        continuous.epoch.wait_leader(box,manifest)
        return
    if not (directory/'public-complete.json').exists():raise ValueError('ACTUAL_SUPPLY_NOT_COMPLETE')
    rows=continuous.rows(manifest);save(directory/'events.json',rows)
    frozen={};transition=False
    try:
        for owner in ('spark','mac'):
            frozen[owner]=deploy.roll.freeze_writer(box,manifest,owner)
            save(directory/'audit-barrier.json',frozen)
        inventory={n:continuous.epoch.inventory(box,manifest,n) for n in 'abcd'}
        prior=load(directory/'inventories.json') if (directory/'inventories.json').exists() else []
        prior.append(inventory);save(directory/'inventories.json',prior)
        transition=True
        for owner in ('spark','mac'):deploy.retire_writer(box,manifest,owner,frozen[owner])
        continuous.epoch.stop_anchors(manifest)
        save(directory/'closed.json',continuous.epoch.close_inventory(box,manifest,prior))
        for owner,member in [('mac','a'),('spark','c')]:
            journal=manifest[owner]['service']['online_privacy']['journal']
            code='from pathlib import Path\nprint(Path('+repr(journal)+').read_text(),end="")'
            (directory/(owner+'-boundary.jsonl')).write_text(deploy.execute(member,code,manifest,90))
        subprocess=__import__('subprocess')
        subprocess.run([sys.executable,str(Path(__file__).with_name('public-supply-check.py')),str(box),'--closed'],check=True)
    finally:
        if transition:
            for owner,record in frozen.items():deploy.retire_writer(box,manifest,owner,record)
            continuous.resume_runtime(box,manifest)
        else:
            for owner,record in frozen.items():deploy.roll.spare.writer_signal(box,manifest,owner,'SIGCONT',record)
    continuous.epoch.wait_leader(box,manifest)
    save(directory/'resumed.json',dict(at=time.time(),states=continuous.epoch.states(box,manifest)))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('box',type=Path)
    parser.add_argument('--close',action='store_true');args=parser.parse_args()
    if args.close:close_and_audit(args.box.resolve())
    else:run(args.box.resolve())
