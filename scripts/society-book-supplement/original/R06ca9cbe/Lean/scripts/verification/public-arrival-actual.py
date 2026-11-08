"""Commit source arrival and its eight native successors through the original TLS writer."""
import argparse
import fcntl
import importlib.util
import inspect
import json
from pathlib import Path
import secrets
import selectors
import socket
import socketserver
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[3]
NETWORK = ROOT/'Verification/public-audit/network'
sys.path.insert(0, str(NETWORK))
from anchor import ledger_hash, public_key, verify_commit
from continuous_capture import Tap
from crypto import app_private, canonical, connect, digest, peer, receive, send, sign, verify
from recovery_loop import save
from application_receipts import Journal as ApplicationJournal
import arrival_extension
import arrival_readiness
import arrival_regeneration
import energy
import governance
import productive_extension
import productive_regeneration


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


deploy = module('arrival_deploy', 'public-arrival-deploy.py')
continuous = module('arrival_original_continuous', 'public-continuous-actual.py')
runtime_observer = module('arrival_original_runtime', 'public-productive-actual.py')
load = deploy.load


def response_timeout(config):
    settings = config.get('arrival', config.get('productive'))
    if not settings:
        return 180
    from ha_quorum import vote_timeout
    return max(180, 2*settings.get('native_call_seconds', 30)
               + 2*vote_timeout(config, 'ha-stage') + 10)


class ArrivalRelayHandler(socketserver.BaseRequestHandler):
    def handle(self):
        try:
            with socket.create_connection(self.server.target, timeout=10) as remote:
                timeout = self.server.response_timeout
                self.request.settimeout(timeout)
                remote.settimeout(timeout)
                with selectors.DefaultSelector() as selector:
                    selector.register(self.request, selectors.EVENT_READ, remote)
                    selector.register(remote, selectors.EVENT_READ, self.request)
                    while True:
                        ready = selector.select(timeout)
                        if not ready:
                            return
                        for key, _ in ready:
                            data = key.fileobj.recv(65536)
                            if not data:
                                return
                            key.data.sendall(data)
        except (OSError, EOFError):
            return


def relay_for(box, manifest, owner):
    relay = continuous.Relay(('127.0.0.1', 0), ArrivalRelayHandler)
    relay.response_timeout = response_timeout(manifest[owner]['service'])
    address = load(box/'ha/addresses.json')['a' if owner == 'mac' else 'c']
    relay.target = (address, manifest[owner]['service']['port'])
    thread = threading.Thread(target=relay.serve_forever,
                              kwargs={'poll_interval': .1}, daemon=True)
    thread.start()
    return relay, thread


def current_state(config, rows, kind):
    if kind == arrival_extension.EVENT:
        return productive_regeneration.context(config, rows)[2]
    if kind == arrival_regeneration.KIND:
        return arrival_regeneration.context(config, rows)[2]
    raise ValueError('ARRIVAL_REQUEST_KIND')


def authorize(box, manifest, prefix, kind, command, directory, label):
    config = manifest['mac']['service']
    entry = governance.registered(prefix)[0]
    if kind == arrival_extension.EVENT:
        _, _, current = productive_regeneration.context(config, prefix)
    elif kind == arrival_regeneration.KIND:
        _, scope, current = arrival_regeneration.context(config, prefix)
    else:
        raise ValueError('ARRIVAL_REQUEST_KIND')
    body = dict(source=manifest['source'], stream='recovery', actor='2',
                parent=dict(seq=len(prefix), head=prefix[-1][2]),
                member=governance.member(config, prefix, '2'),
                executor=entry['result']['key'], cut=current['cut'], epoch=current['version'])
    if kind == arrival_extension.EVENT:
        body.update(feature=arrival_extension.FEATURE,
                    certificate=digest(config['arrival_extension']))
        wanted = arrival_extension.authorization(body)
        domain = 'native-arrival-extension'
    else:
        body.update(command=command, scope=scope, unit='energy',
                    source_root=arrival_extension.ORIGIN)
        wanted = arrival_regeneration.authorization(config, body)
        domain = 'native-arrival-regeneration'
    path = directory/(label+'-owner.json')
    if path.exists():
        proof = load(path)
        if proof['body'] != wanted:
            if (directory/(label+'-request.json')).exists():
                raise ValueError('RETAIN_ORIGINAL_OWNER_AUTHORIZATION')
            path.rename(directory/('unsubmitted-owner-'+digest(proof)+'.json'))
    if not path.exists():
        owner = entry['proof']['body']['owner']
        if owner == 'mac':
            proof = sign(app_private(Path(config['ha']['owner_profile'])), domain, wanted)
        else:
            item = manifest['nodes']['c']
            code = ("import json,sys\nfrom pathlib import Path\n"
                    "sys.path.insert(0,"+repr(item['code'])+")\n"
                    "from crypto import app_private,sign\n"
                    "print(json.dumps(sign(app_private(Path("+repr(item['home']+'/ha/owner')+")),"
                    +repr(domain)+","+repr(wanted)+")))")
            proof = json.loads(deploy.execute('c', code, manifest, 60))
        save(path, proof)
    return {**body, 'execution': proof}


def check_arrival_result(result, message, key, profile, *, recovered, native_config, prefix):
    request = message['body']
    if request.get('stream') != 'recovery':
        raise ValueError('ARRIVAL_CLIENT_STREAM_BINDING')
    if (any(result[k] != request[k] for k in ('source', 'stream', 'request_id', 'seq', 'cut', 'epoch'))
            or result['request'] != digest(message)):
        raise ValueError('ARRIVAL_RESPONSE_BINDING')
    event = result['event']
    ledger = verify(key, 'ledger', result['ledger'])
    if (ledger != event or event['request'] != message or event['source'] != request['source']
            or event.get('stream') != request['stream']):
        raise ValueError('ARRIVAL_EVENT_BINDING')
    anchor_receipt = result['anchor']
    point = anchor_receipt['body']
    binding = dict(source=request['source'], stream=request['stream'], seq=point['seq'],
                   head=result['head'], previous=point['previous'], message=result['ledger'])
    if (profile/'anchors.json').is_file():
        from quorum import verify_certificate
        verify_certificate(json.loads((profile/'anchors.json').read_text()), anchor_receipt, **binding)
    elif (profile/'anchor.json').is_file():
        verify_commit(json.loads((profile/'anchor.json').read_text()), anchor_receipt, **binding)
    else:
        raise ValueError('ARRIVAL_EXTERNAL_ANCHOR_TRUST_REQUIRED')
    if (type(point['seq']) is not int or point['seq'] != len(prefix) + 1
            or point['previous'] != (prefix[-1][2] if prefix else '0'*64)
            or ledger_hash(point['previous'], result['ledger']) != result['head']):
        raise ValueError('ARRIVAL_ANCHOR_PARENT_BINDING')
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes
    local = x509.load_pem_x509_certificate((profile/'cert.pem').read_bytes()).fingerprint(hashes.SHA256()).hex()
    governance.registration_bound(event)
    if event['type'] != message['kind'] or (not recovered and event.get('peer') != local):
        raise ValueError('ARRIVAL_EVENT_IDENTITY')
    if message['kind'] == arrival_extension.EVENT:
        result['arrival_checked'] = arrival_extension.expected(native_config, prefix, event)
    elif message['kind'] == arrival_regeneration.KIND:
        result['arrival_checked'] = arrival_regeneration.expected(native_config, prefix, event)
    else:
        raise ValueError('ARRIVAL_CLIENT_REQUEST_KIND')
    return result


def observe(box, manifest, directory, port, label, kind=None, command=None, lookup=None,
            expected_prefix=None):
    config = manifest['mac']['service']
    profile = Path(config['pki'])/'auditor2'
    journal = ApplicationJournal(directory/'applications.jsonl', app_private(profile),
                                 config['source'], config['stream'], 'client')
    attempt = journal.start(dict(label=label, actor='2', lookup=lookup))
    times = dict(connect_start_ns=time.monotonic_ns())
    problem = None
    try:
        with connect(profile, port) as connection:
            connection.settimeout(response_timeout(config))
            times['connected_ns'] = time.monotonic_ns()
            uri, fingerprint, key = peer(connection)
            if uri != 'urn:public-audit:server' or fingerprint != config['registry']['server']['fingerprint']:
                raise ValueError('ARRIVAL_SERVER_IDENTITY')
            tls, cipher = connection.version(), connection.cipher()[0]
            attempt.add('tls', dict(peer=dict(uri=uri, fingerprint=fingerprint,
                                app=key.public_bytes_raw().hex()), tls=tls, cipher=cipher))
            challenge = receive(connection)
            issued = verify(key, 'challenge', challenge)
            attempt.add('challenge', challenge)
            times['challenge_received_ns'] = time.monotonic_ns()
            if lookup:
                request = sign(app_private(profile), 'lookup',
                               {**issued, 'lookup_id': lookup, 'request_id': secrets.token_hex(16)})
            else:
                request_path = directory/(label+'-request.json')
                if request_path.exists():
                    raise ValueError('RECOVER_ORIGINAL_REQUEST_BY_LOOKUP')
                deadline = time.monotonic() + 20
                while True:
                    prefix = continuous.rows(manifest)
                    if expected_prefix is not None and prefix != expected_prefix:
                        raise ValueError('ARRIVAL_REQUEST_PARENT_MOVED')
                    try:
                        current = current_state(config, prefix, kind)
                    except ValueError as error:
                        if str(error) not in {'ARRIVAL_NOT_COMMITTED', 'PRODUCTIVE_NOT_COMMITTED'} or time.monotonic() >= deadline:
                            raise
                        time.sleep(.1)
                        continue
                    if (current['cut'], current['version']) == (issued['cut'], issued['epoch']):
                        break
                    if time.monotonic() >= deadline:
                        raise ValueError('ARRIVAL_HEAD_NOT_READY')
                    time.sleep(.1)
                body = authorize(box, manifest, prefix, kind, command, directory, label)
                if (body['cut'], body['epoch']) != (issued['cut'], issued['epoch']):
                    raise ValueError('ARRIVAL_HEAD_NOT_READY')
                request = sign(app_private(profile), kind, {**issued, **body,
                               'request_id': secrets.token_hex(16)})
            save(directory/(label+'-request.json'), request)
            save(directory/(label+'-challenge.json'), challenge)
            times['request_sent_ns'] = time.monotonic_ns()
            attempt.add('send-intent', request)
            send(connection, request)
            attempt.add('sent', dict(request=digest(request)))
            try:
                response = receive(connection)
                verify(key, response['kind'], response)
                attempt.add('response', response)
            except (OSError, EOFError) as error:
                response = {'transport_error': type(error).__name__}
                attempt.add('transport-error', response)
            times['response_received_ns'] = time.monotonic_ns()
            observation = sign(app_private(profile), 'online-client-observation',
                dict(peer=dict(uri=uri, fingerprint=fingerprint, app=key.public_bytes_raw().hex()),
                     tls=tls, cipher=cipher, challenge=challenge, request=request,
                     response=response, times=times))
            save(directory/(label+'-observation.json'), observation)
            return observation
    except BaseException as error:
        problem = type(error).__name__
        raise
    finally:
        attempt.close(problem)


def submit(box, manifest, directory, port, label, kind, command, prefix):
    config = manifest['mac']['service']
    request_path = directory/(label+'-request.json')
    result_path = directory/(label+'-result.json')
    profile = Path(config['pki'])/'auditor2'
    key = public_key(config['registry']['server'])

    def validate_saved(result, request):
        rows = continuous.rows(manifest)
        sequence = result['anchor']['body']['seq']
        if sequence > len(rows) or rows[sequence-1][3] != canonical(result['ledger']).decode():
            raise ValueError('ARRIVAL_PAID_RESULT_NOT_IN_JOURNAL')
        if sequence != len(prefix)+1:
            raise ValueError('ARRIVAL_PAID_RESULT_SEQUENCE_CHANGED')
        if result['event']['request'] != request:
            raise ValueError('ARRIVAL_PAID_REQUEST_CHANGED')
        check_arrival_result(result, request, key, profile, recovered=False,
                             native_config=config, prefix=prefix)
        return rows

    if result_path.exists():
        result = load(result_path)
        request = load(request_path)
        rows = validate_saved(result, request)
    else:
        if request_path.exists():
            request = load(request_path)
            observation = observe(box, manifest, directory, port,
                                  label+'-recover-'+secrets.token_hex(4), lookup=request['body']['request_id'])
        else:
            observation = observe(box, manifest, directory, port, label, kind, command,
                                  expected_prefix=prefix)
        request = load(request_path)
        response = observation['body']['response']
        if response.get('kind') == 'response':
            result = verify(key, 'response', response)
        elif response.get('kind') == 'lookup-response':
            envelope = verify(key, 'lookup-response', response)
            lookup_request=observation['body']['request']
            if (envelope['request'] != digest(lookup_request)
                    or lookup_request['body'].get('lookup_id') != request['body']['request_id']):
                raise ValueError('ARRIVAL_LOOKUP_BINDING')
            result = envelope['result']
        elif response.get('kind') == 'error':
            raise ValueError('SIGNED_ARRIVAL_REJECTION:'+verify(key, 'error', response)['code'])
        else:
            raise ValueError('ARRIVAL_OUTCOME_UNKNOWN_RETAIN_ORIGINAL_REQUEST')
        if result['anchor']['body']['seq'] != len(prefix)+1:
            raise ValueError('ARRIVAL_RESULT_SEQUENCE')
        checked = check_arrival_result(result, request, key, profile, recovered=False,
                                       native_config=config, prefix=prefix)
        save(result_path, checked)
        result = checked
        rows = continuous.rows(manifest)

    for index in range(2):
        lookup_path = directory/(label+'-lookup-'+str(index)+'-observation.json')
        if lookup_path.exists():
            value = load(lookup_path)
        else:
            value = observe(box, manifest, directory, port, label+'-lookup-'+str(index),
                            lookup=request['body']['request_id'])
            save(lookup_path, value)
        reply = verify(key, 'lookup-response', value['body']['response'])
        lookup_request=value['body']['request']
        if (reply.get('request') != digest(lookup_request)
                or lookup_request['body'].get('lookup_id') != request['body']['request_id']
                or reply['result']['ledger'] != result['ledger']):
            raise ValueError('ARRIVAL_IDEMPOTENT_LOOKUP')
    row = [result['anchor']['body']['seq'], result['anchor']['body']['previous'],
           result['anchor']['body']['head'], canonical(result['ledger']).decode()]
    if rows[:len(prefix)] != prefix:
        raise ValueError('ARRIVAL_PARENT_PREFIX_CHANGED')
    if len(rows) > len(prefix) and rows[len(prefix)] != row:
        raise ValueError('ARRIVAL_PAID_ROW_CHANGED')
    if result['event']['request']['body']['parent'] != dict(seq=len(prefix), head=prefix[-1][2]):
        raise ValueError('ARRIVAL_PARENT_BINDING')
    return result, row


def commands():
    return arrival_readiness.commands() if hasattr(arrival_readiness, 'commands') else arrival_readiness.events()


def non_executable(stat, status):
    if status==1 and not stat.strip():return 'gone'
    if status==0 and stat.strip().startswith('Z'):return 'zombie'
    raise ValueError('ARRIVAL_UNCLASSIFIED_PROCESS_WITHOUT_BIRTH')


def executable_inventories(box, manifest, inventories):
    """Retain dead-process evidence without treating empty stamps as identities."""
    normalized=[]
    for batch in inventories:
        result={}
        for member,signed in batch.items():
            entry=manifest['nodes'][member] if member!='a' else None
            home=entry['home'] if entry else str(box/'local-anchor')
            code=entry['code'] if entry else str(NETWORK)
            script='import json,subprocess,sys\nfrom pathlib import Path\nsys.path.insert(0,'+repr(code)+')\nfrom crypto import app_private,digest,sign,verify\nfrom anchor import public_key\n'+inspect.getsource(non_executable)+f'''
s={signed!r};r=verify(public_key({manifest['trust']['members'][member]!r}),'public-epoch-inventory',s)
assert r['member']=={member!r} and r['source']=={manifest['source']!r}
excluded=[];processes=[]
for p in r['processes']:
 if p['birth']:processes.append(p);continue
 state=subprocess.run(['ps','-p',str(p['pid']),'-o','stat='],capture_output=True,text=True)
 classification=non_executable(state.stdout,state.returncode)
 excluded.append(dict(process=p,classification=classification,stat=state.stdout.strip(),status=state.returncode))
print(json.dumps(sign(app_private(Path({home!r})/'pki/anchor'),'public-epoch-inventory',
 {{**r,'processes':processes,'non_executable':excluded,'original_inventory':digest(s)}})))
'''
            result[member]=json.loads(deploy.execute(member,script,manifest,60))
        normalized.append(result)
    return normalized


def finalize(manifest, directory, initial, results, rows, owner, word):
    if len(results) != 9 or len(rows) != 77 or rows[:len(initial)] != initial:
        raise ValueError('ARRIVAL_EXPECTED_68_PLUS_9_ROWS')
    if len(word) != 8:
        raise ValueError('ARRIVAL_EXPECTED_EIGHT_COMMANDS')
    actual_commands = [result['event']['request']['body']['command'] for result in results[1:]]
    if canonical(actual_commands) != canonical(word):
        raise ValueError('ARRIVAL_READINESS_WORD_CHANGED')
    if results[0]['event']['type'] != arrival_extension.EVENT:
        raise ValueError('ARRIVAL_CONTROL_EVENT_MISSING')
    if any(result['event']['type'] != arrival_regeneration.KIND for result in results[1:]):
        raise ValueError('ARRIVAL_SUCCESSOR_KIND')
    value, scope, current = arrival_regeneration.context(manifest['mac']['service'], rows)
    save(directory/'events.json', rows)
    save(directory/'source-input.json', value)
    save(directory/'after.json', dict(rows=rows, current=current, scope=scope))
    complete = dict(events=len(rows), original_events=len(initial), head=rows[-1][2],
                    control_events=1, arrival_requests=8, lookups=18, owner=owner,
                    current=current, scope=scope, physical_reboots=0)
    save(directory/'public-complete.json', complete)
    print('ACTUAL ARRIVAL PASS: original 68 + admission + eight source-native successors; two lookups per request', flush=True)


def run(box):
    lock = (box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX|fcntl.LOCK_NB)
    home = deploy.location(box)
    directory = home/'actual'
    directory.mkdir(exist_ok=True)
    manifest = deploy.load(box/'ha/deployment.json')
    config = manifest['mac']['service']
    admission_receipt = deploy.load(home/'admission.json')
    certificate = admission_receipt['certificate']
    point = arrival_extension.admission(config, certificate)
    if (manifest.get('arrival', {}).get('admission') != digest(certificate)
            or admission_receipt.get('original_prefix') != point['prefix']):
        raise ValueError('ARRIVAL_READY_RECEIPT_NOT_INSTALLED')
    current_rows = continuous.rows(manifest)
    before_path = directory/'before.json'
    if not before_path.exists():
        if len(current_rows) != 68 or dict(seq=len(current_rows), head=current_rows[-1][2]) != point['prefix']:
            raise ValueError('ARRIVAL_ACTIVATION_PARENT_NOT_CURRENT_68')
        productive_extension.require(config, current_rows)
        if arrival_extension.committed(config, current_rows) is not None:
            raise ValueError('ARRIVAL_ALREADY_ACTIVATED')
        save(before_path, current_rows)
    initial = load(before_path)
    if len(initial) != 68 or current_rows[:len(initial)] != initial:
        raise ValueError('ARRIVAL_ORIGINAL_PREFIX_CHANGED')
    owner, _ = runtime_observer.wait_runtime(box, manifest)
    word = commands()
    probe = arrival_readiness.probe(config, initial)
    if len(word) != 8 or canonical(word) != canonical(probe['events']):
        raise ValueError('ARRIVAL_PROBE_WORD_BINDING')
    labels = ['arrival-admission'] + ['arrival-'+str(index) for index in range(8)]
    kinds = [arrival_extension.EVENT] + [arrival_regeneration.KIND for _ in word]
    payloads = [None] + word
    relay, thread = relay_for(box, manifest, owner)
    tap_path = directory/('tls-'+str(len(list(directory.glob('tls-*.jsonl.gz')))+1)+'.jsonl.gz')
    tap = Tap(relay.server_address[1], tap_path, timeout=max(240, response_timeout(config)))
    results=[];rows=initial
    try:
        for label, kind, command in zip(labels, kinds, payloads, strict=True):
            if rows[:len(initial)] != initial:
                raise ValueError('ARRIVAL_ORIGINAL_PREFIX_CHANGED')
            current=continuous.rows(manifest)
            if current[:len(rows)] != rows or len(current) > 77:
                raise ValueError('ARRIVAL_UNEXPECTED_PAID_SUFFIX')
            result,row=submit(box,manifest,directory,tap.port,label,kind,command,rows)
            results.append(result)
            if row[0] != len(rows)+1 or row[1] != rows[-1][2]:
                raise ValueError('ARRIVAL_APPEND_PARENT')
            rows=rows+[row]
            visible=continuous.rows(manifest)
            if visible[:len(rows)]!=rows:
                raise ValueError('ARRIVAL_VISIBLE_PREFIX_CHANGED')
            target=rows if len(visible)<len(rows) else visible
            runtime_observer.wait_prefix(box,manifest,target)
            latest=continuous.rows(manifest)
            if latest!=target or latest[:len(rows)]!=rows:
                raise ValueError('ARRIVAL_FOUR_ANCHOR_PREFIX_NOT_CAUGHT_UP')
        finalize(manifest,directory,initial,results,rows,owner,word)
    finally:
        tap.close()
        relay.shutdown();relay.server_close();thread.join(3)
        governance.close_readers();energy.close_readers()


def close_and_audit(box):
    lock=(box/'ha/live-timing/operation.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    home=deploy.location(box);directory=home/'actual';manifest=deploy.load(box/'ha/deployment.json')
    if (directory/'owner-accepted.json').exists():
        if not (directory/'resume-started.json').exists():
            continuous.resume_runtime(box,manifest)
            save(directory/'resume-started.json',dict(at=time.time(),head=load(directory/'public-complete.json')['head']))
        runtime_observer.wait_runtime(box,manifest)
        save(directory/'resumed.json',dict(at=time.time(),states=continuous.epoch.states(box,manifest)))
        return
    if (directory/'resume-started.json').exists():
        archive=directory/('audit-failed-'+str(time.time_ns()));archive.mkdir()
        for name in ('audit-barrier.json','inventories.json','raw-inventories.json','closed.json',
                     'resume-started.json','resumed.json','private-one.json','private-one.stderr',
                     'private-one-exit.json','private-two.json','private-two.stderr','private-two-exit.json'):
            path=directory/name
            if path.exists():path.rename(archive/name)
    complete=load(directory/'public-complete.json') if (directory/'public-complete.json').exists() else None
    if not complete or complete.get('events')!=77 or complete.get('physical_reboots')!=0:
        raise ValueError('ACTUAL_ARRIVAL_NOT_COMPLETE')
    rows=continuous.rows(manifest)
    if len(rows)!=77 or rows[-1][2]!=complete['head']:
        raise ValueError('ACTUAL_ARRIVAL_JOURNAL_CHANGED')
    save(directory/'events.json',rows)
    frozen={};transition=False
    try:
        barrier_path=directory/'audit-barrier.json'
        if barrier_path.exists():
            frozen=load(barrier_path)
        for owner in ('spark','mac'):
            if owner not in frozen:
                frozen[owner]=deploy.roll.freeze_writer(box,manifest,owner)
                save(barrier_path,frozen)
        if set(frozen)!={'spark','mac'}:
            raise ValueError('ARRIVAL_AUDIT_BARRIER_RECEIPT')
        inventory_path=directory/'inventories.json'
        if inventory_path.exists():
            prior=load(inventory_path)
        else:
            inventory={name:continuous.epoch.inventory(box,manifest,name) for name in 'abcd'}
            save(directory/'raw-inventories.json',[inventory])
            prior=executable_inventories(box,manifest,[inventory])
            save(inventory_path,prior)
        transition=True
        for owner in ('spark','mac'):
            deploy.prior.retire_writer(box,manifest,owner,frozen[owner])
        if not (directory/'closed.json').exists():
            continuous.epoch.stop_anchors(manifest)
            save(directory/'closed.json',continuous.epoch.close_inventory(box,manifest,prior))
        for owner,member in [('mac','a'),('spark','c')]:
            journal=manifest[owner]['service']['online_privacy']['journal']
            for name,path in [('boundary',journal),('applications',journal+'.applications.jsonl')]:
                target=directory/(owner+'-'+name+'.jsonl')
                raw=deploy.execute(member,'from pathlib import Path\nprint(Path('+repr(path)+').read_text(),end="")',manifest,120)
                if target.exists() and target.read_text()!=raw:
                    raise ValueError('ARRIVAL_PRIVATE_AUDIT_SNAPSHOT_CHANGED')
                if not target.exists():target.write_text(raw)
        subprocess=__import__('subprocess')
        subprocess.run([sys.executable,str(Path(__file__).with_name('public-arrival-live-check.py')),
                        str(box),'--closed'],check=True)
    finally:
        if transition:
            for owner,record in frozen.items():
                deploy.prior.retire_writer(box,manifest,owner,record)
            continuous.resume_runtime(box,manifest)
            save(directory/'resume-started.json',dict(at=time.time(),head=rows[-1][2]))
        else:
            for owner,record in frozen.items():
                deploy.roll.spare.writer_signal(box,manifest,owner,'SIGCONT',record)
    runtime_observer.wait_runtime(box,manifest)
    save(directory/'resumed.json',dict(at=time.time(),states=continuous.epoch.states(box,manifest)))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('box',type=Path);parser.add_argument('--close',action='store_true')
    args=parser.parse_args()
    if args.close:close_and_audit(args.box.resolve())
    else:run(args.box.resolve())
