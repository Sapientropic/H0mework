"""Submit the original owner-approved successor once; thereafter only look it up."""
import argparse
from copy import deepcopy
from fractions import Fraction
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import secrets
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT/'Verification/public-audit/network'))
import donor_arrival_live as donor
import donor_owner_continuation as owner
from donor_result_codec import decode_body, enabled
from anchor import ledger_hash, public_key
from crypto import app_private, canonical, connect, digest, peer, receive, send, sign, verify
from quorum import verify_certificate
from recovery_loop import save
import supply_disposition
from productive_owner_request import history


def module(name, file):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(file))
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value


original = module('supply_original_client', 'public-arrival-actual.py')
load = original.load


def once(path, value):
    raw = canonical(value)
    if path.exists():
        if path.read_bytes() != raw: raise ValueError('SUPPLY_CLIENT_ORIGINAL_ARTIFACT_CHANGED')
    else:
        with path.open('xb') as stream:
            stream.write(raw); stream.flush(); os.fsync(stream.fileno())


def checked(config, rows, message, result):
    body = message['body']; event = result['event']
    actors, _, _ = history(config, rows)
    verify(public_key(actors[body['actor']]), donor.ACTION, message)
    if event['peer'] != actors[body['actor']]['fingerprint']:
        raise ValueError('SUPPLY_CLIENT_ACTUAL_ACTOR')
    if (verify(public_key(config['registry']['server']), 'ledger', result['ledger']) != event or
            event['request'] != message or event['type'] != donor.ACTION or
            result['request'] != digest(message) or
            any(result[k] != body[k] for k in ('source', 'stream', 'request_id', 'seq', 'cut', 'epoch'))):
        raise ValueError('SUPPLY_CLIENT_RESPONSE_BINDING')
    point = result['anchor']['body']
    verify_certificate(config['anchors']['trust'], result['anchor'], source=body['source'], stream=body['stream'],
        seq=point['seq'], previous=point['previous'], head=result['head'], message=result['ledger'])
    if (point['seq'] != len(rows)+1 or point['previous'] != rows[-1][2] or
            ledger_hash(point['previous'], result['ledger']) != result['head']):
        raise ValueError('SUPPLY_CLIENT_PARENT')
    donor.expected(config, rows, event, native=False)
    previous = None
    for row in reversed(rows):
        native = json.loads(row[3])['body'].get('native', {})
        if 'next' in native:
            previous = native['next']; break
        if (set(native) != {'source_root','metadata','status','message'} or native['status'] != 'ERROR' or
                native['metadata'].get('kind') != 'donate' or native['metadata'].get('quantity') == 6):
            raise ValueError('SUPPLY_CLIENT_UNEXPLAINED_PARENT_STATE')
    if previous is None: raise ValueError('SUPPLY_CLIENT_MISSING_PARENT_STATE')
    prepared = deepcopy(previous)
    prepared['clock'] = str(Fraction(prepared['clock'])+1); prepared['round'] += 1
    if canonical(event['native']['before']) != canonical(prepared):
        raise ValueError('SUPPLY_CLIENT_ACTUAL_BEFORE')
    if event['native']['before']['claims'] != event['native']['next']['claims']:
        raise ValueError('SUPPLY_CLIENT_ORIGINAL_CLAIMS_CHANGED')
    if not event['native']['oldSpent'] or event['native']['oldSourceNext']['available'] != '0':
        raise ValueError('SUPPLY_CLIENT_OLD_SOURCE_REISSUED')
    if event['native']['status'] == 'SUPPLIED':
        quantity = str(body['command']['quantity']); point = config['donor_admission']['point']
        rows_ = event['native']['rows']
        if (len(rows_) != 1 or rows_[0]['accepted'] is not True or
                rows_[0]['debit'] != [[point['donor'], point['unit'], quantity]] or
                rows_[0]['credit'] != [[point['recipient'], point['unit'], quantity]]):
            raise ValueError('SUPPLY_CLIENT_NATIVE_PAYMENT')
        for stock in prepared['stock']:
            if stock[:2] == [point['recipient'], point['unit']]:
                stock[2] = str(Fraction(stock[2])+body['command']['quantity'])
    elif event['native']['rows']:
        raise ValueError('SUPPLY_CLIENT_REFUSAL_IS_NOT_PAYMENT')
    prepared['clock'] = str(Fraction(prepared['clock'])+1); prepared['round'] += 1
    if canonical(event['native']['next']) != canonical(prepared):
        raise ValueError('SUPPLY_CLIENT_ACTUAL_NEXT')
    return dict(status=event['native']['status'], request_id=body['request_id'], seq=result['anchor']['body']['seq'],
                head=result['head'], old_source_spent=True, original_claims_retained=True)


def run(box, work, revision):
    directory = work/'actual'; directory.mkdir(exist_ok=True)
    roll = work/'roll'/revision
    installed = load(roll/'installed.json')
    if installed['protocol'] != revision: raise ValueError('SUPPLY_CLIENT_INSTALLED_PROFILE')
    with (box/'ha/live-timing/operation.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        manifest = load(box/'ha/deployment.json'); config = manifest['mac']['service']
        if manifest['release'] != revision: raise ValueError('SUPPLY_CLIENT_PROFILE_MOVED')
        request_path = directory/'original-request.json'; rows_path = directory/'parent.json'
        if rows_path.exists():
            rows = load(rows_path)
        else:
            rows = original.continuous.rows(manifest)
            if donor.prefix(rows) != load(work/'prepared.json')['prefix']: raise ValueError('SUPPLY_CLIENT_PARENT_MOVED')
            once(rows_path, rows)
        current_owner, _ = original.runtime_observer.wait_runtime(box, manifest)
        relay, thread = original.relay_for(box, manifest, current_owner)
        tap = original.Tap(relay.server_address[1], directory/('tls-'+secrets.token_hex(8)+'.jsonl.gz'),
                           timeout=original.response_timeout(config))
        profile = Path(config['pki'])/'auditor1'; key = public_key(config['registry']['server'])
        admitted = enabled(config); lookup = request_path.exists()
        label = ('lookup-' if lookup else 'submit-')+secrets.token_hex(6)
        started = time.monotonic_ns()
        try:
            with connect(profile, tap.port) as connection:
                connection.settimeout(original.response_timeout(config))
                uri, fingerprint, remote_key = peer(connection)
                if (uri != 'urn:public-audit:server' or fingerprint != config['registry']['server']['fingerprint'] or
                        remote_key.public_bytes_raw().hex() != config['registry']['server']['app']):
                    raise ValueError('SUPPLY_CLIENT_SERVER_IDENTITY')
                challenge = receive(connection); issued = verify(key, 'challenge', challenge)
                if lookup:
                    request = sign(app_private(profile), 'lookup', dict(issued, lookup_id=load(request_path)['body']['request_id'],
                                                                      request_id=secrets.token_hex(16)))
                else:
                    intent = load(work/'intent.json'); permission = load(work/'owner-packet.json')['permission']
                    body = owner.transport_body(config, rows, intent, permission, issued)
                    request = sign(app_private(profile), donor.ACTION, body)
                    event = dict(type=donor.ACTION, source=body['source'], stream=body['stream'], request=request,
                                 peer=config['registry']['auditor1']['fingerprint'], scope=body['scope'])
                    if donor.argument(config, rows, event) != load(work/'authorized-source-input.json'):
                        raise ValueError('SUPPLY_CLIENT_ORIGINAL_INPUT_CHANGED')
                    once(request_path, request); once(directory/'original-challenge.json', challenge)
                once(directory/(label+'-request.json'), request)
                save(directory/(label+'-send-started.json'), dict(at=time.time(), request=digest(request),
                    original_request_id=load(request_path)['body']['request_id'], economic=not lookup))
                send(connection, request)
                try:
                    response = receive(connection)
                except (OSError, EOFError) as problem:
                    save(directory/(label+'-unknown.json'), dict(error=type(problem).__name__, at=time.time()))
                    raise ValueError('SUPPLY_OUTCOME_UNKNOWN_USE_ORIGINAL_ID_LOOKUP') from problem
                raw = verify(key, response['kind'], response)
                body = decode_body(response['kind'], raw, admitted=admitted)
                observation = sign(app_private(profile), 'online-client-observation', dict(
                    peer=dict(uri=uri,fingerprint=fingerprint,app=remote_key.public_bytes_raw().hex()),
                    tls=connection.version(), cipher=connection.cipher()[0], challenge=challenge, request=request,
                    response=response, times=dict(started_ns=started, received_ns=time.monotonic_ns())))
                once(directory/(label+'-observation.json'), observation)
                if response['kind'] == 'error': raise ValueError('SIGNED_SUPPLY_REJECTION:'+body['code'])
                if lookup:
                    if response['kind'] != 'lookup-response' or body['request'] != digest(request):
                        raise ValueError('SUPPLY_CLIENT_LOOKUP_BINDING')
                    result = body['result']
                else:
                    if response['kind'] != 'response': raise ValueError('SUPPLY_CLIENT_RESPONSE_KIND')
                    result = body
                summary = checked(config, rows, load(request_path), result)
                if (directory/'result.json').exists():
                    if load(directory/'result.json')['ledger'] != result['ledger']:
                        raise ValueError('SUPPLY_CLIENT_RESULT_FORK')
                else:once(directory/'result.json', result)
                once(directory/'accepted.json', summary)
                save(directory/(label+'-accepted.json'), summary)
                print(json.dumps(dict(exit=0, lookup_only=lookup, **summary)))
        finally:
            tap.close(); relay.shutdown(); relay.server_close(); thread.join(3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--box', type=Path, default=ROOT/'.agents/tmp/public-recovery-20261103/live')
    parser.add_argument('--work', type=Path, required=True); parser.add_argument('--revision', required=True)
    args = parser.parse_args(); run(args.box.resolve(), args.work.resolve(), args.revision)


if __name__ == '__main__':
    main()
