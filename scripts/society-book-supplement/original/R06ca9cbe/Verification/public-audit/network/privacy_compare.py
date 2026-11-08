"""Independent verifier: complete signed frames, source replays and clock-offset witnesses.

No producer PASS field or comparison routine is consumed. Independent samples
are not equated. Each complete response is bound to both original histories;
raw clocks are retained and checked, not removed by a comparison projection.
"""
from __future__ import annotations

import base64
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess

from cryptography import x509
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, ed25519
from cryptography.x509.oid import ObjectIdentifier

DOMAIN=b'public-source-audit/network/v1\x00'
SOURCE='public-source-audit/privacy-readout/v1'
APP_KEY=ObjectIdentifier('1.3.6.1.4.1.57264.2026.1')
ROOT=Path(__file__).resolve().parents[3]
PREFIX='SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Privacy/'


def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode()
def digest(x):return hashlib.sha256(canonical(x)).hexdigest()
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def load(path):
    if str(path).endswith('.gz'):
        with gzip.open(path,'rt')as stream:return json.load(stream)
    return json.loads(Path(path).read_text())
def lines(path):
    if str(path).endswith('.gz'):
        with gzip.open(path,'rt')as stream:return [json.loads(line)for line in stream]
    return [json.loads(line)for line in Path(path).read_text().splitlines()]


def signed(key,kind,message):
    assert set(message)=={'kind','body','signature'} and message['kind']==kind,'MESSAGE_SCHEMA'
    ed25519.Ed25519PublicKey.from_public_bytes(bytes.fromhex(key)).verify(
        base64.b64decode(message['signature'],validate=True),DOMAIN+kind.encode()+b'\x00'+canonical(message['body']))
    return message['body']


def frame(message):
    assert len(canonical(message))==65532,'FIXED_FRAME_BYTES'
    pad=message['body']['padding']
    assert isinstance(pad,str)and set(pad)<={'0'},'PADDING'


def public_keys(directory):
    registry=load(directory/'registry.json')
    ca=x509.load_pem_x509_certificate((directory/'ca.pem').read_bytes())
    for label,entry in registry.items():
        cert=x509.load_pem_x509_certificate((directory/(label+'.pem')).read_bytes())
        ca.public_key().verify(cert.signature,cert.tbs_certificate_bytes,ec.ECDSA(cert.signature_hash_algorithm))
        assert cert.issuer==ca.subject
        uris=cert.extensions.get_extension_for_class(x509.SubjectAlternativeName).value.get_values_for_type(x509.UniformResourceIdentifier)
        assert uris==['urn:public-audit:'+entry['actor']]
        assert cert.fingerprint(hashes.SHA256()).hex()==entry['fingerprint']
        assert cert.extensions.get_extension_for_oid(APP_KEY).value.value.hex()==entry['app']
    return registry


def check_pair(client,server,registry,descriptor,expected):
    c=signed(registry['auditor2']['app'],'privacy-client-observation',client)
    s=signed(registry['server']['app'],'privacy-measurement',server)
    assert set(c)=={'peer','challenge','request','response','times','tls','cipher'},'CLIENT_FIELDS'
    assert set(s)=={'source','index','previous','peer','challenge','request','response','sent_ns','observed_end_ns'},'MEASUREMENT_FIELDS'
    assert c['tls']=='TLSv1.3' and s['source']==SOURCE
    assert c['peer']==dict(uri='urn:public-audit:server',fingerprint=registry['server']['fingerprint'],app=registry['server']['app'])
    assert s['peer']==dict(uri='urn:public-audit:2',fingerprint=registry['auditor2']['fingerprint'],app=registry['auditor2']['app'])
    for key in ('challenge','request','response'):
        assert c[key]==s[key],('TRANSCRIPT_BINDING',key)
        frame(c[key])
    challenge=signed(registry['server']['app'],'privacy-challenge',c['challenge'])
    assert set(challenge)=={'source','actor','peer','descriptor','nonce','issued_ns','expires_ns','padding'},'CHALLENGE_FIELDS'
    assert challenge['source']==SOURCE and challenge['actor']=='urn:public-audit:2'
    assert challenge['descriptor']==descriptor and challenge['peer']==registry['auditor2']['fingerprint'],'DESCRIPTOR_OR_PEER'
    assert len(challenge['nonce'])==64 and all(x in '0123456789abcdef'for x in challenge['nonce'])
    assert challenge['expires_ns']-challenge['issued_ns']==30_000_000_000
    r=c['request']['body']
    assert set(r)=={'source','actor','challenge','request_id','release_after_ms','input','padding'},'REQUEST_FIELDS'
    try:
        signed(registry['auditor2']['app'],'privacy-request',c['request'])
    except Exception:
        refusal='REQUEST_SIGNATURE'
    else:
        if r['challenge']!=digest(c['challenge']):refusal='CHALLENGE_BINDING'
        elif 'privateLarger'in r['input']:refusal='SOURCE_INPUT_FIELDS'
        else:refusal=None
    response=signed(registry['server']['app'],'privacy-response',c['response'])
    fields={'source','descriptor','challenge','request','actor','native','issued_ns','received_ns','work_start_ns',
            'work_done_ns','release_ns','send_start_ns','padding'}
    assert set(response)==fields,'RESPONSE_FIELDS'
    assert response['source']==SOURCE and response['descriptor']==descriptor,'RESPONSE_DESCRIPTOR'
    assert response['challenge']==digest(c['challenge'])and response['request']==digest(c['request']),'REQUEST_BINDING'
    assert response['actor']==r['actor']==challenge['actor'],'ACTOR_BINDING'
    assert response['issued_ns']==challenge['issued_ns']
    issued,received,done,sending=[response[k]for k in ('issued_ns','received_ns','work_done_ns','send_start_ns')]
    assert all(type(x)is int for x in (issued,received,done,sending,s['sent_ns'],s['observed_end_ns']))
    assert issued<=received<=done<=sending<=s['sent_ns']<=s['observed_end_ns'],'SERVER_CLOCK_ORDER'
    assert received<=challenge['expires_ns'],'EXPIRY'
    t=c['times']
    names=['connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns']
    assert set(t)==set(names)
    assert all(type(t[k])is int for k in names)
    assert all(t[a]<=t[b]for a,b in zip(names,names[1:])),'CLIENT_CLOCK_ORDER'
    # Server minus client clock offset consistent with both directions of the
    # actual nonce-bound exchange. This includes raw timing, not bucket equality.
    lower=max(issued-t['challenge_received_ns'],sending-t['response_received_ns'])
    upper=received-t['request_sent_ns']
    assert lower<=upper,'NO_CLOCK_OFFSET_WITNESS'
    # These deployments run on this host, so the clocks also have the known zero offset.
    assert lower<=0<=upper,'LOCAL_MONOTONIC_CLOCK_MISMATCH'
    if response['work_start_ns']is not None:
        assert received<=response['work_start_ns']<=done
        assert response['release_ns']==received+r['release_after_ms']*1_000_000
        assert sending>=response['release_ns'],'EARLY_RELEASE'
    if expected is not None:assert response['native']==expected,'ORIGINAL_SOURCE_FULL_VALUE'
    if refusal is not None:assert response['native']=={'error':refusal},'PROTOCOL_REFUSAL'
    return r['input'],response['native'],dict(offset_min_ns=lower,offset_max_ns=upper,
        client_elapsed_ns=t['response_received_ns']-t['connect_start_ns'],
        source_elapsed_ns=done-(response['work_start_ns']or done),
        release_late_ns=(sending-response['release_ns'])if response['release_ns']is not None else None)


def audit(run,out):
    out.mkdir(parents=True,exist_ok=False)
    actual=run/'actual';receipt=load(actual/'accepted.json');build=load(run/'build.json')
    descriptor=load(actual/'descriptor.json')
    assert sha(ROOT/'Verification/public-audit/network/privacy_worker_check.py')==build['worker_check_sha256']
    from privacy_worker_check import check
    assert check()==['timeout','partial','bad-json']
    for filename,expected in receipt['files'].items():assert sha(actual/filename)==expected,('RECEIPT_BYTES',filename)
    for filename,expected in receipt['source_inputs'].items():assert sha(filename)==expected,('SOURCE_BYTES',filename)
    assert digest(descriptor)==receipt['descriptor']
    assert descriptor['source_inputs']=={str(Path(path).relative_to(ROOT)):value for path,value in receipt['source_inputs'].items()}
    assert all(not Path(path).is_absolute() for path in descriptor['source_inputs'])
    assert sha(ROOT/'Lean/scripts/verification/public-network-privacy-check.py')==build['producer_sha256']
    assert sha(receipt['lean'])==descriptor['compiler_sha256']
    baseline=Path(receipt['baseline']);old=load(baseline/'accepted.json')
    assert sha(baseline/'accepted.json')==descriptor['original_privacy_receipt']
    for filename,expected in old['inputs'].items():assert sha(ROOT/filename)==expected
    for name,value in old['compiled_modules'].items():assert sha(run/'lib'/(PREFIX+name+'.olean'))==value
    for name,expected in build['modules'].items():assert sha(run/'lib'/(PREFIX+name+'.olean'))==expected
    requests=lines(baseline/'native-input.jsonl');answers=lines(baseline/'native.stdout')
    expected={}
    for i in range(0,44,2):
        assert answers[i]==answers[i+1]
        raw={k:v for k,v in requests[i].items()if k!='privateLarger'}
        expected[digest(raw)]=(raw,answers[i])
    inputs=load(actual/'inputs.json');assert len(inputs)==22
    all_raw={};clocks={};nonces=[];keys=[];negative=[]
    for lane in ('one','two'):
        directory=actual/lane
        registry=public_keys(directory/'public');keys.append(registry['server']['app'])
        config=load(directory/'config.json')
        assert config['descriptor']==descriptor
        wanted=[receipt['lean'],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run','scripts/verification/public-network-privacy-source.lean','public']
        assert config['worker']['command']==wanted
        assert config['worker']['cwd']==str(ROOT/'Lean')
        assert load(directory/'ready.json')['observed_backend_command']==' '.join(wanted)
        assert Path(config['worker']['command'][-2]).name=='public-network-privacy-source.lean'
        assert config['worker']['lean_path']==str(run/'lib')
        clients=lines(directory/'client.jsonl.gz');servers=lines(directory/'server.jsonl.gz')
        assert len(clients)==len(servers)==34
        previous='0'*64;times=[];lane_nonces=[];used=set()
        for index,(c,s)in enumerate(zip(clients,servers)):
            body=s['body'];assert body['index']==index and body['previous']==previous,'JOURNAL_CHAIN'
            previous=digest(s)
            if index<30:
                raw=inputs[index]if index<22 else inputs[int(digest(clients[index-1])[:8],16)%22]
                assert c['body']['request']['body']['input']==raw,'ADAPTIVE_STRATEGY'
                goal=expected[digest(raw)][1];all_raw[digest(raw)]=raw
            else:
                goal={'error':('REQUEST_SIGNATURE','CHALLENGE_BINDING','REPLAY','SOURCE_INPUT_FIELDS')[index-30]}
            raw,native,clock=check_pair(c,s,registry,descriptor,goal)
            if index==32:
                assert c['body']['request']['body']['request_id']in used
            elif index<30:
                assert c['body']['request']['body']['request_id']not in used
                used.add(c['body']['request']['body']['request_id'])
            times.append(clock);lane_nonces.append(c['body']['challenge']['body']['nonce'])
        assert len(set(lane_nonces))==34
        nonces.append(set(lane_nonces));clocks[lane]=times
        for control in load(directory/'controls.json.gz'):
            # Every attacker control carries valid actor/server signatures.
            signed(registry['auditor2']['app'],'privacy-client-observation',control['client'])
            signed(registry['server']['app'],'privacy-measurement',control['server'])
            signed(registry['server']['app'],'privacy-response',control['client']['body']['response'])
            try:check_pair(control['client'],control['server'],registry,descriptor,expected[digest(inputs[0])][1])
            except (AssertionError,ValueError):negative.append(lane+'/'+control['name'])
            else:raise AssertionError('SIGNED_ATTACK_ACCEPTED '+control['name'])
    assert keys[0]!=keys[1]and nonces[0].isdisjoint(nonces[1]),'INDEPENDENT_RANDOMNESS'
    assert len(negative)==12
    # Original source is replayed separately for both private histories. Reuse
    # only byte-identical whole requests; no producer verdict or narrowed field.
    raw=list(all_raw.values());encoded=''.join(canonical(x).decode()+'\n'for x in raw)
    env=os.environ.copy();env['LEAN_PATH']=str(run/'lib')
    for mode in ('actual-one','actual-two'):
        command=[receipt['lean'],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',
                 'scripts/verification/public-network-privacy-source.lean',mode]
        p=subprocess.run(command,cwd=ROOT/'Lean',env=env,input=encoded,text=True,capture_output=True,timeout=120)
        (out/(mode+'.stdout')).write_text(p.stdout);(out/(mode+'.stderr')).write_text(p.stderr)
        assert p.returncode==0 and not p.stderr,('SOURCE_REPLAY',mode,p.stderr)
        values=[json.loads(line)for line in p.stdout.splitlines()]
        assert len(values)==len(raw)
        for x,value in zip(raw,values):assert value==expected[digest(x)][1],('BOTH_ACTUAL_HISTORIES',mode)
    (out/'source-input.jsonl').write_text(encoded)
    mouths=('Wire.public_readout_is_actual','Wire.actual_branches_equal','Network.full_observation_coupling',
            'Network.public_run_is_actual','Network.all_exogenous_laws_preserve_complete_observation_distribution',
            'Network.independent_draws_have_the_same_product_law')
    namespace=PREFIX.replace('/','.')
    capsule=out/'kernel.lean';capsule.write_text('import '+namespace+'Network\n'+
                                              ''.join('#print axioms '+namespace+mouth+'\n'for mouth in mouths))
    p=subprocess.run([receipt['lean'],'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',str(capsule)],
                     cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=120)
    (out/'kernel.log').write_text(p.stdout+p.stderr)
    import re
    rows=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",p.stdout)
    assert p.returncode==0 and len(rows)==len(mouths)
    for name,axioms in rows:assert set(map(str.strip,axioms.split(',')))<={'propext','Classical.choice','Quot.sound'},name
    (out/'clock-witnesses.json').write_text(json.dumps(clocks,indent=2)+'\n')
    result=dict(observations=68,independent_deployments=2,adaptive_per_lane=8,source_pairs=len(raw),
                standard_axiom_mouths=6,signed_negative_controls=negative,
                all_clocks_retained=True,original_literal_unchanged=True,
                receipt_sha256=sha(actual/'accepted.json'),audit_source_sha256=sha(__file__),
                environment_contract='Same exogenous entropy/scheduler law; independent draws; no OS noninterference assertion')
    (out/'accepted.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('INDEPENDENT NETWORK PRIVACY PASS: 2 real deployments; 68 signed full observations; 44 actual-source replays; 12 valid-signature attacks rejected; all clock witnesses retained',flush=True)
