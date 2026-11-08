"""Auditor process: authenticates transport, then independently checks scoped source data."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import secrets
import sys

from cryptography import x509
from cryptography.hazmat.primitives import hashes

from crypto import app_private, connect, digest, peer, receive, send, sign, verify
from verify import verify_disclosure


def check_result(result, message, key, profile, *, allow_unanchored=False, recovered=False, expected_stream=None,
                 native_config=None, prefix=None):
    request = message["body"]
    pin = profile / "stream.json"
    expected_stream = expected_stream if expected_stream is not None else json.loads(pin.read_text()) if pin.is_file() else request["source"] if allow_unanchored else None
    if expected_stream is None or request.get("stream") != expected_stream:
        raise ValueError("CLIENT_STREAM_BINDING")
    if any(result[k] != request[k] for k in ("source", "stream", "request_id", "seq", "cut", "epoch")) or result["request"] != digest(message):
        raise ValueError("RESPONSE_BINDING")
    event = result["event"]
    ledger = verify(key, "ledger", result["ledger"])
    if ledger != event or event["request"] != message or event["source"] != request["source"] or event.get("stream") != request["stream"]:
        raise ValueError("EVENT_BINDING")
    trust = profile / "anchor.json"
    multi = profile / "anchors.json"
    if multi.is_file() or trust.is_file():
        from anchor import ledger_hash, verify_commit
        receipt = result["anchor"]
        point = receipt["body"]
        binding = dict(source=request["source"],stream=request["stream"],seq=point["seq"],head=result["head"],previous=point["previous"],message=result["ledger"])
        if multi.is_file():
            from quorum import verify_certificate
            verify_certificate(json.loads(multi.read_text()),receipt,**binding)
        else:
            verify_commit(json.loads(trust.read_text()),receipt,**binding)
        if type(point["seq"]) is not int or point["seq"] < 1 or ledger_hash(point["previous"],result["ledger"]) != result["head"]:
            raise ValueError("ANCHOR_LEDGER_BINDING")
    elif not allow_unanchored or "anchor" in result:
        raise ValueError("EXTERNAL_ANCHOR_TRUST_REQUIRED")
    local_fingerprint = x509.load_pem_x509_certificate((profile / "cert.pem").read_bytes()).fingerprint(hashes.SHA256()).hex()
    from governance import registration_bound
    registration_bound(event)
    if message["kind"] == "audit":
        if event["type"] != "disclosure" or not recovered and event["peer"] != local_fingerprint:
            raise ValueError("EVENT_IDENTITY")
        record = event["record"]
        if record["actor"] != int(request["actor"]) or record["cut"] != request["cut"] or record["query"] != request["query"]:
            raise ValueError("SCOPE_BINDING")
        result["checked"] = verify_disclosure(record)
        if 'registration' in event:
            if native_config is None or prefix is None:raise ValueError('NATIVE_CONTEXT_REQUIRED')
            from governance import expected
            result['native_checked']=expected(native_config,prefix,event)
    elif message['kind']=='native-response':
        if event['type']!='native-response' or not recovered and event['peer']!=local_fingerprint:
            raise ValueError('NATIVE_RESPONSE_IDENTITY')
        if native_config is None or prefix is None:raise ValueError('NATIVE_CONTEXT_REQUIRED')
        from governance import expected
        result['native_checked']=expected(native_config,prefix,event)
    elif message['kind'] in {'energy-renewal','energy-audit'}:
        if event['type']!=message['kind'] or not recovered and event['peer']!=local_fingerprint:
            raise ValueError('ENERGY_EVENT_IDENTITY')
        if native_config is None or prefix is None:raise ValueError('ENERGY_CONTEXT_REQUIRED')
        from energy import expected
        result['energy_checked']=expected(native_config,prefix,event)
    elif message['kind']=='energy-continuation':
        if native_config is None or prefix is None:raise ValueError('CONTINUATION_CONTEXT_REQUIRED')
        from continuation import expected
        result['continuation_checked']=expected(native_config,prefix,event)
    elif message['kind']=='energy-handoff':
        if native_config is None or prefix is None:raise ValueError('HANDOFF_CONTEXT_REQUIRED')
        from handoff import expected
        result['handoff_checked']=expected(native_config,prefix,event)
    elif message['kind'] in {'source-extension','energy-regeneration','material-extension','energy-material','productive-extension','energy-productive'}:
        if event['type']!=message['kind'] or not recovered and event['peer']!=local_fingerprint:
            raise ValueError('SUPPLY_EVENT_IDENTITY')
        if native_config is None or prefix is None:raise ValueError('SUPPLY_CONTEXT_REQUIRED')
        if message['kind']=='source-extension':
            from source_extension import expected
        elif message['kind']=='material-extension':
            from material_extension import expected
        elif message['kind']=='productive-extension':
            from productive_extension import expected
        elif message['kind']=='energy-productive':
            from productive_regeneration import expected
        elif message['kind']=='energy-material':
            from material_regeneration import expected
        else:
            from regeneration import expected
        result['supply_checked']=expected(native_config,prefix,event)
    elif message['kind']=='rotate':
        rotation = request["rotation"]
        if event["type"] != "rotation" or not recovered and event["old"] != local_fingerprint or event["new"] != rotation:
            raise ValueError("ROTATION_BINDING")
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
        proof = verify(Ed25519PublicKey.from_public_bytes(bytes.fromhex(rotation["app"])), "new-key", request["new_signature"])
        challenge = {field: request[field] for field in ("source","stream","actor","nonce","seq","cut","epoch","expires")}
        if proof != {"challenge":digest(challenge),"rotation":rotation}:
            raise ValueError("ROTATION_POSSESSION")
    else:raise ValueError('CLIENT_REQUEST_KIND')
    return result


def exchange(profile: Path, port: int, source: str, query: dict, *, rotation=None, new_profile=None,
             tamper=None, replay=None, hostname="audit.local", lookup=None, allow_unanchored=False, expected_stream=None) -> dict:
    with connect(profile, port, hostname=hostname) as connection:
        uri, _, key = peer(connection)
        if uri != "urn:public-audit:server":
            raise ValueError("SERVER_IDENTITY")
        challenge = receive(connection)
        if challenge["kind"] == "error":
            return {"error": verify(key, "error", challenge)["code"]}
        body = verify(key, "challenge", challenge)
        if body["source"] != source:
            raise ValueError("SOURCE_IDENTITY")
        pin = profile / "stream.json"
        expected_stream = expected_stream if expected_stream is not None else json.loads(pin.read_text()) if pin.is_file() else source if allow_unanchored else None
        if expected_stream is None or body.get("stream") != expected_stream:
            raise ValueError("CLIENT_STREAM_BINDING")
        request = {**body, "request_id": secrets.token_hex(16), "query": query}
        kind = "audit"
        if rotation:
            kind = "rotate"
            request.pop("query")
            request["rotation"] = rotation
            request["new_signature"] = sign(app_private(new_profile), "new-key", {"challenge": digest(body), "rotation": rotation})
        if lookup:
            kind = "lookup"
            request.pop("query",None)
            request["lookup_id"] = lookup["body"]["request_id"]
        message = sign(app_private(profile), kind, request)
        if tamper == "scope":
            message["body"]["query"] = {"slots": 1, "fields": 3}
        elif tamper == "epoch":
            message["body"]["epoch"] += 1
            message = sign(app_private(profile), kind, message["body"])
        elif tamper == "actor":
            message["body"]["actor"] = "2" if body["actor"] == "1" else "1"
            message = sign(app_private(profile), kind, message["body"])
        if replay:
            message = replay
        try:
            send(connection, message)
            response = receive(connection)
        except (EOFError,OSError):
            return {"error":"OUTCOME_UNKNOWN","request":message}
        if response["kind"] == "error":
            return {"error": verify(key, "error", response)["code"], "detail": response["body"], "request": message}
        if lookup:
            envelope = verify(key,"lookup-response",response)
            if envelope["request"] != digest(message) or lookup["body"]["actor"] != body["actor"]:
                raise ValueError("LOOKUP_BINDING")
            result = check_result(envelope["result"],lookup,key,profile,allow_unanchored=allow_unanchored,recovered=True,expected_stream=expected_stream)
        else:
            result = check_result(verify(key,"response",response),message,key,profile,allow_unanchored=allow_unanchored,expected_stream=expected_stream)
        return {"response":result,"request":message,"tls":connection.version(),"cipher":connection.cipher()[0]}



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("profile", type=Path)
    parser.add_argument("--allow-unanchored",action="store_true")
    args = parser.parse_args()
    for line in sys.stdin:
        try:
            request = json.loads(line)
            result = exchange(args.profile, request["port"], request["source"], request.get("query", {"slots": 63, "fields": 3}),
                              tamper=request.get("tamper"), replay=request.get("replay"),lookup=request.get("lookup"),allow_unanchored=args.allow_unanchored,expected_stream=request.get("stream"))
        except Exception as error:
            result = {"error":str(error) if isinstance(error,ValueError) else type(error).__name__}
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
