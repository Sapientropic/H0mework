"""Lossless donor replies: the signed ledger already carries the complete event."""
from copy import deepcopy

PROFILE='ledger-body-result/v1'
KINDS={'donor-extension','energy-donor'}


def enabled(config):
    profile=config.get('donor_result_codec')
    if profile is not None and (profile!=PROFILE or not config.get('donor')):
        raise ValueError('DONOR_RESULT_CODEC_PROFILE')
    return profile==PROFILE


def encode_result(result,*,admitted):
    if result is None or not admitted:return result
    if not isinstance(result,dict):raise ValueError('DONOR_RESULT_TYPE')
    event=result.get('event')
    if not isinstance(event,dict) or event.get('type') not in KINDS:return result
    if 'event_ref' in result or result.get('ledger',{}).get('kind')!='ledger' or result['ledger'].get('body')!=event:
        raise ValueError('DONOR_RESULT_COMMON_EVENT')
    return {**{k:v for k,v in result.items() if k!='event'},'event_ref':PROFILE}


def decode_result(result,*,admitted):
    if result is None:return result
    if not isinstance(result,dict):raise ValueError('DONOR_RESULT_TYPE')
    if 'event_ref' not in result:return result
    ledger=result.get('ledger')
    if (not admitted or result['event_ref']!=PROFILE or 'event' in result or not isinstance(ledger,dict) or
            ledger.get('kind')!='ledger' or not isinstance(ledger.get('body'),dict) or ledger['body'].get('type') not in KINDS):
        raise ValueError('DONOR_RESULT_REFERENCE')
    value=deepcopy(result);value.pop('event_ref');value['event']=deepcopy(value['ledger']['body'])
    return value


def decode_body(kind,body,*,admitted):
    # Verify the original wire signature before applying this projection.
    if kind=='response':return decode_result(body,admitted=admitted)
    if kind=='lookup-response':return {**body,'result':decode_result(body['result'],admitted=admitted)}
    return body
