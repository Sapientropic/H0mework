"""Different-auditor replacement generated from the current paid Window."""
from anchor import public_key
from crypto import canonical,digest,verify
import continuation
import energy
import governance

KIND='energy-handoff'
OPS={'replace','read'}


def latest(rows):
    return next((event for event in reversed(energy.events(rows)) if event['type']==KIND),None)


def context(config,rows):
    events=energy.events(rows)
    cut=next((i for i,event in enumerate(events) if event['type']==KIND),len(events))
    if not cut or events[cut-1]['type']!=continuation.KIND:
        raise ValueError('HANDOFF_ACTUAL_WINDOW_REQUIRED')
    original,phases,scope,current=continuation.context(config,rows[:cut])
    requests=[]
    for event in events[cut:]:
        if event['type']!=KIND:raise ValueError('HANDOFF_PREFIX_KIND')
        body=event['request']['body']
        requests.append(dict(replace=body['op']=='replace',actor=int(body['actor']),query=body['query']))
        current={**event['native']['next'],'cut':event['native']['nextCut']}
    return {**original,'phases':phases,'handoffs':requests},scope,current


def authorization(config,body):
    return {k:body[k] for k in ('source','stream','parent','member','executor','cut','epoch','op','actor','query','unit','scope')} | {
        'descriptor':digest(config['handoff']['descriptor'])}


def argument(config,rows,event):
    body=event['request']['body']
    if event['type']!=KIND or event['request']['kind']!=KIND or body['op'] not in OPS:
        raise ValueError('HANDOFF_KIND')
    source=config.get('source') or config['streams'][event['stream']]['source']
    parent=dict(seq=len(rows),head=rows[-1][2])
    value,scope,current=context(config,rows)
    if (event['source']!=source or body['source']!=source or body['unit']!='energy' or body['parent']!=parent
            or event['scope']!=scope or body['scope']!=scope):
        raise ValueError('HANDOFF_PARENT_SCOPE_OR_UNIT')
    if body['actor'] not in ('1','2') or any(type(body[k]) is not int for k in ('cut','epoch')):
        raise ValueError('HANDOFF_ACTOR_OR_CURRENT_TYPE')
    if (body['cut'],body['epoch'])!=(current['cut'],current['version']):raise ValueError('HANDOFF_CURRENT')
    energy.query(body['query'])
    if canonical(body['member'])!=canonical(governance.member(config,rows,body['actor'])):
        raise ValueError('HANDOFF_MEMBER_ORIGIN')
    registration=next((entry for entry in governance.registered(rows) if entry['result']['key']==body['executor']),None)
    if registration is None:raise ValueError('HANDOFF_OWNER_NOT_REGISTERED')
    owner=registration['proof']['body']['owner']
    proof=verify(public_key(config['ha']['owners'][owner]),'native-energy-handoff',body['execution'])
    if canonical(proof)!=canonical(authorization(config,body)):raise ValueError('HANDOFF_OWNER_AUTHORIZATION')
    value['handoffs'].append(dict(replace=body['op']=='replace',actor=int(body['actor']),query=body['query']))
    return value


def native_call(config,value):
    return energy.native_call({**config,'energy':config['handoff']},value)


def expected(config,rows,event,*,native=True):
    value=argument(config,rows,event);_,scope,current=context(config,rows)
    supplied=event['native'];body=event['request']['body']
    checked=continuation.check_flows(supplied,current)
    if (type(supplied['actor']) is not int or supplied['actor']!=int(body['actor']) or
            event['nextScope'] is not None or supplied['nextScope'] is not None):
        raise ValueError('HANDOFF_SIGNER_OR_SCOPE_CHANGE')
    if body['op']=='replace' and (type(supplied['candidate']) is not int or supplied['candidate']!=supplied['actor']):
        raise ValueError('HANDOFF_SOURCE_SELECTED_CANDIDATE')
    if any(packet['actor']!=supplied['actor'] for packet in supplied['packets']):raise ValueError('HANDOFF_PACKET_ACTOR')
    if native and canonical(native_call(config,value))!=canonical(supplied):raise ValueError('HANDOFF_SOURCE_MISMATCH')
    return checked


def produce(config,rows,event):
    event['native']=native_call(config,argument(config,rows,event));event['nextScope']=None
    expected(config,rows,event)
    return event
