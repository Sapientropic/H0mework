"""Admit material regeneration as a successor of the committed supply coface."""
import json
import re

from anchor import public_key
from crypto import canonical, digest, verify
import source_extension

EVENT = 'material-extension'
FEATURE = 'energy-material'
READY = 'native-material-extension-ready'


def point(config, prefix):
    parent = source_extension.admission(config)
    descriptor = config['refeed']['descriptor']
    if (descriptor['source'], descriptor['stream'], descriptor['compiler']) != (
            parent['source'], parent['stream'], parent['descriptor']['compiler']):
        raise ValueError('MATERIAL_DESCRIPTOR')
    if (set(prefix) != {'seq', 'head'} or type(prefix['seq']) is not int
            or prefix['seq'] <= parent['prefix']['seq'] or type(prefix['head']) is not str
            or re.fullmatch('[0-9a-f]{64}', prefix['head']) is None):
        raise ValueError('MATERIAL_PREFIX')
    return dict(version=1, feature=FEATURE, parent=digest(config['source_extension']),
                source=parent['source'], stream=parent['stream'], cluster=parent['cluster'],
                prefix=prefix, descriptor=descriptor)


def admission(config, certificate=None):
    certificate = config['material_extension'] if certificate is None else certificate
    if set(certificate) != {'point', 'votes'}:
        raise ValueError('MATERIAL_CERTIFICATE')
    value = certificate['point']
    if value != point(config, value['prefix']):
        raise ValueError('MATERIAL_CERTIFICATE_BINDING')
    settings = config['refeed']; backend = settings['backend']
    if (len(backend) != 6 or backend[-1] != 'private-one'
            or settings.get('private_variant', 'private-one') != 'private-one'
            or 'private_exporter' in settings):
        raise ValueError('MATERIAL_PUBLIC_SOURCE')
    members = []; probes = []
    for vote in certificate['votes']:
        if set(vote) != {'member', 'receipt'} or vote['member'] not in config['ha']['trust']['members']:
            raise ValueError('MATERIAL_VOTE')
        member = vote['member']
        body = verify(public_key(config['ha']['trust']['members'][member]), READY, vote['receipt'])
        if (body['point'] != value or body['member'] != member or body['legacy_prefix'] != value['prefix']
                or body['compiler'] != value['descriptor']['compiler']
                or not body['legacy_backend'] or not body['source_backend']
                or set(body['probe']) != {'input', 'output'}
                or any(not isinstance(x, str) or re.fullmatch('[0-9a-f]{64}', x) is None for x in body['probe'].values())):
            raise ValueError('MATERIAL_READY')
        members.append(member); probes.append(body['probe'])
    if members != list('abcd') or any(p != probes[0] for p in probes[1:]):
        raise ValueError('MATERIAL_LOCAL_KERNEL_COVERAGE')
    return value


def committed(config, rows):
    active = None
    for index, row in enumerate(rows):
        event = json.loads(row[3])['body']
        if event['type'] == EVENT:
            if active is not None: raise ValueError('MATERIAL_DUPLICATE')
            certificate = event['native']; value = admission(config, certificate)
            prefix = dict(seq=index, head=rows[index-1][2] if index else '0'*64)
            if value['prefix'] != prefix or row[1] != prefix['head']:
                raise ValueError('MATERIAL_COMMITTED_PARENT')
            if value['parent'] != digest(source_extension.require(config, rows[:index])[1]):
                raise ValueError('MATERIAL_ACTUAL_PARENT_CERTIFICATE')
            active = (row[0], certificate)
        elif active is not None and event['type'] not in {FEATURE, 'rotation', 'productive-extension', 'energy-productive', 'arrival-extension', 'energy-arrival', 'donor-extension', 'energy-donor'}:
            raise ValueError('MATERIAL_PAST_KIND')
    return active


def require(config, rows):
    active = committed(config, rows)
    if active is None: raise ValueError("MATERIAL_NOT_COMMITTED")
    return active


def guard(config, rows, event):
    from productive_extension import guard as productive_guard
    productive_guard(config, rows, event)
    active = committed(config, rows)
    if event['type'] in {EVENT, FEATURE} and not config.get('refeed'):
        raise ValueError('MATERIAL_NOT_INSTALLED')
    if event['type'] == EVENT and active is not None: raise ValueError('MATERIAL_DUPLICATE')
    if event['type'] == FEATURE and active is None: raise ValueError('MATERIAL_NOT_COMMITTED')
    if active is not None and event['type'] not in {FEATURE, 'rotation', 'productive-extension', 'energy-productive', 'arrival-extension', 'energy-arrival', 'donor-extension', 'energy-donor'}:
        raise ValueError('MATERIAL_QUERY_REQUIRED')


def authorization(body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'feature', 'certificate')}


def expected(config, rows, event):
    import governance
    import regeneration
    source_extension.guard(config, rows, event)
    body = event['request']['body']; value = admission(config, event['native'])
    prefix = dict(seq=len(rows), head=rows[-1][2])
    if value['parent'] != digest(source_extension.require(config, rows)[1]):
        raise ValueError('MATERIAL_ACTUAL_PARENT_CERTIFICATE')
    if (set(event) != {'type', 'source', 'stream', 'request', 'peer', 'native'}
            or event['type'] != EVENT or event['request']['kind'] != EVENT
            or value['prefix'] != prefix or body['parent'] != prefix
            or event['source'] != value['source'] or body['source'] != value['source']
            or event['stream'] != value['stream'] or body['stream'] != value['stream']
            or body['feature'] != FEATURE or body['certificate'] != digest(event['native'])):
        raise ValueError('MATERIAL_ADMISSION_EVENT')
    _, _, current = regeneration.context(config, rows)
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])
            or body['member'] != governance.member(config, rows, body['actor'])):
        raise ValueError('MATERIAL_CURRENT_MEMBER')
    registration = next((e for e in governance.registered(rows) if e['result']['key'] == body['executor']), None)
    if registration is None: raise ValueError('MATERIAL_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    actual = verify(public_key(config['ha']['owners'][owner]), 'native-material-extension', body['execution'])
    if actual != authorization(body): raise ValueError('MATERIAL_OWNER_AUTHORIZATION')
    return value


def produce(config, rows, event):
    event['native'] = config['material_extension']
    expected(config, rows, event)
    return event
