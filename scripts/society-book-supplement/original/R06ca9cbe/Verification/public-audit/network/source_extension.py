"""A source coface becomes active only through an original-journal event."""
from __future__ import annotations

import json
import re
from cryptography.exceptions import InvalidSignature
from crypto import canonical, digest, verify
from anchor import public_key

FEATURE = 'energy-regeneration'
KIND = 'native-source-extension-ready'
EVENT = 'source-extension'


def parent_context(config):
    value = dict(config)
    if 'cluster' not in value:
        value['cluster'] = digest(config['ha']['trust'])
    if 'semantic' not in value:
        value['semantic'] = {'descriptor': config['public_base_source']['descriptor']}
    return value


def point(config, prefix):
    import native_spare
    parent = native_spare.admission(parent_context(config))
    descriptor = config['regeneration']['descriptor']
    if (descriptor['source'] != parent['source'] or descriptor['stream'] != parent['stream']
            or descriptor['compiler'] != parent['descriptors']['base']['compiler']):
        raise ValueError('SOURCE_EXTENSION_DESCRIPTOR')
    if (set(prefix) != {'seq', 'head'} or type(prefix['seq']) is not int
            or prefix['seq'] < parent['prefix']['seq'] or type(prefix['head']) is not str
            or re.fullmatch('[0-9a-f]{64}', prefix['head']) is None):
        raise ValueError('SOURCE_EXTENSION_PREFIX')
    return dict(version=1, feature=FEATURE, parent=digest(config['native_admission']),
                source=parent['source'], stream=parent['stream'], cluster=parent['cluster'],
                prefix=prefix, descriptor=descriptor)


def admission(config, certificate=None):
    certificate = config['source_extension'] if certificate is None else certificate
    if set(certificate) != {'point', 'votes'}:
        raise ValueError('SOURCE_EXTENSION_CERTIFICATE')
    value = certificate['point']
    if canonical(value) != canonical(point(config, value['prefix'])):
        raise ValueError('SOURCE_EXTENSION_BINDING')
    backend = config['regeneration'].get('backend')
    if (not isinstance(backend, list) or len(backend) != 6
            or config['regeneration'].get('private_variant', 'private-one') != 'private-one'
            or backend[-1] != 'private-one' or 'private_exporter' in config['regeneration']):
        raise ValueError('SOURCE_EXTENSION_PUBLIC_EXECUTION')
    members, probes = [], []
    for entry in certificate['votes']:
        if set(entry) != {'member', 'receipt'}:
            raise ValueError('SOURCE_EXTENSION_VOTE')
        member = entry['member']
        if member not in config['ha']['trust']['members']:
            raise ValueError('SOURCE_EXTENSION_MEMBER')
        try:
            ready = verify(public_key(config['ha']['trust']['members'][member]), KIND, entry['receipt'])
        except InvalidSignature as error:
            raise ValueError('SOURCE_EXTENSION_SIGNATURE') from error
        if (ready['point'] != value or ready['member'] != member
                or ready['compiler'] != value['descriptor']['compiler']
                or ready['legacy_prefix'] != value['prefix']
                or set(ready['probe']) != {'input', 'output'}
                or any(type(item) is not str or re.fullmatch('[0-9a-f]{64}', item) is None
                       for item in ready['probe'].values())
                or not ready.get('legacy_backend') or not ready.get('source_backend')):
            raise ValueError('SOURCE_EXTENSION_READY')
        members.append(member); probes.append(ready['probe'])
    if members != list('abcd') or any(probe != probes[0] for probe in probes[1:]):
        raise ValueError('SOURCE_EXTENSION_COVERAGE')
    return value


def committed(config, rows):
    """Read the coface from the already validated journal, never from config alone."""
    active = None
    for index, row in enumerate(rows):
        event = json.loads(row[3])['body']
        if event['type'] == EVENT:
            if active is not None:
                raise ValueError('SOURCE_EXTENSION_DUPLICATE')
            certificate = event['native']; value = admission(config, certificate)
            prefix = dict(seq=index, head=rows[index-1][2] if index else '0'*64)
            if value['prefix'] != prefix or row[1] != prefix['head']:
                raise ValueError('SOURCE_EXTENSION_COMMITTED_PARENT')
            active = (row[0], certificate)
        elif active is not None and event['type'] not in {FEATURE, 'rotation', 'material-extension', 'energy-material', 'productive-extension', 'energy-productive', 'arrival-extension', 'energy-arrival', 'donor-extension', 'energy-donor'}:
            raise ValueError('SOURCE_EXTENSION_PAST_KIND')
    return active


def require(config, rows):
    active = committed(config, rows)
    if active is None:
        raise ValueError('SOURCE_EXTENSION_NOT_COMMITTED')
    return active


def guard(config, rows, event):
    from donor_arrival_live import guard as donor_guard
    donor_guard(config, rows, event)
    from material_extension import guard as material_guard
    material_guard(config, rows, event)
    if not config.get('regeneration'):
        if event['type'] in {EVENT, FEATURE}:
            raise ValueError('SOURCE_EXTENSION_NOT_INSTALLED')
        return
    active = committed(config, rows)
    if event['type'] == EVENT and active is not None:
        raise ValueError('SOURCE_EXTENSION_DUPLICATE')
    if event['type'] == FEATURE and active is None:
        raise ValueError('SOURCE_EXTENSION_NOT_COMMITTED')
    if active is not None and event['type'] not in {FEATURE, 'rotation', 'material-extension', 'energy-material', 'productive-extension', 'energy-productive', 'arrival-extension', 'energy-arrival', 'donor-extension', 'energy-donor'}:
        raise ValueError('SOURCE_EXTENSION_QUERY_REQUIRED')


def authorization(body):
    return {key: body[key] for key in ('source', 'stream', 'parent', 'member', 'executor', 'actor',
                                      'cut', 'epoch', 'feature', 'certificate')}


def expected(config, rows, event):
    import governance
    import handoff
    guard(config, rows, event)
    body = event['request']['body']; certificate = event['native']
    value = admission(config, certificate)
    prefix = dict(seq=len(rows), head=rows[-1][2] if rows else '0'*64)
    if (set(event) != {'type', 'source', 'stream', 'request', 'peer', 'native'}
            or event['type'] != EVENT or event['request']['kind'] != EVENT
            or value['prefix'] != prefix or body['parent'] != prefix
            or event['source'] != value['source'] or body['source'] != value['source']
            or event['stream'] != value['stream'] or body['stream'] != value['stream']
            or body['feature'] != FEATURE or body['certificate'] != digest(certificate)):
        raise ValueError('SOURCE_EXTENSION_EVENT_BINDING')
    legacy = [row for row in rows if json.loads(row[3])['body']['type'] != 'rotation']
    _, _, current = handoff.context(config, legacy)
    if (type(body['cut']) is not int or type(body['epoch']) is not int
            or (body['cut'], body['epoch']) != (current['cut'], current['version'])
            or canonical(body['member']) != canonical(governance.member(config, rows, body['actor']))):
        raise ValueError('SOURCE_EXTENSION_CURRENT_MEMBER')
    registration = next((entry for entry in governance.registered(rows)
                         if entry['result']['key'] == body['executor']), None)
    if registration is None:
        raise ValueError('SOURCE_EXTENSION_OWNER_NOT_REGISTERED')
    owner = registration['proof']['body']['owner']
    granted = verify(public_key(config['ha']['owners'][owner]), 'native-source-extension', body['execution'])
    if canonical(granted) != canonical(authorization(body)):
        raise ValueError('SOURCE_EXTENSION_OWNER_AUTHORIZATION')
    return value


def produce(config, rows, event):
    event['native'] = config['source_extension']
    expected(config, rows, event)
    return event
