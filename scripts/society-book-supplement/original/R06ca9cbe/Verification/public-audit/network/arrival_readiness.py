"""Issue and independently replay a local readiness vote for native arrival."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import time

from anchor import public_key
from crypto import app_private, canonical, digest, sign, verify
from source_semantics import Engine
import arrival_extension
import productive_regeneration
import source_readiness as original

READY = arrival_extension.READY
MAX_OUTPUT = 2 * 1024 * 1024
TIMEOUT = 1200


def events():
    return [
        {'kind': 'arrival', 'quantity': 4},
        {'kind': 'arrival', 'quantity': 3},
        {'kind': 'service', 'query': {'slots': 63, 'fields': 3}},
        {'kind': 'arrival', 'quantity': 3},
        {'kind': 'service', 'query': {'slots': 63, 'fields': 3}},
        {'kind': 'arrival', 'quantity': 'bad'},
        {'kind': 'nonsense', 'actor': 'metadata-preserved'},
        {'kind': 'arrival', 'quantity': 3},
    ]


def probe(config, rows):
    base, _, _ = productive_regeneration.context(config, rows)
    return {'mode': 'arrival-replay', 'source': base, 'events': events()}


def _arrival_state(row, expected_status, command):
    if row.get('status') != expected_status or canonical(row.get('metadata')) != canonical(command):
        raise ValueError('ARRIVAL_PROBE_WORD_STATUS')


def validate_probe_result(argument, output):
    """Check the complete per-event word before a node is allowed to sign it."""
    if not isinstance(output, list) or len(output) != len(argument['events']):
        raise ValueError('ARRIVAL_PROBE_WORD_SCHEMA')
    commands = argument['events']
    statuses = ['BLOCKED', 'ARRIVED', 'OPENED', 'BLOCKED', 'DELIVERED',
                'ERROR', 'ERROR', 'BLOCKED']
    for row, command, status in zip(output, commands, statuses):
        if not isinstance(row, dict):
            raise ValueError('ARRIVAL_PROBE_ROW_SCHEMA')
        _arrival_state(row, status, command)
        if not isinstance(row.get('before'), dict) or not isinstance(row.get('next'), dict):
            raise ValueError('ARRIVAL_PROBE_STATE_SCHEMA')
        if row.get('source_root') != arrival_extension.ORIGIN:
            raise ValueError('ARRIVAL_PROBE_ROOT_BINDING')
        if (not isinstance(row.get('scope'), dict) or row['scope'].get('unit') != 'energy'
                or not isinstance(row.get('nextScope'), dict) or row['nextScope'].get('unit') != 'energy'):
            raise ValueError('ARRIVAL_PROBE_SCOPE_SCHEMA')
        if command['kind'] == 'arrival' and status != 'ERROR' and row.get('service') is not None:
            raise ValueError('ARRIVAL_PROBE_SERVICE_SHAPE')
        if status in {'OPENED', 'DELIVERED'} and row.get('service') is None:
            raise ValueError('ARRIVAL_PROBE_SERVICE_SHAPE')
        if status == 'ERROR':
            nested = row.get('service')
            if (not isinstance(nested, dict) or nested.get('status') != 'ERROR'
                    or canonical(nested.get('metadata')) != canonical(row['metadata'])):
                raise ValueError('ARRIVAL_PROBE_ERROR_REPLY')

    # The source's six paid rows are consumed once: 3 feedstock, six steps,
    # and no second credit after the receipt is spent.
    accepted = output[1]
    source_before, source_after = accepted.get('source'), accepted.get('sourceNext')
    if (not isinstance(source_before, dict) or not isinstance(source_after, dict)
            or source_before.get('available') != '3' or source_after.get('available') != '0'
            or source_before.get('clock') != '125' or source_after.get('clock') != '131'
            or source_before.get('round') != 125 or source_after.get('round') != 131
            or len(accepted.get('sourceRows', [])) != 6
            or len(accepted.get('debit', [])) != 1 or len(accepted.get('credit', [])) != 1
            or accepted.get('spent') is not True):
        raise ValueError('ARRIVAL_PROBE_SOURCE_CONSUMPTION')
    paid_rows = accepted['sourceRows']
    if (paid_rows[0].get('remainingBefore') != 26 or paid_rows[-1].get('remainingAfter') != 20
            or accepted['debit'] != [['source:1', 'feed', '3']]
            or accepted['credit'] != [['audit:0', 'feed', '3']]):
        raise ValueError('ARRIVAL_PROBE_SOURCE_RECEIPT')
    source_request = {'consents': [], 'gates': [],
        'operation': {'actor': 'source:1', 'bundle': [['feed', '3']],
                      'kind': 'use', 'purpose': 'contribution'},
        'purpose': {'base': 'reserve', 'kind': 'source', 'owner': 1}, 'signer': 'source:1'}
    available = source_before; remaining = 26
    for index, source_row in enumerate(paid_rows):
        if (set(source_row) != {'cut', 'before', 'next', 'remainingBefore', 'remainingAfter', 'submitted', 'items'}
                or source_row['cut'] != paid_rows[0]['cut'] + index
                or source_row['before'] != available or source_row['remainingBefore'] != remaining):
            raise ValueError('ARRIVAL_PROBE_SOURCE_ROW_CHAIN')
        expected_next = dict(available)
        if index == 0:
            if (source_row['submitted'] != [source_request]
                    or source_row['items'] != [dict(index=0, request=source_request, accepted=True,
                        debit=[['source:1', 'feed', '3']], credit=[])]):
                raise ValueError('ARRIVAL_PROBE_SOURCE_EXPORT')
            expected_next['available'] = '0'
        elif source_row['submitted'] or source_row['items']:
            raise ValueError('ARRIVAL_PROBE_SOURCE_ROW_EMPTY')
        expected_next['clock'] = str(int(available['clock']) + 1)
        expected_next['round'] = available['round'] + 1
        remaining -= 1
        if (source_row['next'] != expected_next or source_row['remainingAfter'] != remaining):
            raise ValueError('ARRIVAL_PROBE_SOURCE_ROW_NEXT')
        available = expected_next
    if available != source_after or remaining != 20:
        raise ValueError('ARRIVAL_PROBE_SOURCE_EXHAUSTION')
    for refused in (output[3], output[7]):
        if (refused.get('source', {}).get('available') != '0'
                or refused.get('sourceNext', {}).get('available') != '0'
                or refused.get('sourceRows') != [] or refused.get('debit') != []
                or refused.get('credit') != [] or refused.get('spent') is not True):
            raise ValueError('ARRIVAL_PROBE_REPEAT_CREDIT')
    for row in output[5:7]:
        if (row['before'] != row['next'] or row['source'] != row['sourceNext']
                or row['sourceRows'] or row['debit'] or row['credit']):
            raise ValueError('ARRIVAL_PROBE_ERROR_ADVANCED_STATE')

    initial_claims = output[0]['before'].get('claims')
    if not isinstance(initial_claims, list):
        raise ValueError('ARRIVAL_PROBE_CLAIM_PREFIX')
    for row in output:
        if (row['before'].get('claims', [])[:len(initial_claims)] != initial_claims
                or row['next'].get('claims', [])[:len(initial_claims)] != initial_claims
                or row.get('account', {}).get('slots', -1) < 18
                or row.get('account', {}).get('outstanding') != '0'):
            raise ValueError('ARRIVAL_PROBE_CLAIM_PREFIX')
    if (output[1]['account']['slots'] != 18 or output[2]['account']['slots'] != 21
            or output[4]['account']['slots'] != 21):
        raise ValueError('ARRIVAL_PROBE_ACCOUNT_APPEND')

    opened, delivered = output[2]['service'], output[4]['service']
    fuel = [row for row in opened.get('rows', [])
            if row.get('accepted') is True
            and row.get('request', {}).get('operation') == {'actor': 'provider:0', 'kind': 'produce'}]
    settlements = [row for row in opened.get('rows', [])
                   if row.get('accepted') is True
                   and row.get('request', {}).get('operation', {}).get('kind') == 'settle'
                   and row['request']['operation'].get('instrument') == 'delivery']
    if (len(fuel) != 3 or len(settlements) != 3
            or any(row.get('debit') != [['provider:0', 'energy', '2']]
                   or row.get('credit') != [['audit:3', 'energy', '2']] for row in settlements)):
        raise ValueError('ARRIVAL_PROBE_FUEL_SETTLEMENT')
    if any(['provider:0', 'energy', '2'] not in row.get('credit', [])
           or ['provider:0', 'labor', '3'] not in row.get('credit', []) for row in fuel):
        raise ValueError('ARRIVAL_PROBE_FUEL_OUTPUT')
    packets = delivered.get('packets', [])
    if (len(packets) != 1 or [packet.get('slot') for packet in packets[0]] != list(range(6))
            or any(packet.get('payment', {}).get('available') != '1'
                   or int(packet['payment']['finish']) - int(packet['payment']['start']) != 1
                   for packet in packets[0])):
        raise ValueError('ARRIVAL_PROBE_SIX_SLOT_PAYMENT')
    return output


def _latest_productive(rows):
    for row in reversed(rows):
        event = json.loads(row[3])['body']
        if event['type'] == 'energy-productive':
            return event['native']
    raise ValueError('ARRIVAL_BASELINE_NOT_FOUND')


def _run_word(settings, argument):
    env = os.environ.copy(); env['LEAN_PATH'] = settings['lean_path']
    error_path = Path(settings['error_log'])
    error_path.parent.mkdir(parents=True, exist_ok=True)
    with error_path.open('ab') as error_stream:
        result = subprocess.run(settings['backend'], input=canonical(argument).decode() + '\n',
            text=True, stdout=subprocess.PIPE, stderr=error_stream, cwd=settings['cwd'], env=env,
            timeout=TIMEOUT, check=True)
    if len(result.stdout.encode()) > MAX_OUTPUT:
        raise ValueError('ARRIVAL_PROBE_OUTPUT_LIMIT')
    lines = result.stdout.splitlines()
    if len(lines) != 1:
        raise ValueError('ARRIVAL_PROBE_OUTPUT_FRAME')
    try:
        return json.loads(lines[0])
    except json.JSONDecodeError as error:
        raise ValueError('ARRIVAL_PROBE_OUTPUT_JSON') from error


def evaluate(config, rows, argument, seconds=TIMEOUT):
    expected_argument = probe(config, rows)
    if canonical(argument) != canonical(expected_argument):
        raise ValueError('ARRIVAL_PROBE_ORIGIN')
    settings = config['arrival']
    source = original.LocalEngine(settings)
    try:
        source.start()
        baseline = source.call(argument['source'], time.monotonic() + seconds)
        status = source.status()
    finally:
        original.close_all(source)
    if canonical(baseline) != canonical(_latest_productive(rows)):
        raise ValueError('ARRIVAL_OLD_LITERAL_CHANGED')
    output = _run_word(settings, argument)
    validate_probe_result(argument, output)
    return output, baseline, status


def issue(config, directory):
    directory = Path(directory); directory.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, directory)
    member, signed, prefix = original.snapshot(config)
    rows = [row[:4] for row in signed]
    point = arrival_extension.point(config, prefix)
    argument = probe(config, rows)
    output, baseline, source_status = evaluate(config, rows, argument)
    if original.snapshot(config) != (member, signed, prefix):
        raise ValueError('ARRIVAL_PREFIX_MOVED')
    key = app_private(Path(config['pki']) / 'anchor')
    if key.public_key().public_bytes_raw().hex() != config['registry']['anchor']['app']:
        raise ValueError('ARRIVAL_SIGNER')
    legacy = {'native': baseline, 'backend': source_status['backend']}
    body = dict(point=point, member=member, compiler=point['descriptor']['compiler'],
                legacy_prefix=prefix, probe=dict(input=digest(argument), output=digest(output)),
                source_descriptor=digest(config['arrival']['descriptor']), baseline=digest(legacy),
                source_backend=source_status['backend'], legacy_backend=source_status['backend'], journal=digest(signed), at=time.time())
    vote = dict(member=member, receipt=sign(key, READY, body))
    for name, value in [('rows', signed), ('input', argument), ('output', output),
                        ('legacy', legacy), ('vote', vote)]:
        original.save(directory / (name + '.json'), value)
    return vote


def check(config, directory, output):
    directory = Path(directory); output = Path(output); output.mkdir(parents=True, exist_ok=False)
    config = original.isolated(config, output)
    member, signed, prefix = original.snapshot(config)
    rows = [row[:4] for row in signed]
    recorded = json.loads((directory / 'rows.json').read_text())
    if recorded != [list(row) for row in signed]:
        raise ValueError('ARRIVAL_INDEPENDENT_JOURNAL')
    vote = json.loads((directory / 'vote.json').read_text())
    body = verify(public_key(config['registry']['anchor']), READY, vote['receipt'])
    argument = json.loads((directory / 'input.json').read_text())
    expected = json.loads((directory / 'output.json').read_text())
    legacy = json.loads((directory / 'legacy.json').read_text())
    if (vote['member'] != member or body['member'] != member
            or body['point'] != arrival_extension.point(config, prefix)
            or body['compiler'] != config['arrival']['descriptor']['compiler']
            or body['source_descriptor'] != digest(config['arrival']['descriptor'])
            or body['baseline'] != digest(legacy) or body['journal'] != digest(signed)
            or body['legacy_prefix'] != prefix
            or body['probe'] != dict(input=digest(argument), output=digest(expected))):
        raise ValueError('ARRIVAL_INDEPENDENT_BINDING')
    actual, baseline, source_status = evaluate(config, rows, argument)
    if (canonical(actual) != canonical(expected) or canonical(baseline) != canonical(legacy['native'])
            or not source_status['backend']):
        raise ValueError('ARRIVAL_INDEPENDENT_REPLAY')
    report = dict(exit=0, member=member, prefix=prefix, word=len(actual),
                  source_root=arrival_extension.ORIGIN, probe=body['probe'])
    original.save(output / 'acceptance.json', report)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['issue', 'check'])
    parser.add_argument('config', type=Path); parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(); config = json.loads(args.config.read_text())
    result = issue(config, args.directory) if args.operation == 'issue' else check(config, args.directory, args.output)
    print(json.dumps(result))
