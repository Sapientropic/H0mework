"""Independent consumer of original HA events, wire bytes and source successors."""
from __future__ import annotations

import argparse
import base64
from collections import defaultdict
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import sqlite3
import subprocess

from privacy_compare import signed, public_keys
from quorum import verify_certificate

ROOT = Path(__file__).resolve().parents[3]
MODULE = 'SaturationMonoid/ProcessGame/Society/PublicFunction/Productivity/Cell/Audit/Scoped/EnergyRenewal/Privacy/'
MOUTHS = ('window_append_keeps_consumed_current', 'handoff_append_keeps_consumed_current',
          'online_handoff_preserves_parent_next_and_complete_reply', 'online_handoff_next_is_own_root')


def load(path): return json.loads(Path(path).read_text())
def canonical(value): return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode()
def digest(value): return hashlib.sha256(canonical(value)).hexdigest()
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def source_request(rows):
    past = [json.loads(row[3])['body'] for row in rows]
    response = next(event for event in past if event['type'] == 'native-response')
    epochs = [event for event in past if event['type'] in {'energy-renewal', 'energy-audit'}]
    assert len(epochs) == 2
    reply = response['request']['body']
    births = [{'cut': event['registration']['result']['cut'], 'key': event['registration']['result']['key']}
              for event in past if 'registration' in event]
    births.append({'cut': reply['cut'], 'key': reply['executor']})
    phases = [[]]
    for event in past:
        if event['type'] == 'energy-continuation':
            body = event['request']['body']
            phases[-1].append({'op': body['op'], 'query': body['query']})
            if event['native']['nextScope'] is not None: phases.append([])
    return {'mode': 'handoff', 'cut': response['native']['next']['cut'],
        'history': [{'cut': event['record']['cut'], 'query': event['record']['query']}
                    for event in past if event['type'] == 'disclosure'],
        'births': births, 'replies': [{'cut': reply['cut'], 'challenger': int(reply['actor']),
            'observedCut': reply['proposal']['body']['record']['cut'], 'alleged': reply['proposal']['body']['record']}],
        'candidate': epochs[0]['request']['body']['candidate'],
        'queries': [{'ordinal': event['native']['epoch']['ordinal'], 'query': event['request']['body']['query']}
                    for event in epochs],
        'ordinal': epochs[-1]['native']['epoch']['ordinal'], 'phases': phases,
        'handoffs': [{'replace': event['request']['body']['op'] == 'replace',
                      'actor': int(event['request']['body']['actor']), 'query': event['request']['body']['query']}
                     for event in past if event['type'] == 'energy-handoff']}


def frames(data):
    result = []
    while data:
        assert len(data) >= 16384, 'PARTIAL_APPLICATION_FRAME'
        size = int.from_bytes(data[:4], 'big')
        assert 0 < size <= 65532
        length = ((size+4+16383)//16384)*16384
        assert len(data) >= length and not any(data[4+size:length]), 'FRAME_PADDING'
        value = json.loads(data[4:4+size])
        assert canonical(value) == data[4:4+size]
        result.append(value)
        data = data[length:]
    return result


def wire_observations(path, registry):
    values = [json.loads(line) for line in Path(path).read_text().splitlines()]
    boundaries, observations = [], []
    for message in values:
        kind = message['kind']
        value = signed(registry['server']['app'], kind, message)
        assert kind in {'online-wire-observation', 'online-privacy-boundary'}
        if kind == 'online-privacy-boundary':
            assert set(value) == {'source','stream','phase','seq','parent','request_id','event','input','native','started_ns','finished_ns'}
            assert value['phase'] in {'before-intent','before-reconcile','restore','reply'}
            assert value['started_ns'] <= value['finished_ns']
            boundaries.append(value)
            continue
        assert set(value) == {'index','started_ns','finished_ns','peer','tls','cipher','operations'}
        assert value['tls'] == 'TLSv1.3' and value['started_ns'] <= value['finished_ns']
        data = {'sent': b'', 'received': b''}
        for op in value['operations']:
            assert value['started_ns'] <= op['at_ns'] <= value['finished_ns']
            if 'finished_ns' in op: assert op['at_ns'] <= op['finished_ns'] <= value['finished_ns']
            data[op['direction']] += base64.b64decode(op['bytes'], validate=True)
        sent, received = frames(data['sent']), frames(data['received'])
        assert len(sent) == 2 and len(received) == 1
        observations.append((value, sent[0], received[0], sent[1]))
    return boundaries, observations


def tls_streams(directory, expected_connections=6):
    streams = {}
    for path in sorted(directory.glob('tls-*.jsonl.gz')):
        chunks, forwarded, eof = defaultdict(bytes), defaultdict(int), defaultdict(int)
        with gzip.open(path, 'rt') as stream:
            for line in stream:
                row = json.loads(line)
                key = (row['connection'], row['direction'])
                if row['phase'] == 'received': chunks[key] += base64.b64decode(row['bytes'], validate=True)
                elif row['phase'] == 'forwarded': forwarded[key] += row['length']
                elif row['phase'] == 'eof': eof[key] += 1
                else: assert row['phase'] == 'interrupted'
        for key, data in chunks.items():
            assert forwarded[key] <= len(data) and eof[key] == 1
            raw = data
            records = []
            while raw:
                assert len(raw) >= 5, 'PARTIAL_TLS_RECORD_HEADER'
                size = int.from_bytes(raw[3:5], 'big')
                assert raw[0] in {20,21,22,23} and raw[1:3] in {b'\x03\x01', b'\x03\x03'}
                assert 0 < size <= 18432 and len(raw) >= 5+size, 'PARTIAL_TLS_RECORD'
                records.append({'type': raw[0], 'length': size})
                raw = raw[5+size:]
            assert records[0]['type'] == 22 and any(row['type'] == 23 for row in records)
            streams[path.name+':'+str(key)] = {'bytes': len(data), 'forwarded': forwarded[key],
                                             'sha256': hashlib.sha256(data).hexdigest(), 'records': records}
    assert type(expected_connections) is int and expected_connections > 0
    assert len(streams) == 2*expected_connections, 'COMPLETE_REAL_TLS_CONNECTIONS'
    return streams


def audit(run, out):
    out.mkdir(parents=True, exist_ok=False)
    receipt = load(run/'accepted.json')
    for path, expected in receipt['source_inputs'].items(): assert sha(path) == expected, ('ONLINE_SOURCE_BYTES', path)
    for path, expected in receipt['files'].items(): assert sha(run/path) == expected, ('ONLINE_RECEIPT_BYTES', path)
    assert receipt['original_live_events'] == 27
    prefix = load(run/'original-prefix.json')
    assert len(prefix) == 24
    baseline = Path(receipt['baseline'])
    config = load(baseline/'actual/one/config.json')
    lean = config['worker']['command'][0]
    env = os.environ.copy()
    env['LEAN_PATH'] = config['worker']['lean_path']
    exporter_manifest = load(run.parent/'exporters-01/accepted.json')
    assert exporter_manifest['builder_sha256'] == sha(ROOT/'Lean/scripts/verification/public-online-privacy-build.py')
    assert sha(lean) == config['descriptor']['compiler_sha256']
    for feature, installed in exporter_manifest['exporters'].items():
        source = Path(installed['exporter'])
        assert sha(source) == installed['exporter_sha256']
        text = source.read_text()
        declarations, main = text.split('\ndef main (arguments : List String) : IO Unit := do')
        assert 'let larger := arguments.head? = some "private-two"' in main
        namespace = feature.capitalize()+'Export'
        assert namespace+'.execute larger' in main
        original_text = (ROOT/'Lean/scripts/verification'/('public-'+feature+'-source.lean')).read_text()
        original = original_text.split('\ndef main : IO Unit :=')[0]
        expected_main = original_text[original_text.index('\ndef main : IO Unit :='):].replace(
            'def main : IO Unit := do','def main (arguments : List String) : IO Unit := do\n  let larger := arguments.head? = some "private-two"')
        call = '    let result := Json.parse line >>= '+namespace+'.execute'
        if feature == 'handoff':
            expected_main = expected_main.replace(call,'    let result := Json.parse line >>= fun input =>\n      if (input.getObjValAs? Bool "__private_audit").toOption = some true then\n        HandoffExport.privateAfter larger input\n      else HandoffExport.execute larger input')
        else: expected_main = expected_main.replace(call,call+' larger')
        assert '\ndef main (arguments : List String) : IO Unit := do'+main == expected_main
        normalized = declarations
        if feature == 'handoff':
            normal_start = normalized.index('\ndef privateAfter ')
            actual_inspection = normalized[normal_start+1:normalized.index('\nend HandoffExport',normal_start)]
            execute_start = normalized.index('def execute (larger : Bool)')
            result_start = normalized.index('  let result := EnergyRenewal.Handoff.Runtime.consume handoffSeed received ordinal',execute_start)
            expected_inspection = normalized[execute_start:result_start].replace('def execute ','def privateAfter ',1)+(
                '  let after := handoffSeed.current received (ordinal+1)\n  return Json.mkObj [("feed",toJson (toString (after.stock 3 Good.feed))),("larger",toJson larger)]\n')
            assert actual_inspection == expected_inspection
            normalized = normalized[:normal_start]+normalized[normalized.index('\nend HandoffExport',normal_start):]
            normalized = normalized.replace('\n\nend HandoffExport','\nend HandoffExport')
        normalized = normalized.replace('def execute (larger : Bool) (request : Json)', 'def execute (request : Json)')
        if feature == 'governance': normalized = normalized.replace('queries larger births','queries false births')
        else:
            normalized = normalized.replace('Governance.current queries larger births','Governance.current queries false births')
            normalized = normalized.replace('⟨queries,larger,births,replies,cut,candidate⟩','⟨queries,false,births,replies,cut,candidate⟩')
        assert normalized == original, 'ONLY_ORIGINAL_PRIVATE_PARAMETER_CHANGED'
        imports = '\n'.join(line for line in original.splitlines() if line.startswith('import '))
        old = '\n'.join(line for line in original.splitlines() if not line.startswith('import '))
        new = '\n'.join(line for line in declarations.splitlines() if not line.startswith('import '))
        proof = out/(feature+'-original.lean')
        proof.write_text(imports+'\nnamespace Original\n'+old+'\nend Original\nnamespace Branched\n'+new+
            '\nend Branched\ntheorem original_false_is_exact (request : Lean.Json) : Branched.'+namespace+
            '.execute false request = Original.'+namespace+'.execute request := rfl\n')
        checked = subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',str(proof)],
            cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=120)
        (out/(feature+'-original.log')).write_text(checked.stdout+checked.stderr)
        assert checked.returncode == 0, checked.stdout+checked.stderr
    pairs, transcript_counts, stream_results = {}, {}, {}
    for lane, variant in (('one','private-one'), ('two','private-two')):
        directory = run/lane
        cfg = load(directory/'config.json')
        assert cfg['backend'][-1] == variant
        for name in ('governance','energy','continuation','handoff'):
            assert cfg[name]['private_variant'] == cfg[name]['backend'][-1] == variant
            installed = exporter_manifest['exporters'][name]
            assert cfg[name]['exporter'] == cfg[name]['backend'][4] == installed['exporter']
            assert cfg[name]['private_exporter']['original_exporter_sha256'] == cfg[name]['descriptor']['exporter_sha256']
            assert cfg[name]['private_exporter']['exporter_sha256'] == installed['exporter_sha256']
        assert cfg['online_privacy']['prefix'] == {'seq': 24, 'head': prefix[-1][2]}
        registry = public_keys(directory/'public')
        events = load(directory/'events.json')
        assert len(events) == 27 and events[:24] == prefix
        original_cfg = load(Path(cfg['original_live_root'])/'service.json')
        with sqlite3.connect(Path(original_cfg['database']).as_uri()+'?mode=ro',uri=True) as db:
            originals = db.execute('SELECT id,previous,hash,message FROM events ORDER BY id').fetchall()
        assert len(originals) == 27 and [list(row) for row in originals[:24]] == prefix
        assert originals[-1][2] == receipt['original_live_head']
        keys = {registry[label]['actor']:registry[label] for label in ('auditor1','auditor2')}
        previous = '0'*64
        for number, before, hashed, text in prefix:
            event = signed(registry['server']['app'],'ledger',json.loads(text))
            request = event['request']; actor = request['body']['actor']
            signed(keys[actor]['app'],request['kind'],request)
            assert before == previous and hashed == hashlib.sha256(bytes.fromhex(before)+canonical(json.loads(text))).hexdigest()
            assert event['source'] == request['body']['source'] == cfg['source']
            if event['type'] == 'rotation': keys[actor] = event['new']
            previous = hashed
        trust = load(directory/'trust.json')
        observations = load(directory/'observations.json')
        assert len(observations) == 6
        boundaries, wires = wire_observations(directory/'boundary.jsonl', registry)
        assert len(wires) == 5
        successful = []
        for index, message in enumerate(observations):
            if 'coordinator_observation_lost' in message:
                assert index == 2 and set(message) == {'coordinator_observation_lost','request'}
                boundary = signed(registry['server']['app'],'ha-fault-boundary',message['coordinator_observation_lost'])
                assert boundary['seq'] == 26 and boundary['phase'] == 'after-intent'
                assert boundary['message'] == json.loads(events[25][3])
                assert boundary['message']['body']['request'] == message['request']
                continue
            actor = message['body']['request']['body']['actor']
            key = registry['auditor'+actor]['app']
            value = signed(key, 'online-client-observation', message)
            request, challenge, response = value['request'], value['challenge'], value['response']
            cb = signed(registry['server']['app'], 'challenge', challenge)
            body = signed(key, request['kind'], request)
            for field in ('source','stream','actor','nonce','seq','cut','epoch','expires'): assert body[field] == cb[field]
            clocks = [value['times'][field] for field in ('connect_start_ns','connected_ns','challenge_received_ns','request_sent_ns','response_received_ns')]
            assert all(type(clock) is int for clock in clocks) and clocks == sorted(clocks)
            if index == 2:
                assert response.get('transport_error') in {'EOFError','ConnectionResetError'}
                assert value['tls'] in {'TLSv1.3', None}
                continue
            assert value['tls'] == 'TLSv1.3'
            rb = signed(registry['server']['app'], response['kind'], response)
            result = rb['result'] if response['kind'] == 'lookup-response' else rb
            if response['kind'] == 'lookup-response': assert rb['request'] == digest(request)
            seq = result['anchor']['body']['seq']
            row = events[seq-1]
            ledger = result['ledger']
            event = signed(registry['server']['app'], 'ledger', ledger)
            assert ledger == json.loads(row[3]) and event == result['event']
            assert set(event) == {'type','source','stream','request','peer','scope','native','nextScope'}
            assert result['head'] == row[2] == hashlib.sha256(bytes.fromhex(row[1])+canonical(ledger)).hexdigest()
            verify_certificate(trust, result['anchor'], source=cfg['source'], stream=cfg['stream'], seq=seq,
                               previous=row[1], head=row[2], message=ledger)
            assert result['request'] == digest(event['request'])
            successful.append(result)
            wire, wc, wr, ws = wires[len(successful)-1]
            assert (wc,wr,ws) == (challenge,request,response), 'ENTIRE_APPLICATION_WIRE'
            assert wire['started_ns'] <= clocks[-1] and wire['finished_ns'] >= clocks[3]
        assert successful[0] == successful[1], 'PAID_LOOKUP_WAS_CHANGED'
        assert successful[2] == successful[3], 'RECOVERED_LOOKUP_WAS_CHANGED'
        pending = load(directory/'pending.json')
        assert pending['seq'] == 26 and pending['message'] == json.loads(events[25][3])
        lost_request = observations[2].get('request') if 'coordinator_observation_lost' in observations[2] else observations[2]['body']['request']
        assert pending['message']['body']['request'] == lost_request
        phases = {(entry['seq'],entry['phase']) for entry in boundaries}
        assert {(25,'before-intent'),(25,'reply'),(26,'before-intent'),(26,'before-reconcile'),(26,'restore'),(26,'reply'),(27,'before-intent'),(27,'reply')} <= phases
        inputs = []
        for seq in (25,26,27):
            row = events[seq-1]
            event = json.loads(row[3])['body']
            raw = source_request(events[:seq])
            inputs.append(raw)
            relevant = [entry for entry in boundaries if entry['seq'] == seq]
            assert relevant and all(entry['event'] == digest(event) and entry['native'] == digest(event['native']) and
                entry['input'] == raw and entry['parent'] == row[1] and entry['request_id'] == event['request']['body']['request_id'] for entry in relevant)
        private_rows = [signed(registry['server']['app'],'online-private-state',json.loads(line))
                        for line in (directory/'private-state.jsonl').read_text().splitlines()]
        assert {row['seq'] for row in private_rows} == {25,26,27}
        for row in private_rows:
            assert row['event'] == digest(json.loads(events[row['seq']-1][3])['body'])
            assert row['private'] == {'feed': '39' if variant == 'private-one' else '38', 'larger': variant == 'private-two'}
            assert row['argv'] == cfg['handoff']['backend'] == shlex.split(row['observed_command'])
        for mode in ('actual-one','actual-two'):
            result = subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true','--run',
                'scripts/verification/public-network-privacy-source.lean',mode],cwd=ROOT/'Lean',env=env,
                input=''.join(canonical(raw).decode()+'\n' for raw in inputs),text=True,capture_output=True,timeout=120)
            (out/(lane+'-'+mode+'.stdout')).write_text(result.stdout)
            assert result.returncode == 0 and result.stderr == '', result.stderr
            answers = [json.loads(line) for line in result.stdout.splitlines()]
            assert answers == [json.loads(row[3])['body']['native'] for row in events[24:]], 'ACTUAL_SOURCE_REPLY'
        native = [json.loads(row[3])['body']['native'] for row in events[24:]]
        assert native[0]['before']['energy'] == ['2','0','0','3'] and native[0]['next']['energy'] == ['0']*4
        assert [point['reason'] for point in native] == ['DELIVERED','UNAUTHORIZED','UNFUNDED']
        assert all(not packet['packets'] and not any(row['accepted'] for row in packet['rows']) for packet in native[1:])
        assert native[0]['next'] == native[1]['before'] and native[1]['next'] == native[2]['before']
        assert len({json.loads(row[3])['body']['request']['body']['request_id'] for row in events}) == 27
        pairs[lane] = native
        transcript_counts[lane] = len(wires)
        stream_results[lane] = tls_streams(directory)
        for member in 'abcd':
            ac = load(directory/(member+'-config.json'))
            assert ac['semantic']['private_variant'] == ac['semantic']['backend'][-1] == variant
        stderr1 = load(directory/'writer-1-ready.json')['public_stderr']
        stderr2 = load(directory/'writer-2-ready.json')['public_stderr']
        assert stderr1 != stderr2 and Path(stderr1).is_file() and Path(stderr2).is_file()
    assert pairs['one'] == pairs['two'], 'DISTINCT_PRIVATE_STATES_PUBLIC_RESULTS'
    assert not list(run.rglob('*.key'))
    # New proof compiles independently; no producer success bit is a premise.
    overlay = out/'lib'
    overlay.mkdir()
    for dependency in Path(env['LEAN_PATH']).rglob('*'):
        destination = overlay/dependency.relative_to(env['LEAN_PATH'])
        if dependency.is_dir(): destination.mkdir(exist_ok=True)
        else: os.link(dependency,destination)
    target = overlay/(MODULE+'Online.olean'); target.parent.mkdir(parents=True,exist_ok=True)
    source = ROOT/'Lean'/(MODULE+'Online.lean')
    compiled = subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',
        '-o',str(target),str(source)],cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=60)
    assert compiled.returncode == 0 and not compiled.stdout and not compiled.stderr, compiled.stdout+compiled.stderr
    assert sha(target) == sha(run.parent/'Online.olean')
    namespace = MODULE.replace('/','.')
    capsule = out/'kernel.lean'
    capsule.write_text('import '+namespace+'Online\n'+''.join('#print axioms '+namespace+name+'\n' for name in MOUTHS))
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    kernel = subprocess.run([lean,'--trust=0','-j1','-DElab.async=false','-DwarningAsError=true',str(capsule)],
        cwd=ROOT/'Lean',env=env,text=True,capture_output=True,timeout=60)
    (out/'kernel.log').write_text(kernel.stdout+kernel.stderr)
    assert kernel.returncode == 0
    mouths = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", kernel.stdout)
    assert {name for name,_ in mouths} == {namespace+name for name in MOUTHS}
    for _, axioms in mouths: assert set(filter(None,map(str.strip,axioms.split(',')))) <= {'propext','Classical.choice','Quot.sound'}
    (out/'tls-streams.json').write_bytes(canonical(stream_results)+b'\n')
    result = {'source_receipt_sha256': sha(run/'accepted.json'), 'audit_source_sha256': sha(__file__),
        'actual_private_branches': 2, 'new_actual_events': 6, 'paid_energy_each': 5,
        'complete_application_connections': transcript_counts, 'captured_tls_streams': 24,
        'actual_source_replays': 12, 'original_prefix_preserved': 24, 'original_live_events': 27,
        'pending_recoveries': 2, 'repeated_lookup_without_repayment': True, 'standard_axiom_mouths': 4,
        'coordinator_observation_lost': 1, 'closed_connection_tls_metadata': 1,
        'scope': 'Original HA same-event values, actual payment and exact next, full captured bytes and clocks; HA timing independence is not inferred from value equality'}
    (out/'accepted.json').write_bytes(canonical(result)+b'\n')
    print('INDEPENDENT ONLINE HA PASS: 2 actual private branches; 6 new events; paid5 each; exact intent recovery; no repayment; 12 source replays; 24 TLS streams',flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('run',type=Path); parser.add_argument('out',type=Path)
    args=parser.parse_args(); audit(args.run.resolve(),args.out.resolve())
