from pathlib import Path
import hashlib
import json
import re
import shutil

repo = Path('runtime/Documents/Homework')
state = Path(__file__).resolve().parent
prior = repo / 'ComputeNode/state/cps1-native-current-next-audit'
cert = Path('/Volumes/Extension/Codex-Homework-cache/cps1-native-root-registration-certification')
promotion = json.loads((cert / 'promotion.json').read_text())
bootstrap = json.loads((state / 'bootstrap.json').read_text())
parent = Path(bootstrap['parent_receipt']['path'])
assert hashlib.sha256(parent.read_bytes()).hexdigest() == bootstrap['parent_receipt']['sha256']
src = state / 'input/src'
prefix = 'SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.'
modules, sources, files, mouths, data = [], {}, [], [], []
for row in promotion['entries']:
    source = Path(row['production'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == row['sha256']
    module = row['module']
    rel = module.replace('.', '/') + '.lean'
    target = src / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    modules.append(module)
    sources[str(source.relative_to(repo))] = row['sha256']
    files.append('src/' + rel)
    for hit in re.finditer(r'^(?:noncomputable )?(def|abbrev|theorem|structure|inductive) ([A-Za-z_][A-Za-z0-9_?.]*)', source.read_text(), re.M):
        name = prefix + hit[2]
        mouths.append(name)
        if hit[1] in ('def', 'abbrev'):
            data.append(name)
assert len(modules) == 15 and len(mouths) == len(set(mouths))
required_short = {
    'registeredNativeInput': ['registeredTranslationRaw', 'registeredSupply', 'registeredResponse', 'registeredExchange'],
    'registeredResponse': ['responseRawFromRepair', 'registeredWhole', 'registeredSupply'],
    'registeredExchange': ['exchangeRawFromRepair', 'registeredWhole', 'registeredSupply', 'registeredResponse'],
    'exchangeRawFromRepair': ['source_exchange_raw'],
    'source_exchange_raw': ['source_base_parameters', 'normalRawAt'],
    'source_base_parameters': ['rationalCoordinate', 'dyadicHeight'],
    'registered_input_programme': ['registered_programme_actual'],
    'registered_input_exchange_positive': ['registered_repair_selected', 'registered_exchange_actual'],
    'registered_generated_input_native': ['registered_input_programme', 'registered_repair_selected', 'registered_exchange_actual'],
    'registered_exchange_actual': ['registered_response_actual', 'source_exchange_actual'],
    'registered_response_actual': ['indexed_response_actual'],
    'registered_genomic_complete': ['registered_before_dna', 'registered_before_remaining'],
    'registered_repair_selected': ['registered_whole_successful'],
}
required = {prefix + n: [prefix + d for d in ds] for n, ds in required_short.items()}
checks = [[name, required.get(name, [])] for name in mouths]
contract = {
    'schema': 'CPS1-native-root-registration-audit-contract/v1',
    'modules': modules, 'sources': sources, 'mouths': mouths, 'checks': checks,
    'data_mouths': data, 'capture_data_mouths': [], 'capture_entry_points': [],
    'live_mouths': data + [prefix + 'registered_generated_input_native', prefix + 'registered_input_exchange_positive'],
    'forbidden_live_prefixes': ['CPS1BiologicalUpdate.SourcePositive.'],
    'forbidden_live_names': ['Classical.choose'],
    'Root_recompiles': 0, 'controller_advanced': False,
    'scope': 'closed original primitive37 registration generates same actual programme, genomic update, repair, classical response and native exchange; direct generated_input consumer; no runtime installation',
    'source_review': promotion['source_review'],
}
(state / 'audit-contract.json').write_text(json.dumps(contract, indent=2) + '\n')
tool = (prior / 'input/src/NativeCurrentNextAuditTools.lean').read_text()
tool = re.sub(r'private def ownerModules : List Name := .*', 'private def ownerModules : List Name := [' + ','.join('`' + m for m in modules) + ']', tool, count=1)
tool = tool.replace('auditNativeCurrentNextCandidate', 'auditNativeRootRegistrationCandidate')
i = tool.index('  let checks : Array (Name × Array Name) := #[')
j = tool.index('\n  let mut valueRows', i)
tool = tool[:i] + '  let checks : Array (Name × Array Name) := #[\n' + ',\n'.join('    (`' + n + ', #[' + ','.join('`' + d for d in ds) + '])' for n, ds in checks) + '\n  ]' + tool[j:]
tool = re.sub(r'  for mouth in #\[.*?\] do', '  for mouth in #[' + ','.join('`' + m for m in mouths) + '] do', tool, count=1)
(src / 'NativeRootRegistrationAuditTools.lean').write_text(tool)
imports = ''.join('import ' + m + '\n' for m in modules)
(src / 'ExecuteAudit.lean').write_text(imports + 'import NativeRootRegistrationAuditTools\nauditNativeRootRegistrationCandidate\n')
(src / 'Axioms.lean').write_text(imports + ''.join('#print axioms ' + m + '\n' for m in mouths))
math_files = list(files)
files += ['src/paid-names-native-root-registration.txt', 'src/NativeRootRegistrationAuditTools.lean', 'src/ExecuteAudit.lean', 'src/Axioms.lean']
profile = hashlib.sha256(parent.read_bytes() + ''.join(bootstrap['shared']).encode() + b''.join((state / 'input' / p).read_bytes() for p in math_files)).hexdigest()
old = json.loads((prior / 'units.jsonl').read_text().splitlines()[-1])
runner = old['argv'][2]
runner = runner[:runner.index('\ncompile_gate "')]
runner = runner.replace(json.loads((prior / 'preparation.json').read_text())['proof_gate_profile'], profile).replace('paid-names-native-current-next', 'paid-names-native-root-registration')
runner += '\n' + ''.join('compile_gate "' + m.replace('.', '/') + '" "' + m.replace('.', '/') + '.lean"\n' for m in modules)
for m in ['NativeRootRegistrationAuditTools', 'ExecuteAudit']:
    runner += 'lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 -o "$PCNODE_OUT/' + m + '.olean" "$PCNODE_SRC/src/' + m + '.lean"\n'
runner += 'lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 "$PCNODE_SRC/src/Axioms.lean"\n'
unit = {**old, 'argv': ['bash', '-lc', runner], 'files': files, 'shared': bootstrap['shared'],
        'outputs': [m.replace('.', '/') + '.olean' for m in modules] + ['NativeRootRegistrationAuditTools.olean'] + [p for p in old['outputs'] if p.startswith('ExecuteAudit.') or p == 'math-gates.log']}
unit['id'] = 'native-root-registration-execute-audit@' + hashlib.sha256(profile.encode() + runner.encode() + b''.join((state / 'input' / p).read_bytes() for p in files)).hexdigest()[:16]
(state / 'units.jsonl').write_text(json.dumps(unit, separators=(',', ':')) + '\n')
destination = state / 'results' / unit['id']
assert not destination.exists()
destination.symlink_to(bootstrap['canonical_outputs'], target_is_directory=True)
report = {'id': unit['id'], 'proof_gate_profile': profile, 'sources': sources, 'math_gates': len(modules),
          'mouths': len(mouths), 'value_paths': len(checks), 'shared_count': len(bootstrap['shared']),
          'paid_names': bootstrap['paid_names'], 'parent_receipt_sha256': bootstrap['parent_receipt']['sha256'], 'Root_recompiles': 0}
(state / 'preparation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'sources'}, indent=2))
