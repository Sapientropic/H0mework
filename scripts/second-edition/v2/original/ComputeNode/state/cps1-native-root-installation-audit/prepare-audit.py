from pathlib import Path
import hashlib
import json
import re
import shutil

repo = Path('runtime/Documents/Homework')
state = Path(__file__).resolve().parent
prior = repo / 'ComputeNode/state/cps1-native-root-registration-audit'
cert = Path('/Volumes/Extension/Codex-Homework-cache/cps1-native-root-installation-certification')
promotion = json.loads((cert / 'promotion.json').read_text())
bootstrap = json.loads((state / 'bootstrap.json').read_text())
parent = Path(bootstrap['parent_receipt']['path'])
assert hashlib.sha256(parent.read_bytes()).hexdigest() == bootstrap['parent_receipt']['sha256']
src = state / 'input/src'
B = 'SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.'
body = repo / 'Lean' / ((B + 'Source.NativeRegistration.BodyPositive').replace('.', '/') + '.lean')
entries = [{'module': B + 'Source.NativeRegistration.BodyPositive', 'source': str(body), 'sha256': hashlib.sha256(body.read_bytes()).hexdigest()}] + promotion['entries']
modules, sources, files, mouths, data = [], {}, [], [], []
for row in entries:
    source = Path(row['source'])
    assert hashlib.sha256(source.read_bytes()).hexdigest() == row['sha256']
    module = row['module']
    rel = module.replace('.', '/') + '.lean'
    target = src / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, target)
    modules.append(module)
    sources[str(source.relative_to(repo))] = row['sha256']
    files.append('src/' + rel)
    prefix = module.rsplit('.', 1)[0] + '.'
    for hit in re.finditer(r'^(?:noncomputable )?(def|abbrev|theorem|structure|inductive) ([A-Za-z_][A-Za-z0-9_?.]*)', source.read_text(), re.M):
        name = prefix + hit[2]
        mouths.append(name)
        if hit[1] in ('def', 'abbrev'):
            data.append(name)
assert len(modules) == 21 and len(mouths) == len(set(mouths))
required = {
    B + 'Root.nativeSource': [B + 'Root.Native.initial', B + 'Source.NativeRegistration.registeredNativeInput'],
    B + 'Root.emitted': [B + 'Root.Native.sourceEvent'],
    B + 'Root.ledgerCompiler': [B + 'Root.Native.nativeTarget', B + 'Root.emitted'],
    B + 'Root.sourceNativeInputMaterial': [B + 'Root.Native.Current.body'],
    B + 'Root.projectionLaw': [B + 'Root.sourceNativeInputMaterial', B + 'Root.ledgerCompiler'],
    B + 'Runtime.readNativeBody': [B + 'Runtime.readNativeMaterial', B + 'Root.NativeInputMaterial.sourceBody'],
    B + 'Runtime.readWrittenNativeBody': [B + 'Runtime.readNativeWrite', B + 'Root.Native.Write.body'],
    B + 'Runtime.literal_native_body_next': [B + 'Runtime.literal_next_consumes_installed_body', B + 'Runtime.installed_written_body_actual'],
    B + 'Runtime.second_literal_next_consumes_previous_body': [B + 'Runtime.literal_native_body_next'],
    B + 'Source.NativeRegistration.registered_native_body_run': [B + 'Source.NativeRegistration.registered_generated_input_native'],
    B + 'Source.NativeRegistration.registered_native_body_not_reset': [B + 'Source.NativeRegistration.registered_native_body_run'],
}
checks = [[name, required.get(name, [])] for name in mouths]
contract = {
    'schema': 'CPS1-native-root-installation-audit-contract/v1',
    'modules': modules, 'sources': sources, 'mouths': mouths, 'checks': checks,
    'data_mouths': data, 'capture_data_mouths': [], 'capture_entry_points': [],
    'live_mouths': list(required), 'forbidden_live_prefixes': ['CPS1BiologicalUpdate.SourcePositive.'],
    'forbidden_live_names': [], 'Root_fresh_owners': 20,
    'intentional_ABI_retirement': str(state / 'input/src/retired-root-owner-names.txt'),
    'scope': 'same named Root stores actual native body; internally generated event/compiler/whole-ledger/runtime and two successive native-body next steps; same installed inputs source/target time positions; old phase/material restrictions and 75 fields/13 faces retained',
    'source_review': promotion['source_review'],
}
(state / 'audit-contract.json').write_text(json.dumps(contract, indent=2) + '\n')
tool = (prior / 'input/src/NativeRootRegistrationAuditTools.lean').read_text()
tool = re.sub(r'private def ownerModules : List Name := .*', 'private def ownerModules : List Name := [' + ','.join('`' + m for m in modules) + ']', tool, count=1)
tool = tool.replace('auditNativeRootRegistrationCandidate', 'auditNativeRootInstallationCandidate')
i = tool.index('  let checks : Array (Name × Array Name) := #[')
j = tool.index('\n  let mut valueRows', i)
tool = tool[:i] + '  let checks : Array (Name × Array Name) := #[\n' + ',\n'.join('    (`' + n + ', #[' + ','.join('`' + d for d in ds) + '])' for n, ds in checks) + '\n  ]' + tool[j:]
tool = re.sub(r'  for mouth in #\[.*?\] do', '  for mouth in #[' + ','.join('`' + m for m in mouths) + '] do', tool, count=1)
(src / 'NativeRootInstallationAuditTools.lean').write_text(tool)
imports = ''.join('import ' + m + '\n' for m in modules)
(src / 'ExecuteAudit.lean').write_text(imports + 'import NativeRootInstallationAuditTools\nauditNativeRootInstallationCandidate\n')
(src / 'Axioms.lean').write_text(imports + ''.join('#print axioms ' + m + '\n' for m in mouths))
math_files = list(files)
files += ['src/paid-names-native-root-installation.txt', 'src/NativeRootInstallationAuditTools.lean', 'src/ExecuteAudit.lean', 'src/Axioms.lean']
profile = hashlib.sha256(parent.read_bytes() + ''.join(bootstrap['shared']).encode() + b''.join((state / 'input' / p).read_bytes() for p in math_files)).hexdigest()
old = json.loads((prior / 'units.jsonl').read_text().splitlines()[-1])
runner = old['argv'][2]
runner = runner[:runner.index('\ncompile_gate "')]
runner = runner.replace(json.loads((prior / 'preparation.json').read_text())['proof_gate_profile'], profile).replace('paid-names-native-root-registration', 'paid-names-native-root-installation')
runner += '\n' + ''.join('compile_gate "' + m.replace('.', '/') + '" "' + m.replace('.', '/') + '.lean"\n' for m in modules)
for m in ['NativeRootInstallationAuditTools', 'ExecuteAudit']:
    runner += 'lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 -o "$PCNODE_OUT/' + m + '.olean" "$PCNODE_SRC/src/' + m + '.lean"\n'
runner += 'lean --trust=0 -DElab.async=false -DwarningAsError=true -M32000 -j1 "$PCNODE_SRC/src/Axioms.lean" > "$PCNODE_OUT/axioms.log" 2>&1\n'
unit = {**old, 'argv': ['bash', '-lc', runner], 'files': files, 'shared': bootstrap['shared'],
        'outputs': [m.replace('.', '/') + '.olean' for m in modules] + ['NativeRootInstallationAuditTools.olean', 'axioms.log'] + [p for p in old['outputs'] if p.startswith('ExecuteAudit.') or p == 'math-gates.log']}
unit['id'] = 'native-root-installation-execute-audit@' + hashlib.sha256(profile.encode() + runner.encode() + b''.join((state / 'input' / p).read_bytes() for p in files)).hexdigest()[:16]
(state / 'units.jsonl').write_text(json.dumps(unit, separators=(',', ':')) + '\n')
destination = state / 'results' / unit['id']
assert not destination.exists()
destination.symlink_to(bootstrap['canonical_outputs'], target_is_directory=True)
report = {'id': unit['id'], 'proof_gate_profile': profile, 'sources': sources, 'math_gates': len(modules),
          'mouths': len(mouths), 'value_paths': len(checks), 'shared_count': len(bootstrap['shared']),
          'parent_receipt_sha256': bootstrap['parent_receipt']['sha256'], 'Root_fresh_owners': 20}
(state / 'preparation.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'sources'}, indent=2))
