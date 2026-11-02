from pathlib import Path
import ast
import hashlib
import json
import os
import re
import shlex
import subprocess
import time

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
base = box.parents[1]
prior = base / 'financial-direct/runtime'
load = lambda p: json.loads(Path(p).read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs = {}

def bind(path, wanted=None):
    path = Path(path)
    value = sha(path)
    assert wanted is None or value == wanted, str(path)
    inputs[str(path)] = value
    return value

old = load(prior / 'ready-verification.json')
assert old['ready'] and old['init_only_passed'] and not old['executed_main']
for p, wanted in old['inputs'].items():
    bind(p, wanted)
bind(prior / 'ready-verification.json')
old_linkage = load(prior / 'linkage-verification.json')
assert old_linkage['accepted']
for p, wanted in old_linkage['inputs'].items():
    bind(p, wanted)
bind(prior / 'linkage-verification.json')
certificate = load(box.parent / 'verification-check.json')
assert certificate['certified']
for p, wanted in certificate['inputs'].items():
    bind(p, wanted)
bind(box.parent / 'verification-check.json')
state = load(box / 'status.json')
rows = load(box / 'hot-source-plan.json')
assert state['exit'] == 0 and state['complete'] == state['total'] == len(rows) == 31
config = load(box / 'lean-env.json')
plan = load(box / 'source-plan.json')
assert len(plan) == len({r['module'] for r in plan}) == 122
old_plan = {r['module']: r for r in load(prior / 'source-plan.json')}
assert {r['module'] for r in plan} - old_plan.keys() == {
    'SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime'}
inventory = {r['module']: r for r in load(base / 'native/module-inventory-checked.json')}
receipts = {r['module']: load(box / f'Owner{i}-compile.json') for i, r in enumerate(rows)}
old_objects = shlex.split((prior / 'objects.rsp').read_text())
expected = {}
dependency_edges = []
for i, row in enumerate(rows):
    r = receipts[row['module']]
    assert r['exit'] == 0 and r['exact_dependencies']
    assert r['compile_options'] == dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000)
    assert r['module_package'] == row['package'] == inventory[row['module']]['package']
    bind(box / f'Owner{i}-compile.json')
    bind(row['source'], r['source_sha256'])
    assert r['source_sha256'] == row['source_sha256']
    assert Path(row['source']) == root / r['source']
    artifact = box / 'lib' / Path(row['module'].replace('.', '/') + '.olean')
    bind(artifact, r['artifact_sha256'])
    if row['package'] is not None:
        setup = config['module_setups'][row['module']]
        bind(setup, r['setup_sha256'])
        assert load(setup)['package'] == row['package']
    else:
        assert r['setup_sha256'] is None
    for module, wanted in r['dependencies'].items():
        relative = Path(module.replace('.', '/') + '.olean')
        provider = next(Path(p) / relative for p in config['LEAN_PATH'].split(':')
                        if (Path(p) / relative).exists())
        bind(provider, wanted)
        if module in receipts:
            assert wanted == receipts[module]['artifact_sha256']
        else:
            assert any(Path(p).resolve() == provider.resolve() and value == wanted
                       for p, value in old['inputs'].items()), ('unbound provider', module)
        dependency_edges.append(dict(consumer=row['module'], provider=module, sha256=wanted))
    c = box / 'generated' / Path(row['module'].replace('.', '/') + '.c')
    assert str(c) == r['c_path']
    bind(c, r['c_sha256'])
    code = c.read_text()
    inv = inventory[row['module']]
    marker = 'LEAN_EXPORT lean_object* ' + inv['initializer'] + '(uint8_t builtin) {'
    assert code.count(marker) == 1
    calls = re.findall(r'res = (initialize_\w+)\(builtin\)', code.split(marker, 1)[1])
    expected_calls = list(inv['import_initializers'])
    if inv['is_module']:
        expected_calls += [inv['runtime_initializer'], inv['comptime_initializer']]
    assert calls == expected_calls, row['module']
    obj = c.with_suffix('.o')
    paid = load(box / f'Object{i}.json')
    assert paid['exit'] == 0 and paid['c_sha256'] == sha(c)
    assert paid['command'] == [str(Path(config['binary']).with_name('leanc')), '-c', '-O2', '-ffp-contract=off', str(c), '-o', str(obj)]
    bind(obj, paid['object_sha256'])
    bind(box / f'Object{i}.json')
    original_obj = str(Path(row['actual_c']).with_suffix('.o'))
    assert original_obj in old_objects
    expected[original_obj] = str(obj)
assert expected == state['replacements']
objects = shlex.split((box / 'objects.rsp').read_text())
assert objects == [expected.get(p, p) for p in old_objects]
assert len(objects) == 1147
sources = load(box / 'c-sources.json')
main_c = base / 'shared-runtime/generated/PublicDefaultActualNative.c'
main_obj = main_c.with_suffix('.o')
assert sources == [str(Path(p).with_suffix('.c')) for p in objects] + [str(main_c), str(base / 'native/NativeBoot.c')]
binding = load(prior / 'source-binding.json')
assert binding['same_literal_consumer'] and not binding['executed_main']
bind(root / binding['source'], binding['source_sha256'])
literal = next(r for r in plan if r['module'] == 'PublicDefaultActualNative')
assert literal['source_sha256'] == binding['source_sha256'] == old['original_literal_source_sha256']
assert Path(literal['source']).read_bytes() == (root / binding['source']).read_bytes()
bind(main_c, old['inputs'][str(main_c)])
bind(main_obj, old['inputs'][str(main_obj)])
identity = load(box / 'logical-identity.json')
assert identity['exit'] == 0 and 'modules=31;' in identity['output'] and 'additiveDeclarations=4' in identity['output']
identity_args = []
for row in rows:
    relative = Path(row['module'].replace('.', '/') + '.olean')
    before, after = prior / 'lib' / relative, box / 'lib' / relative
    identity_args += [str(before), str(after)]
    wanted = next(value for p, value in old['inputs'].items() if Path(p).resolve() == before.resolve())
    bind(before, wanted)
assert identity['command'] == [config['binary'], '--trust=0', '-DwarningAsError=true', '-DElab.async=false', '-j1', '-M12000', '--run', str(box / 'identity.lean'), *identity_args]
canonical = load(box / 'canonical-identity.json')
assert canonical['exit'] == 0 and 'modules=2;' in canonical['output'] and 'additiveDeclarations=0' in canonical['output']
assert canonical['source_sha256'] == sha(box / 'identity.lean')
assert canonical['config_sha256'] == sha(box / 'lean-env.json')
canonical_args = []
for module in ['SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Runtime',
               'SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Source']:
    relative = Path(module.replace('.', '/') + '.olean')
    canonical_args += [str(box.parent / 'lib' / relative), str(box / 'lib' / relative)]
assert canonical['arguments'] == canonical_args
for p, wanted in canonical['argument_sha256'].items():
    bind(p, wanted)
for label, path in [('FrameLifecycle', canonical_args[0]), ('FrameFinancedSource', canonical_args[2])]:
    bind(path, load(box.parent / (label + '-compile.json'))['artifact_sha256'])
ir = load(box / 'frame-ir-run.json')
assert ir['exit'] == 0 and ir['source_sha256'] == sha(box / 'frame-ir.lean')
assert ir['config_sha256'] == sha(box / 'lean-env.json')
bind(box / 'frame-ir.json', ir['output_sha256'])
for run in [canonical, ir]:
    for p, wanted in run['imports'].items():
        bind(p, wanted)
body = '\n'.join(r['body'] for r in load(box / 'frame-ir.json'))
for name in ['Lifecycle.Runtime.frameCurrentAt', 'Lifecycle.Runtime.frameWordAt']:
    assert body.count(name) > 1
for forbidden in ['Lifecycle.Runtime.currentAt', 'Lifecycle.Runtime.wordAt', 'ProgrammeHistory.visitAt', 'OutstandingSource.actualExecution']:
    assert forbidden not in body, forbidden

# C pointer types erase borrowing, so compare the compiler's IR signatures and
# its own package-aware symbol names before accepting old object callers.
tables = {}
for version, cfg in [('old', prior / 'lean-env.json'), ('new', box / 'lean-env.json')]:
    run = load(box / (version + '-impure-abi-run.json'))
    assert run['exit'] == 0 and run['source_sha256'] == sha(box / 'impure-abi.lean')
    assert run['config_sha256'] == sha(cfg)
    bind(box / (version + '-impure-abi.json'), run['output_sha256'])
    for p, wanted in run['imports'].items():
        bind(p, wanted)
    data = load(box / (version + '-impure-abi.json'))
    assert {r['module']: r['package'] for r in data['modules']} == {r['module']: r['package'] for r in rows}
    tables[version] = {r['name']: r for r in data['declarations']}
    assert len(tables[version]) == len(data['declarations'])
old_abi, new_abi = tables['old'], tables['new']
changed = {n for n in old_abi.keys() & new_abi.keys()
           if any(old_abi[n][k] != new_abi[n][k] for k in ['symbol', 'params', 'result'])}
removed = old_abi.keys() - new_abi.keys()
symbols = {old_abi[n]['symbol'] for n in changed | removed}
fresh_c = {str(Path(p).with_suffix('.c')) for p in expected.values()}
uses = []
if symbols:
    pattern = re.compile(r'\b(?:l|lp)_[A-Za-z0-9_]+\b')
    for p in sources:
        for line_no, line in enumerate(Path(p).read_text().splitlines(), 1):
            for symbol in set(pattern.findall(line)) & symbols:
                if re.match(r'^(?:(?:LEAN_EXPORT|extern|static) )?(?:lean_object\*|uint\w+|size_t|double|float) ' + re.escape(symbol) + r'\(', line):
                    continue
                assert p in fresh_c, ('stale calling convention/helper', p, line_no, symbol)
                uses.append(dict(source=p, line=line_no, symbol=symbol))
abi = load(box / 'c-abi-verification.json')
assert abi['accepted'] and abi['executable_not_invoked']
tree = ast.parse((box / 'check_c_abi.py').read_text())
node = next(n for n in tree.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'pattern' for t in n.targets))
pattern = re.compile(ast.literal_eval(node.value.args[0]))
found = {}
total = 0
for p in sources:
    bind(p, abi['input_sha256'][p])
    for m in pattern.finditer(Path(p).read_text()):
        args = tuple(re.sub(r'\s+\w+$', '', part.strip()) for part in m[3].split(',')) if m[3].strip() not in ['', 'void'] else ()
        found.setdefault(m[2], set()).add((m[1], args))
        total += 1
assert not {n: s for n, s in found.items() if len(s) > 1}
assert total == abi['declarations'] and len(found) == abi['symbols']
negative = load(box / 'c-abi-negative-controls.json')
assert negative['exit'] == 0
link = load(box / 'native-link.json')
proof = load(box / 'link-verification.json')
assert link['exit'] == 0 and proof['linked'] and not proof['missing_live_providers']
exe = Path(proof['executable'])
expected_command = ['@' + str(box / 'objects.rsp') if a == '@' + str(prior / 'objects.rsp') else a for a in load(prior / 'native-link.json')['command']]
expected_command[-1] = str(exe)
assert link['command'] == expected_command and '-Wl,-undefined,error' in expected_command
assert proof['exact_replacements'] == expected
bind(exe, proof['executable_sha256'])
linked_libraries = subprocess.check_output(['otool', '-L', str(exe)], text=True)
for provider in load(base / 'native/official-package-providers.json'):
    bind(provider['path'], provider['sha256'])
    assert provider['path'] in linked_libraries
assert 'FlyCNS' not in linked_libraries
for name in ['lean-env.json', 'source-plan.json', 'hot-source-plan.json', 'objects.rsp', 'c-sources.json',
             'verify_ready.py', 'check_c_abi.py', 'c-abi-verification.json', 'c-abi-negative-controls.json',
             'logical-identity.json', 'canonical-identity.json', 'identity.lean', 'frame-ir.lean',
             'frame-ir-run.json', 'frame-ir.json', 'impure-abi.lean', 'emit_impure_abi.py',
             'old-impure-abi-run.json', 'new-impure-abi-run.json', 'old-impure-abi.json',
             'new-impure-abi.json', 'native-link.json', 'link-verification.json']:
    bind(box / name)
init_path = box / 'native-init-only.json'
if not init_path.exists():
    started = time.time()
    result = subprocess.run([str(exe), '--init-only'], cwd=root / 'Lean', capture_output=True, text=True)
    init_path.write_text(json.dumps(dict(exit=result.returncode, seconds=round(time.time() - started, 3),
        executable_sha256=sha(exe), output=result.stdout + result.stderr), indent=2) + '\n')
init = load(init_path)
assert init['exit'] == 0 and init['executable_sha256'] == sha(exe) and 'consumer main not called' in init['output']
bind(init_path)
(box / 'source-binding.json').write_text((prior / 'source-binding.json').read_text())
(box / 'extra-exports-plan.json').write_text((prior / 'extra-exports-plan.json').read_text())
bind(box / 'source-binding.json', sha(prior / 'source-binding.json'))
bind(box / 'extra-exports-plan.json', sha(prior / 'extra-exports-plan.json'))
for p, wanted in inputs.items():
    assert sha(p) == wanted, p
record = dict(ready=True, executable=str(exe), executable_sha256=sha(exe), inputs=inputs,
    original_literal_source_sha256=binding['source_sha256'], init_only_passed=True,
    original_logical_modules_preserved=121, source_compiled_modules=122,
    reused_original_objects=old['reused_original_objects'] - 1,
    original_olean_reemitted_modules=old['original_olean_reemitted_modules'], official_package_libraries=8,
    abi_declarations=total, abi_symbols=len(found), abi_conflicts=0,
    lean_external_symbols=proof['live_lean_external_symbols'], unresolved_lean_symbols=0,
    dependency_edges=dependency_edges, changed_ownership_signatures=sorted(changed),
    removed_ir_helpers=sorted(removed), refreshed_helper_references=uses,
    executed_main=False, goal_complete=False)
(box / 'ready-verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(f'LIFECYCLE READY PASS: 31 exact owners / 122 source union; original package identities and dependency edges; ABI={total}/{len(found)}; ownership callers refreshed; original initialization exit0')
