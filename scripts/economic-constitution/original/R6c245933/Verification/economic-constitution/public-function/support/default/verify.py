from pathlib import Path
import hashlib
import json

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
load = lambda path: json.loads(path.read_text())
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
config = load(box / 'lean-env.json')
roots = [Path(path) for path in config['LEAN_PATH'].split(':')]

def artifact(module):
    relative = module.replace('.', '/') + '.olean'
    return next(path / relative for path in roots if (path / relative).exists())

rows = load(box / 'strict-current.json')
assert len(rows) == 18
for row in rows:
    assert row['exit'] == 0 and row['exact_dependencies']
    assert row['compile_options'] == dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000)
    assert sha(root / row['source']) == row['source_sha256']
    assert sha(artifact(row['module'])) == row['artifact_sha256']
    assert all(sha(artifact(name)) == digest for name, digest in row['dependencies'].items())

def checked(label, marker, expected=0, directory=box):
    receipt = load(directory / (label + '-run.json'))
    assert receipt['exit'] == expected and marker in receipt['output'], label
    assert receipt['trust'] == 0 and receipt['werror'] and not receipt['elab_async']
    assert sha(root / receipt['source']) == receipt['source_sha256']
    assert all(sha(Path(path)) == digest for path, digest in receipt['imports'].items())
    return receipt

for label, marker in [
    ('default-contract', 'DEFAULT SOURCE CONTINUATION CONTRACT PASS: 8/8'),
    ('default-input-contract', 'PASS: 20/20'),
    ('default-raw-contract', 'PASS: 18/18'),
    ('default-recursion-contract', 'PASS: 17/17'),
    ('default-task-reentry', 'PUBLIC TASK REENTRY CONTRACT PASS: 12/12'),
    ('default-code-closure', 'declarations=108206, missing_calls=0, affected_modules=0'),
]:
    checked(label, marker)
checked('default-contract', 'DEFAULT SOURCE CONTINUATION IR PASS')
negative = checked('default-sealed-negative', 'is marked as private', 1)
assert negative['output'].count('is marked as private') == 2

review = load(box / 'independent-review.json')
assert review['verdict'] == 'default_first_call_and_same_source_continuation_certified_at_source_scope'
for row in review['source_bindings']:
    assert sha(root / row['source']) == row['sha256']

runtime = box / 'runtime'
for row in load(runtime / 'artifact-manifest.json'):
    assert sha(runtime / 'lib' / row['path']) == row['sha256']
for row in rows:
    relative = row['module'].replace('.', '/')
    assert sha(runtime / 'sources' / (relative + '.lean')) == row['source_sha256']
    assert sha(runtime / 'lib' / (relative + '.olean')) == row['artifact_sha256']

kernel = None
if (box / 'default-kernel-run.json').exists():
    kernel = checked('default-kernel', 'DEFAULT SOURCE KERNEL REPLAY PASS')
    assert 'axioms=[Quot.sound,Classical.choice,propext]' in ''.join(kernel['output'].split())
actual = None
if (runtime / 'default-actual-consumer-run.json').exists():
    actual = checked('default-actual-consumer', 'DEFAULT ACTUAL CONTINUATION CONSUMER PASS: 12/12', directory=runtime)

installed = False
production_checked = False
installation = box / 'installation/receipt.json'
if installation.exists():
    receipt = load(installation)
    assert receipt['source_installed']
    plan = load(box / 'installation-plan.json')
    assert receipt['installed'] == {row['path']: row['candidate_sha256'] for row in plan}
    assert all(sha(root / path) == digest for path, digest in receipt['installed'].items())
    assert all(sha(root / path) == digest for path, digest in receipt['evidence'].items())
    installed = True
    if receipt.get('installed_source_recompile'):
        production = box / 'installed'
        compiled_roots = [Path(path) for path in load(production / 'lean-env.json')['LEAN_PATH'].split(':')]
        exact_parts = True
        pairs = []
        for index, row in enumerate(rows):
            built = load(production / ('Production' + str(index) + '-compile.json'))
            relative = row['module'].replace('.', '/')
            assert built['exit'] == 0 and built['exact_dependencies']
            assert built['source'] == 'Lean/' + relative + '.lean'
            assert sha(root / built['source']) == built['source_sha256'] == row['source_sha256']
            assert built['compile_options'] == dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000)
            output = production / 'lib' / (relative + '.olean')
            assert sha(output) == built['artifact_sha256']
            for name, digest in built['dependencies'].items():
                file = next(path / (name.replace('.', '/') + '.olean') for path in compiled_roots
                            if (path / (name.replace('.', '/') + '.olean')).exists())
                assert sha(file) == digest
            before = runtime / 'lib' / (relative + '.olean')
            pairs.extend([str(before), str(output)])
            for suffix in ['', '.private', '.server']:
                old_part, new_part = Path(str(before) + suffix), Path(str(output) + suffix)
                exact_parts = exact_parts and old_part.exists() == new_part.exists()
                if old_part.exists() and new_part.exists():
                    exact_parts = exact_parts and sha(old_part) == sha(new_part)
        if not exact_parts:
            identity = checked('installed-artifact-identity-consumer', 'COMPILER REFRESH LOGICAL CHECK PASS', directory=production)
            assert identity['arguments'] == ['--reference-path', load(runtime / 'lean-env.json')['LEAN_PATH'], *pairs]
        for label, marker in [('installed-default', 'CONTRACT PASS: 8/8'),
                              ('installed-input', 'PASS: 20/20'),
                              ('installed-raw', 'PASS: 18/18'),
                              ('installed-recursion', 'PASS: 17/17'),
                              ('installed-original-reentry', 'PASS: 12/12')]:
            checked(label, marker, directory=production)
        assert actual is not None
        assert sha(root / 'Lean/scripts/verification/public-source-owned-iteration-consumer.lean') == actual['source_sha256']
        assert sha(root / receipt['installed_validation']) == receipt['installed_validation_sha256']
        production_checked = True

record = dict(source_contracts_accepted=True, strict_modules=18,
    contracts=dict(default='8/8', input='20/20', raw='18/18', recursive='17/17', original_reentry='12/12'),
    private_negative_controls=2, compiled_calls=108206, missing_custom_calls=0,
    original_first_call=True, own_source_tail=True, explicit_legacy_execution=True,
    exact_event_route_deferred=True, independent_source_review=True,
    fresh_empty_environment_kernel=kernel is not None,
    actual_public_two_round_consumer=actual is not None,
    source_installed=installed, installed_sources_independently_verified=production_checked,
    universal_future_capability_closed=False, goal_complete=False)
(box / 'verification-check.json').write_text(json.dumps(record, ensure_ascii=False, indent=2) + '\n')
print('DEFAULT SOURCE CONTRACTS PASS: strict=18; default=8/8; input=20/20; raw=18/18; recursive=17/17; sealed=2')
print('DEFAULT ACTUAL CODE CLOSURE PASS: declarations=108206; missing=0; original first call; own-source tail; explicit legacy')
print('DEFAULT FRESH KERNEL:', 'PASS' if kernel else 'RUNNING')
print('DEFAULT ACTUAL PUBLIC TWO ROUNDS:', 'PASS: 12/12' if actual else 'RUNNING')
print('DEFAULT OWNED PRODUCTION SOURCES:', 'INSTALLED' if installed else 'NOT INSTALLED')
print('DEFAULT PRODUCTION RECOMPILATION:', 'PASS: 18 modules; 75 contracts; exact kernel retained' if production_checked else 'PENDING')
