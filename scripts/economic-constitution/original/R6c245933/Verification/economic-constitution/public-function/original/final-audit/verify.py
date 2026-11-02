from pathlib import Path
import hashlib
import json
import subprocess

root = Path('runtime/Documents/Homework')
box = Path(__file__).absolute().parent
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
load = lambda path: json.loads(path.read_text())
config = load(box / 'lean-env.json')
roots = [Path(path) for path in config['LEAN_PATH'].split(':')]

def artifact(module):
    relative = Path(module.replace('.', '/') + '.olean')
    return next(directory / relative for directory in roots if (directory / relative).exists())

for index in range(3):
    record = load(box / ('RentCurrent' + str(index) + '-compile.json'))
    assert record['exit'] == 0 and record['exact_dependencies']
    assert record['compile_options'] == dict(trust=0, werror=True, elab_async=False, threads=1, memory_mb=12000)
    assert sha(root / record['source']) == record['source_sha256']
    assert sha(artifact(record['module'])) == record['artifact_sha256']
    assert all(sha(artifact(name)) == wanted for name, wanted in record['dependencies'].items())
mouths = load(box / 'final-rent-mouths-current-run.json')
assert mouths['exit'] == 0 and mouths['trust'] == 0 and mouths['werror'] and not mouths['elab_async']
assert sha(root / mouths['source']) == mouths['source_sha256']
assert all(sha(Path(path)) == wanted for path, wanted in mouths['imports'].items())
assert mouths['output'].count('depends on axioms: [propext,\n Classical.choice,\n Quot.sound]') == 6
assert 'FINAL RENT SOURCE MOUTHS PASS' in mouths['output']
history = load(box / 'rent-historical-evidence.json')
commit = history['accepted_scientific_commit']
for path, wanted in history['current_sources_match_scientific_commit'].items():
    assert sha(root / path) == wanted
    frozen = subprocess.check_output(['git', 'show', commit + ':' + path], cwd=root)
    assert hashlib.sha256(frozen).hexdigest() == wanted
historical = root / '.agents/tmp/public-inwindow-burden-20261029/final-verification.json'
assert sha(historical) == history['historical_verification_sha256']
accepted = load(historical)
assert accepted['status'] == 'PASS' and accepted['commit'] == commit
assert accepted['strict_modules'] == 10 and accepted['independent_review'] == 'ACCEPT'
assert 'roots=466 closure=17428 private=1542' in accepted['kernel']
current = load(box / 'verification-check.json')
assert current['rent_source_and_original_consumer_accepted'] and not current['authority_minted_by_stability']
print('FULL COST RENT BOUND PASS: 3 current strict modules; 6 original source mouths; standard three axioms; 10 sources match the accepted scientific commit')
print('ACTUAL COST EVIDENCE PASS: original nonempty self service and three-unit compensation; own paid window and source-computed finite-domain stability retained')
