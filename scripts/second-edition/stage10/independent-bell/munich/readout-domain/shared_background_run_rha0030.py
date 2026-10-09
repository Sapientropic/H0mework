"""Freeze-bound one-shot original archive replay and independent verification."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

import shared_background_rha0030 as primary
import shared_background_independent_rha0030 as independent

OWN = ('criterion-rha0030.md', 'SharedCEMBackground.lean', 'shared_background_rha0030.py',
    'shared_background_independent_rha0030.py', 'shared_background_run_rha0030.py',
    'test_shared_background_rha0030.py', 'shared-background-math-certification-rha0030.json')
INPUTS = ('likelihood.py', 'independent.py', '../schema.py', '../invariant_independent.py', '../sources.json',
    'candidate_record_response.py', 'window_cem_source.py', 'history-occupation-first-rha0029.json')


def bindings(freeze):
    result = {}
    for name in (*OWN, *INPUTS):
        path = (primary.HERE/name).resolve(); relative = path.relative_to(primary.ROOT).as_posix(); data = path.read_bytes()
        frozen = subprocess.check_output(['git', '-C', str(primary.ROOT), 'show', freeze+':'+relative])
        primary.require(data == frozen, 'shared-background source changed after freeze: '+name)
        result[relative] = hashlib.sha256(data).hexdigest()
    return result


def execute(freeze, directory, output):
    bound = bindings(freeze); output = Path(output)
    primary.require(not output.exists(), 'the first shared-background receipt is immutable')
    attempt = output.with_name(output.stem+'-attempt.json')
    with attempt.open('x') as handle:
        json.dump({'scientific_freeze_commit': freeze, 'source_bindings': bound}, handle, sort_keys=True); handle.write('\n')
    try:
        report = primary.generate(directory)
        checked = independent.check(report, directory)
    except Exception as error:
        with output.open('x') as handle:
            json.dump({'schema': primary.SCHEMA+'/failed-attempt', 'status': 'generation_or_check_failed',
                'reason': str(error), 'scientific_freeze_commit': freeze, 'source_bindings': bound}, handle, sort_keys=True)
            handle.write('\n')
        raise
    report.update(scientific_freeze_commit=freeze, source_bindings=bound, independent_report=checked)
    with output.open('x') as handle:
        json.dump(report, handle, sort_keys=True, separators=(',', ':')); handle.write('\n')
    print(json.dumps({'independent_check_passed': True, 'runs': checked['runs'],
        'actual_hardware_uniquely_identified': False}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True)
    parser.add_argument('--directory', type=Path, required=True); parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); execute(args.freeze, args.directory, args.output)
