"""Apply the frozen whole-receipt bounds to the completed current inlet."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import time

import completed_retarded_inlet_rha0028 as paid
import retarded_complete_receipt_normalizer_rha0028 as code
import retarded_normalizer_independent_rha0028 as independent

SCIENCE = ('criterion-rha0028.md', 'criterion-rha0028.1.md', 'criterion-rha0028.2.md', 'criterion-rha0028.3.md',
    'criterion-rha0028.4.md',
    'completed_retarded_inlet_rha0028.py', 'retarded-normalizer-primary-first-rha0028.json',
    'retarded_complete_receipt_normalizer_rha0028.py', 'retarded_normalizer_run_rha0028.py',
    'retarded_normalizer_independent_rha0028.py',
    'test_retarded_normalizer_rha0028.py', 'retarded-inlet-first-rha0027.json',
    'retarded_empty_receipt_time_measure.py', 'retarded_receipt_activity_envelope.py')


def write(path, value):
    with path.open('x') as handle:
        json.dump(value, handle, sort_keys=True); handle.write('\n')


def completed_primary():
    receipt = json.loads(paid.paid.frozen(paid.HERE/'retarded-normalizer-primary-first-rha0028.json'))
    paid.paid.require(receipt['schema'] == 'stage10-completed-primary-retarded-normalizer-evidence/rha0028' and
        receipt['scientific_freeze_commit'] == '318af56c37331e6732a3c52e4deba3e3aad47cf7' and
        receipt['scope']['complete_primary_bound_written'] is True and
        receipt['scope']['independent_check_passed'] is False, 'completed primary evidence scope changed')
    for name in ('completed_retarded_inlet_rha0028.py', 'retarded_complete_receipt_normalizer_rha0028.py',
                 'retarded_empty_receipt_time_measure.py', 'retarded_receipt_activity_envelope.py'):
        path = paid.HERE/name; relative = path.relative_to(paid.ROOT).as_posix()
        paid.paid.require(hashlib.sha256(paid.paid.frozen(path, receipt['scientific_freeze_commit'])).hexdigest() ==
            receipt['source_bindings'][relative], 'completed primary mathematical inputs changed')
    report = paid._artifact(receipt['primary_report'], None)
    _, payload = paid.consume()
    paid.paid.require(report['source_record'] == payload['source_record'] and
        report['whole_first_receipt_mass_interval'] == receipt['whole_first_receipt_mass_interval'] and
        report['four_pattern_mass_bounds'] == receipt['four_pattern_mass_bounds'],
        'completed primary no longer belongs to the paid current inlet')
    return report


def execute(freeze, output, *, reuse_completed_primary=False):
    bindings = {}
    for name in SCIENCE:
        path = paid.HERE/name; data = path.read_bytes(); relative = path.relative_to(paid.ROOT).as_posix()
        paid.paid.require(subprocess.check_output(['git', '-C', str(paid.ROOT), 'show', freeze+':'+relative]) == data,
                          'whole-gate normalizer differs from its scientific freeze: '+name)
        bindings[relative] = hashlib.sha256(data).hexdigest()
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    write(output/'attempt.json', {'scientific_freeze_commit': freeze, 'source_bindings': bindings})
    if reuse_completed_primary:
        report = completed_primary()
        print('reusing the completed frozen whole-gate primary; checking its independent prices', flush=True)
    else:
        source = paid.restore()
        print('restored the current complete retarded inlet; no new pump or density residual', flush=True)
        report = code.bounds(source)
    path = output/'complete-normalizer.json'; write(path, report)
    independent_report = independent.certify(report)
    independent_path = output/'independent-normalizer.json'; write(independent_path, independent_report)
    summary = {key: report[key] for key in ('receipt_interval_seconds', 'whole_first_receipt_mass_interval',
        'four_pattern_mass_bounds', 'whole_first_receipt_strictly_positive', 'four_pattern_masses_strictly_positive',
        'complete_gate_state_or_response_difference_computed', 'generation1_asserted',
        'actual_hardware_member_asserted', 'actual_hardware_uniquely_identified', 'controller_advance')}
    summary.update({'schema': 'stage10-complete-retarded-receipt-normalizer-first/rha0028',
        'scientific_freeze_commit': freeze, 'source_bindings': bindings,
        'paid_current_inlet_first_sha256': hashlib.sha256(paid.FIRST.read_bytes()).hexdigest(),
        'report': {'path': path.relative_to(paid.ROOT).as_posix(), 'bytes': path.stat().st_size,
            'sha256': hashlib.sha256(path.read_bytes()).hexdigest()},
        'independent_report': {'path': independent_path.relative_to(paid.ROOT).as_posix(),
            'bytes': independent_path.stat().st_size, 'sha256': hashlib.sha256(independent_path.read_bytes()).hexdigest()},
        'independent_rational_Mark_flow_and_raw_factor_contraction_passed': True,
        'completed_primary_evidence_reused': reuse_completed_primary,
        'seconds': time.monotonic()-started})
    write(output/'summary.json', summary); print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--freeze', required=True); parser.add_argument('--output', required=True)
    parser.add_argument('--reuse-completed-primary', action='store_true')
    args = parser.parse_args(); execute(args.freeze, args.output, reuse_completed_primary=args.reuse_completed_primary)
