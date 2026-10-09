"""Consume the signed background domain; do not open archives or rerun search."""
from pathlib import Path
from fractions import Fraction as Q
import argparse
import ast
import hashlib
import json
import re
import subprocess

import shared_background_independent_rha0030 as integer

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p/'ComputeNode').is_dir() and (p/'Verification').is_dir())
FIRST = 'shared-background-first-rha0030.json'
ATTEMPT = 'shared-background-first-rha0030-attempt.json'


def frozen(path):
    data = path.read_bytes(); relative = path.relative_to(ROOT).as_posix()
    integer.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', 'HEAD:'+relative]) == data,
                    'unregistered shared-background evidence')
    return data


def bindings(report):
    freeze = report['scientific_freeze_commit']
    integer.require(re.fullmatch('[0-9a-f]{40}', freeze) is not None, 'exact scientific freeze required')
    driver = HERE/'shared_background_run_rha0030.py'
    # Read literal dependency lists without importing the numerical producer.
    assignments = {node.targets[0].id: ast.literal_eval(node.value) for node in ast.parse(driver.read_text()).body
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in ('OWN', 'INPUTS')}
    paths = [(HERE/name).resolve() for name in (*assignments['OWN'], *assignments['INPUTS'])]
    expected = {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    integer.require(report['source_bindings'] == expected, 'registered background source dependency set changed')
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        integer.require(subprocess.check_output(['git', '-C', str(ROOT), 'show', freeze+':'+relative]) == path.read_bytes(),
                        'shared-background source changed after science freeze: '+relative)
    return expected


def summarize(domain):
    nodes = domain['nodes']; excluded = [n for n in nodes if n['decision'] == 'excluded']
    retained = [n for n in nodes if n['decision'] == 'unresolved']; area = Q(0); cells = set()
    upper_a = upper_b = Q(0)
    for node in retained:
        ((lo_a, hi_a), (lo_b, hi_b)) = tuple(tuple(map(Q, row)) for row in node['box'])
        area += (hi_a-lo_a)*(hi_b-lo_b); upper_a = max(upper_a, hi_a); upper_b = max(upper_b, hi_b)
        for i in range(int(lo_a*128), int(hi_a*128)):
            for j in range(int(lo_b*128), int(hi_b*128)): cells.add((i, j))
    return {'physical_click_code': domain['physical_click_code'], 'tree_nodes': len(nodes),
        'excluded_cells': len(excluded), 'joint_positive_birth_exclusions': sum(n['proof']['face'] == 'joint' for n in excluded),
        'unresolved_cells': len(retained), 'unresolved_background_area': str(area),
        'background_upper': list(map(str, (upper_a, upper_b)))}, cells


def consume(directory=HERE):
    directory = Path(directory); original, attempt_data = frozen(HERE/FIRST), frozen(HERE/ATTEMPT)
    integer.require((directory/FIRST).read_bytes() == original and (directory/ATTEMPT).read_bytes() == attempt_data,
                    'relocated shared-background evidence changed')
    report, attempt = json.loads(original), json.loads(attempt_data); expected = bindings(report)
    integer.require(attempt == {'scientific_freeze_commit': report['scientific_freeze_commit'], 'source_bindings': expected},
                    'registered first-attempt binding changed')
    integer.check_header(report); checked = report['independent_report']; runs = []
    integer.require(checked['schema'] == 'stage10-independent-shared-background-domain/rha0030' and
        checked['integer_corner_log_prices_checked'] is True and checked['family_alpha'] == '1/20' and
        checked['unknown_encoder_handled_by_confidence_parameter_inversion'] is True and
        all(checked[name] is False for name in ('background_member_identified', 'actual_hardware_uniquely_identified', 'controller_advance')) and
        len(report['runs']) == len(checked['runs']) == 2, 'independent whole-domain evidence missing')
    for saved, independent in zip(report['runs'], checked['runs']):
        integer.require(saved['run'] == independent['run'] and saved['trials'] == independent['trials'] and
            saved['complete_pair_history_address_sha256'] == independent['complete_pair_history_address_sha256'] and
            independent['independent_original_prefix_witnesses_checked'] is True and independent['complete_quadtree_cover_checked'] is True,
            'complete original record or whole-domain certificate changed')
        integer.require([d['physical_click_code'] for d in saved['encoders']] == [[0, 0], [0, 1], [1, 0], [1, 1]],
                        'every original encoder branch required')
        domains = []; union = set()
        for domain in saved['encoders']:
            summary, cells = summarize(domain); domains.append(summary); union.update(cells)
        integer.require(domains == independent['encoders'] and str(Q(len(union), 128*128)) == independent['all_encoder_union_background_area'],
                        'signed background-domain summary changed')
        runs.append({'run': saved['run'], 'trials': saved['trials'], 'encoders': domains,
            'all_encoder_union_background_area': independent['all_encoder_union_background_area']})
    return {'schema': 'stage10-shared-background-domain-intake/rha0030', 'status': 'independent_background_domain_admitted',
        'evidence_valid': True, 'source_identity': report['source_identity'], 'family_alpha': '1/20', 'runs': runs,
        'history_conditioned_background_domain_certified': True, 'history_dependent_probabilities_allowed': True,
        'all_encoder_branches_and_complete_quadtree_checked': True, 'background_member_identified': False,
        'actual_raw_source_history_membership_certified': False, 'actual_hardware_uniquely_identified': False,
        'old_and_new_gate_intersection_claimed_as_one_95pct_domain': False, 'archive_files_read_at_intake': 0,
        'new_statistical_replays_at_intake': 0, 'new_atomic_solves_at_intake': 0,
        'receipt_sha256': hashlib.sha256(original).hexdigest(), 'controller_advance': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--check-only', action='store_true', required=True)
    parser.add_argument('--directory', type=Path, default=HERE); args = parser.parse_args()
    try:
        result = consume(args.directory)
    except Exception as error:
        print(json.dumps({'status': 'rejected', 'evidence_valid': False, 'reason': str(error)})); raise SystemExit(1)
    print(json.dumps(result, sort_keys=True))
