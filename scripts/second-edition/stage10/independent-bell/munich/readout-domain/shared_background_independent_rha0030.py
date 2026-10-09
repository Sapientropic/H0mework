"""Check whole-cell witnesses against independently parsed original prefixes.

No primary factor, tree search, Decimal logarithm or matrix product is
imported.  Unresolved cells constitute an outer domain, not admitted members.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

from independent import Arithmetic

HERE = Path(__file__).resolve().parent
GRID = 1 << 192
TILTS = tuple(Q(1, 1 << k) for k in range(7, -1, -1))
FACES = ('alice', 'bob', 'joint')


def require(value, reason):
    if not value:
        raise ValueError(reason)


def minimum_factors(box, face, tilt, code):
    result = []
    for event in range(4):
        x = (event >> 1) ^ (1-code[0]); y = (event & 1) ^ (1-code[1])
        xs = (x-box[0][1], x-box[0][0]); ys = (y-box[1][1], y-box[1][0])
        maximum = xs[1] if face == 'alice' else ys[1] if face == 'bob' else max(
            xs[0]*ys[0], xs[0]*ys[1], xs[1]*ys[0], xs[1]*ys[1])
        result.append(1-tilt*maximum)
    return tuple(result)


def prefixes(trials):
    counts = [[0, 0, 0, 0] for _ in range(8)]; result = {}; digest = hashlib.sha256()
    previous_a = previous_b = -1
    for index, trial in enumerate(trials, 1):
        require(trial.row_a > previous_a and trial.row_b > previous_b, 'original local order changed')
        previous_a, previous_b = trial.row_a, trial.row_b
        context = trial.h*4+trial.a*2+trial.b; counts[context][trial.x*2+trial.y] += 1
        address = {'global_pair_prefix': index, 'original_pair_row': trial.row,
            'unix_milliseconds': str(trial.time_ms), 'local_rows': [trial.row_a, trial.row_b],
            'context': [trial.h, trial.a, trial.b]}
        result[index] = (context, list(counts[context]), address)
        digest.update((','.join(str(v) for v in (trial.row, trial.time_ms, trial.row_a, trial.row_b,
            trial.h, trial.a, trial.b, trial.x, trial.y))+'\n').encode('ascii'))
    return result, counts, digest.hexdigest()


class LogCheck:
    def __init__(self):
        self.arithmetic = Arithmetic(384); self.cache = {}
        self.threshold = self.arithmetic.log(Q(7680))

    def lower(self, value):
        if value not in self.cache:
            self.cache[value] = self.arithmetic.log(value).lo
        return Q(self.cache[value], self.arithmetic.scale)


def check_witness(proof, box, code, history, logcheck, threshold):
    require(proof['face'] in FACES and type(proof['tilt_index']) is int and 0 <= proof['tilt_index'] < 8,
            'registered source face or tilt required')
    expected = minimum_factors(box, proof['face'], TILTS[proof['tilt_index']], code)
    require(min(expected) > 0 and proof['whole_cell_factor_lower'] == list(map(str, expected)),
            'whole-cell factor lower bound changed')
    index = proof['source_address']['global_pair_prefix']
    require(type(index) is int and index in history, 'original source prefix required')
    context, counts, address = history[index]
    require(proof['context_index'] == context and proof['counts'] == counts and proof['source_address'] == address,
            'original prefix count, context, clock or address changed')
    lower = list(map(int, proof['log_factor_lower_scaled']))
    require(len(lower) == 4 and all(Q(c, GRID) <= logcheck.lower(v) for c, v in zip(lower, expected)),
            'outward whole-cell log coefficient changed')
    score = sum(n*c for n, c in zip(counts, lower))
    require(score == int(proof['log_capital_lower_scaled']) and score >= threshold,
            'whole-cell exclusion capital is not paid')


def check_tree(domain, history, logcheck, threshold):
    code = domain['physical_click_code']; depth = domain['maximum_depth']
    require(code in [[0, 0], [0, 1], [1, 0], [1, 1]] and type(depth) is int and 0 <= depth <= 7,
            'registered encoder and finite tree budget required')
    require(domain['unresolved_cells_are_membership_certificates'] is False, 'unresolved source scope promoted')
    nodes = domain['nodes']; lookup = {}
    for node in nodes:
        require(node['path'] not in lookup, 'duplicate quadtree address')
        lookup[node['path']] = node
    seen = set(); area = Q(0); excluded = unresolved = joint = 0; upper_a = upper_b = Q(0)
    cells = set()
    def visit(path, bounds):
        nonlocal area, excluded, unresolved, joint, upper_a, upper_b
        require(path in lookup and len(path) <= depth, 'incomplete quadtree cover')
        node = lookup[path]; seen.add(path)
        require(node['box'] == [list(map(str, row)) for row in bounds], 'background rectangle changed')
        decision = node['decision']
        if decision == 'excluded':
            check_witness(node['proof'], bounds, code, history, logcheck, threshold)
            excluded += 1; joint += int(node['proof']['face'] == 'joint')
        elif decision == 'unresolved':
            unresolved += 1
            area += (bounds[0][1]-bounds[0][0])*(bounds[1][1]-bounds[1][0])
            upper_a = max(upper_a, bounds[0][1]); upper_b = max(upper_b, bounds[1][1])
            for i in range(int(bounds[0][0]*128), int(bounds[0][1]*128)):
                for j in range(int(bounds[1][0]*128), int(bounds[1][1]*128)): cells.add((i, j))
        else:
            require(decision == 'split' and len(path) < depth, 'invalid quadtree decision')
            lo_a, hi_a = bounds[0]; lo_b, hi_b = bounds[1]
            mid_a, mid_b = (lo_a+hi_a)/2, (lo_b+hi_b)/2
            for digit in range(4):
                x = (lo_a, mid_a) if digit < 2 else (mid_a, hi_a)
                y = (lo_b, mid_b) if digit % 2 == 0 else (mid_b, hi_b)
                visit(path+str(digit), (x, y))
    visit('', ((Q(0), Q(1)), (Q(0), Q(1))))
    require(len(seen) == len(nodes) and excluded == domain['excluded_leaf_count'] and
        unresolved == domain['unresolved_leaf_count'] and str(area) == domain['unresolved_background_area'],
        'extra tree nodes, leaf inventory or retained area changed')
    return {'physical_click_code': code, 'tree_nodes': len(nodes), 'excluded_cells': excluded,
        'joint_positive_birth_exclusions': joint, 'unresolved_cells': unresolved,
        'unresolved_background_area': str(area), 'background_upper': list(map(str, (upper_a, upper_b)))}, cells


def check_header(report):
    require(report['schema'] == 'stage10-history-shared-CEM-background-domain/rha0030' and
        report['family_alpha'] == '1/20' and report['family_size_per_fixed_encoder'] == 384 and
        report['capital_threshold'] == '7680' and report['grid_bits'] == 192 and report['maximum_depth'] == 7 and
        report['tilts'] == list(map(str, TILTS)) and report['faces'] == list(FACES), 'registered background family changed')
    require(report['source_identity'] == {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10,
        'current_tick': 16, 'next_tick': 17}, 'same physical occurrence changed')
    for name in ('history_dependent_probabilities_allowed', 'continuous_background_rectangles_excluded',
        'all_four_encoders_preserved', 'floating_prefix_search_used_only_to_propose_a_checked_prefix', 'domain_is_outer_approximation'):
        require(report[name] is True, 'background domain scope missing: '+name)
    for name in ('constant_quantum_input_assumed', 'background_member_identified',
        'old_and_new_gate_intersection_claimed_as_one_95pct_domain', 'actual_hardware_uniquely_identified', 'controller_advance'):
        require(report[name] is False, 'background domain scope promoted: '+name)
    logs = LogCheck(); threshold = int(report['threshold_log_upper_scaled'])
    require(Q(threshold, GRID) >= Q(logs.threshold.hi, logs.arithmetic.scale), 'threshold log must be an upper bound')
    return logs, threshold


def check(report, directory):
    logs, threshold = check_header(report)
    spec = importlib.util.spec_from_file_location('_shared_background_independent_schema', HERE.parent/'invariant_independent.py')
    module = importlib.util.module_from_spec(spec); sys.modules[spec.name] = module; spec.loader.exec_module(module)
    previous = json.loads((HERE/'history-occupation-first-rha0029.json').read_text()); runs = []
    require(len(report['runs']) == len(module.ARCHIVE_IDENTITIES) == len(previous['runs']) == 2, 'both complete archives required')
    for saved, identity, parent in zip(report['runs'], module.ARCHIVE_IDENTITIES, previous['runs']):
        admitted = module.archive_run((Path(directory)/identity['name']).read_bytes(), identity)
        history, counts, sha = prefixes(admitted.trials)
        require(saved['run'] == admitted.run == parent['run'] and saved['trials'] == len(admitted.trials) == parent['trials'] and
            saved['complete_pair_history_address_sha256'] == sha == parent['complete_pair_history_address_sha256'] and
            saved['token_dictionaries'] == admitted.token_dictionaries and saved['terminal_context_counts'] == counts,
            'complete independent original source history changed')
        require([d['physical_click_code'] for d in saved['encoders']] == [[0, 0], [0, 1], [1, 0], [1, 1]] and
            all(d['maximum_depth'] == 7 for d in saved['encoders']), 'all four complete encoder branches required')
        domains = []; union = set()
        for domain in saved['encoders']:
            checked, cells = check_tree(domain, history, logs, threshold); domains.append(checked); union.update(cells)
        runs.append({'run': admitted.run, 'trials': len(admitted.trials),
            'complete_pair_history_address_sha256': sha, 'original_independent_join_audit': admitted.audit,
            'encoders': domains, 'all_encoder_union_background_area': str(Q(len(union), 128*128)),
            'independent_original_prefix_witnesses_checked': True, 'complete_quadtree_cover_checked': True})
    return {'schema': 'stage10-independent-shared-background-domain/rha0030', 'runs': runs,
        'integer_corner_log_prices_checked': True, 'family_alpha': '1/20',
        'unknown_encoder_handled_by_confidence_parameter_inversion': True,
        'background_member_identified': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
