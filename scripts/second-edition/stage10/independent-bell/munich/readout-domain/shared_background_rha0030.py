"""Source-positive e-factors prune whole background rectangles at true prefixes.

The floating prefix search only proposes an exclusion witness.  Every
exclusion is paid by exact rational corner factors and outward log prices.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

import numpy as np
from likelihood import Directed

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p/'ComputeNode').is_dir() and (p/'Verification').is_dir())
SCHEMA = 'stage10-history-shared-CEM-background-domain/rha0030'
TILTS = tuple(Q(1, 1 << k) for k in range(7, -1, -1))
FACES = ('alice', 'bob', 'joint')
MAX_DEPTH = 7
GRID_BITS = 192
GRID = 1 << GRID_BITS
FAMILY_SIZE_PER_FIXED_ENCODER = 2*8*3*len(TILTS)
ALPHA = Q(1, 20)
THRESHOLD = FAMILY_SIZE_PER_FIXED_ENCODER/ALPHA
SOURCE_ID = {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10, 'current_tick': 16, 'next_tick': 17}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def parser(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE.parent/filename)
    result = importlib.util.module_from_spec(spec); sys.modules[name] = result; spec.loader.exec_module(result)
    return result


def factor(face, tilt, code, event, a, b):
    x, y = int(event//2 == code[0]), int(event % 2 == code[1])
    z = x-a if face == 'alice' else y-b if face == 'bob' else (x-a)*(y-b)
    return 1-tilt*z


def minimum_factors(box, face, tilt, code):
    return tuple(min(factor(face, tilt, code, event, a, b) for a, b in product(*box)) for event in range(4))


class Prices:
    def __init__(self):
        self.arithmetic = Directed(80); self.cache = {Q(1): 0}
        value = Q(self.arithmetic.logarithm(THRESHOLD).upper)*GRID
        self.threshold = -((-value).__floor__())

    def log_lower(self, value):
        require(value > 0, 'positive whole-cell factor required')
        if value not in self.cache:
            self.cache[value] = (Q(self.arithmetic.logarithm(value).lower)*GRID).__floor__()
        return self.cache[value]


def address(trial, index):
    return {'global_pair_prefix': index, 'original_pair_row': trial.row, 'unix_milliseconds': str(trial.time_ms),
            'local_rows': [trial.row_a, trial.row_b], 'context': [trial.h, trial.a, trial.b]}


def histories(trials):
    counts = [[0]*4 for _ in range(8)]; banks = [[] for _ in range(8)]; by_prefix = {}
    for index, trial in enumerate(trials, 1):
        c = 4*trial.h+2*trial.a+trial.b; counts[c][2*trial.x+trial.y] += 1
        row = {'context_index': c, 'counts': tuple(counts[c]), 'source_address': address(trial, index)}
        banks[c].append(row); by_prefix[index] = row
    require(all(banks), 'all eight original contexts required')
    support = []
    for bank in banks:
        indices = set(range(min(128, len(bank))))
        indices.update(int(i) for i in np.linspace(0, len(bank)-1, min(256, len(bank))))
        support.extend(bank[i] for i in sorted(indices))
    return {'by_prefix': by_prefix, 'terminal_context_counts': counts, 'support': support,
        'support_matrix': np.array([row['counts'] for row in support], dtype=np.float64)}


def witness(history, box, code, prices):
    families = []; coefficients = []
    for face, k in product(FACES, range(len(TILTS))):
        factors = minimum_factors(box, face, TILTS[k], code)
        if min(factors) <= 0:
            continue
        lower = tuple(prices.log_lower(value) for value in factors)
        families.append((face, k, factors, lower)); coefficients.append([float(Q(value, GRID)) for value in lower])
    if not families:
        return None
    scores = history['support_matrix']@np.array(coefficients).T
    position, family = np.unravel_index(int(np.argmax(scores)), scores.shape)
    row = history['support'][position]; face, k, factors, lower = families[family]
    exact = sum(n*c for n, c in zip(row['counts'], lower))
    if exact < prices.threshold:
        return None
    return {'context_index': row['context_index'], 'source_address': row['source_address'],
        'counts': list(row['counts']), 'face': face, 'tilt_index': k,
        'whole_cell_factor_lower': list(map(str, factors)), 'log_factor_lower_scaled': list(map(str, lower)),
        'log_capital_lower_scaled': str(exact)}


def children(box):
    (a, b), (c, d) = box; x, y = (a+b)/2, (c+d)/2
    return (((a, x), (c, y)), ((a, x), (y, d)), ((x, b), (c, y)), ((x, b), (y, d)))


def tree(history, code, prices, *, maximum_depth=MAX_DEPTH):
    require(type(maximum_depth) is int and 0 <= maximum_depth <= MAX_DEPTH, 'registered finite tree budget required')
    def visit(path, box):
        proof = witness(history, box, code, prices)
        node = {'path': path, 'box': [list(map(str, row)) for row in box]}
        if proof is not None:
            node.update(decision='excluded', proof=proof)
            return [node]
        elif len(path) == maximum_depth:
            node['decision'] = 'unresolved'
            return [node]
        else:
            node['decision'] = 'split'
        descendants = [visit(path+str(digit), child) for digit, child in enumerate(children(box))]
        if all(len(rows) == 1 and rows[0]['decision'] == 'unresolved' for rows in descendants):
            node['decision'] = 'unresolved'
            return [node]
        return [node, *(row for rows in descendants for row in rows)]
    nodes = visit('', ((Q(0), Q(1)), (Q(0), Q(1))))
    retained_area = sum((Q(n['box'][0][1])-Q(n['box'][0][0]))*(Q(n['box'][1][1])-Q(n['box'][1][0]))
                        for n in nodes if n['decision'] == 'unresolved')
    excluded = sum(n['decision'] == 'excluded' for n in nodes)
    unresolved = sum(n['decision'] == 'unresolved' for n in nodes)
    return {'physical_click_code': list(code), 'maximum_depth': maximum_depth, 'nodes': nodes,
        'excluded_leaf_count': excluded, 'unresolved_leaf_count': unresolved,
        'unresolved_background_area': str(retained_area), 'unresolved_cells_are_membership_certificates': False}


def record_sha(trials):
    digest = hashlib.sha256()
    for t in trials:
        digest.update((','.join(map(str, (t.row, t.time_ms, t.row_a, t.row_b, t.h, t.a, t.b, t.x, t.y)))+'\n').encode('ascii'))
    return digest.hexdigest()


def generate(directory):
    module = parser('_shared_background_primary_schema', 'schema.py')
    previous = json.loads((HERE/'history-occupation-first-rha0029.json').read_text())
    prices = Prices(); runs = []
    for spec, parent in zip(module.ARCHIVES, previous['runs']):
        admitted = module.admit_archive(Path(directory), spec); sha = record_sha(admitted.trials)
        require(admitted.run == parent['run'] and len(admitted.trials) == parent['trials'] and
            sha == parent['complete_pair_history_address_sha256'], 'original complete record history changed')
        history = histories(admitted.trials)
        domains = [tree(history, code, prices) for code in product((0, 1), repeat=2)]
        runs.append({'run': admitted.run, 'trials': len(admitted.trials),
            'complete_pair_history_address_sha256': sha, 'original_join_audit': admitted.audit,
            'token_dictionaries': admitted.token_dictionaries,
            'terminal_context_counts': history['terminal_context_counts'], 'encoders': domains})
        print(json.dumps({'run': admitted.run, 'encoders': [{'code': d['physical_click_code'],
            'excluded': d['excluded_leaf_count'], 'unresolved': d['unresolved_leaf_count'],
            'retained_area': float(Q(d['unresolved_background_area']))} for d in domains]}), flush=True)
    return {'schema': SCHEMA, 'source_identity': SOURCE_ID, 'family_alpha': str(ALPHA),
        'family_size_per_fixed_encoder': FAMILY_SIZE_PER_FIXED_ENCODER,
        'capital_threshold': str(THRESHOLD), 'threshold_log_upper_scaled': str(prices.threshold),
        'grid_bits': GRID_BITS, 'maximum_depth': MAX_DEPTH, 'tilts': list(map(str, TILTS)), 'faces': list(FACES),
        'runs': runs, 'history_dependent_probabilities_allowed': True, 'constant_quantum_input_assumed': False,
        'continuous_background_rectangles_excluded': True, 'all_four_encoders_preserved': True,
        'floating_prefix_search_used_only_to_propose_a_checked_prefix': True,
        'domain_is_outer_approximation': True, 'background_member_identified': False,
        'old_and_new_gate_intersection_claimed_as_one_95pct_domain': False,
        'actual_hardware_uniquely_identified': False, 'controller_advance': False}
