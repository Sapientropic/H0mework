#!/usr/bin/env python3
"""Check the existing source-domain witness; never generate a tree or native source."""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import time

HERE = Path(__file__).resolve().parent
SCHEMA = 'p23-source-compression-domain-certification/v1'
VERSION = 'p23-public-source-compression-sc0001'
POSITIVE = ('evidence_valid', 'complete_source_outer_cover_certified', 'new_constraints_checked',
            'nonempty_source_fibre_exhibited', 'all_72_original_CI_preserved',
            'uniform_CH_N5_lower_bound_certified')
NEGATIVE = ('actual_source_epoch_or_hardware_identified', 'actual_hardware_identity_claimed',
            'publication_configuration_identified', 'controller_advance',
            'new_full_Born_kernel_claim', 'new_stochastic_process_or_Ville_kernel',
            'original_CI_modified', 'old_source_search_rerun', 'retained_leaves_are_members',
            'posthoc_CH_positive_filter_used', 'finite_prefix_renormalized')
SHARED_HELPERS = ['independent_fiber.I directed 50-place arithmetic',
    'independent_fiber.constants/linear_constraints/linear_contract/population/geometry/padd/pscale',
    'source_independent.common_phase/window_single/window_joint_coefficients',
    'domain.old_material file extraction only; no domain.refine/members/generate/Fock call']


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


@lru_cache(maxsize=1)
def modules():
    import domain as d
    # Legacy source imports insert their directory ahead of this one.
    v = d.statistics.module('_sc_domain_certification_intake', HERE/'verify.py')
    s = d.statistics.module('_sc_domain_statistics_intake', HERE/'statistics_verify.py')
    return d, v, s


def integer(value, minimum=0):
    require(type(value) is int and value >= minimum, 'literal_integer_required')
    return value


def interval(packet):
    d, _, _ = modules()
    require(type(packet) is dict and all(type(packet.get(k)) is str
            for k in ('exact_lower', 'exact_upper')), 'exact_interval_strings_required')
    a, b = F(packet['exact_lower']), F(packet['exact_upper'])
    require(a <= b, 'reversed_exact_interval')
    return d.I(a, b)


def equal(left, right, reason):
    require(left == right, reason)


def serialized(value):
    return modules()[0].geometry.serial(value)


def binding_check(row):
    d, _, s = modules()
    require(type(row) is dict and all(type(row.get(k)) is str for k in ('path', 'commit', 'sha256')),
            'literal_binding_required')
    path = PurePosixPath(row['path'])
    require(not path.is_absolute() and '..' not in path.parts
            and (d.ROOT / row['path']).resolve().is_relative_to(d.ROOT), 'foreign_bound_source')
    s.binding_check(row)


def check_scope(report):
    require(report['schema'] == 'p23-source-compression-domain/v1' and report['version'] == VERSION,
            'wrong_domain_schema')
    for name in ('complete_source_outer_cover_generated', 'nonempty_source_fibre_exhibited',
                 'all_72_old_CI_preserved', 'all_96_conditional_constraints_consumed',
                 'all_4_joint_source_h_cuts_consumed', 'source_stationarity_is_named_model_condition', 'retrospective'):
        require(report[name] is True, 'domain_true_scope_changed:' + name)
    for name in ('empty_source_fibre_certified', 'retained_leaves_are_members', 'old_source_search_rerun',
                 'posthoc_CH_positive_filter_used', 'finite_prefix_renormalized',
                 'publication_configuration_identified', 'actual_epoch_identified', 'controller_advance'):
        require(report[name] is False, 'domain_false_scope_changed:' + name)
    require(integer(report['bell_event_files_read']) == 0, 'raw_event_intake_forbidden')
    equal(report['member_search'], {'candidate_count': 0, 'fresh_Fock_evaluations': 0,
          'performed': False, 'selection_exhausted': False}, 'unexpected_source_or_Fock_search')


def check_means(report, old, records, const):
    d, _, _ = modules()
    equal(report['old_native_mean_domain'], serialized(old), 'old_mean_domain_changed')
    current, expected, position = list(old), [], 0
    for index, feature, rows, bg in ((0, 4, (0, 1), const['background'][0]),
                                  (1, 5, (0, 2), const['background'][1]),
                                  (2, 4, (2, 3), const['background'][0]),
                                  (3, 5, (1, 3), const['background'][1])):
        for record in records:
            n = record['identity']['pulse_count']
            for row in rows:
                witness = report['mean_contractions'][position]
                position += 1
                equal((witness['mean_index'], witness['N'], witness['row']), (index, n, row), 'mean_witness_order_changed')
                equal(witness['original_mean'], serialized(current[index]), 'mean_contraction_chain_broken')
                packet = record['conditional'][row][feature]['interval']
                p = interval(packet).intersect(d.I(0, 1))
                require(p is not None, 'nonphysical_conditional_single')
                proof = witness['proof']
                equal(proof['single_interval'], serialized(p), 'single_packet_changed')
                lower, upper = interval(proof['no_click_root_lower']), interval(proof['no_click_root_upper'])
                for root, target in ((lower, F(d.SCALE - p.hi, d.SCALE)),
                                     (upper, F(d.SCALE - p.lo, d.SCALE))):
                    require(0 <= root.lo <= root.hi <= d.SCALE and root.width <= 1
                            and F(root.lo, d.SCALE) ** n <= target <= F(root.hi, d.SCALE) ** n,
                            'single_root_witness_not_exact_outer')
                before = current[index]
                lo = ((1-bg)/upper-1).lo if upper.lo > 0 else before.lo
                hi = ((1-bg)/lower-1).hi if lower.lo > 0 else before.hi
                after = before.intersect(d.I.raw(max(0, lo), max(0, hi))) if lo <= hi else None
                require(after is not None, 'new_single_intersection_empty')
                equal(proof['finite_upper_boundary'], lower.lo > 0, 'zero_root_boundary_dropped')
                equal(proof['mean_after'], serialized(after), 'single_inverse_contraction_changed')
                current[index] = after
                expected.append(witness)
    require(position == len(report['mean_contractions']) == 32, 'mean_witness_inventory_incomplete')
    equal(report['new_native_mean_domain'], serialized(current), 'four_mean_contraction_changed')
    ratios = [F(new.width, previous.width) for previous, new in zip(old, current)]
    require(all(0 < ratio <= 1 for ratio in ratios) and any(ratio < 1 for ratio in ratios), 'no_actual_mean_domain_compression')
    return current, [str(ratio) for ratio in ratios]


def source_polynomials(box, pop, const, means, records, epsilon):
    d, _, _ = modules()
    g, add, scale = d.geometry, d.geometry.padd, d.geometry.pscale
    geos = [g.geometry(box, pop, const, row, means) for row in range(4)]
    ba, bb = const['background']
    factor, pulses = (1-ba)*(1-bb), []
    for geo in geos:
        a, b = geo['alpha'], geo['beta']
        base = a*b/geo['D']+(geo['Ccorr']*geo['L']+geo['g'].square()*pop['T2'])/(geo['E']*geo['D'])
        pulses.append([factor*base+ba*(1-bb)*b/(1+b)+bb*(1-ba)*a/(1+a)+ba*bb,
                       factor*geo['g']/geo['E']])
    result = []
    for record in records:
        n, cells = record['identity']['pulse_count'], []
        for geo, pulse in zip(geos, pulses):
            a = g.clipped(d.legacy.window_single(geo['pulse_A'], n), 0, d.SCALE)
            b = g.clipped(d.legacy.window_single(geo['pulse_B'], n), 0, d.SCALE)
            joint = d.legacy.window_joint_coefficients(geo['pulse_A'], geo['pulse_B'], pulse, n)
            cells.append([joint, add([a], scale(joint, -1)), add([b], scale(joint, -1)),
                          add([1-a-b], joint), [a], [b]])
        losses = [cells[1][1], cells[2][2], cells[3][0]]
        ch = cells[0][0]
        for loss in losses:
            ch = add(ch, scale(loss, -1))
        lower, cost = ((1-epsilon)/2)**2, epsilon*(1-epsilon)
        result.append({'N': n, 'cells': cells, 'H': [add(scale(ch, lower), scale(loss, -cost)) for loss in losses]})
    return result


def bernstein(polynomial, phase):
    d, _, _ = modules()
    degree, a, width = len(polynomial)-1, d.I.raw(phase.lo, phase.lo), d.I.raw(phase.width, phase.width)
    shifted = [sum((polynomial[j]*math.comb(j, i)*a.power(j-i)*width.power(i)
                    for j in range(i, degree+1)), d.I(0)) for i in range(degree+1)]
    coefficients = [sum((shifted[j]*F(math.comb(i, j), math.comb(degree, j))
                        for j in range(i+1)), d.I(0)) for i in range(degree+1)]
    return d.I.raw(min(v.lo for v in coefficients), max(v.hi for v in coefficients)), coefficients


def support_ranges(polynomials, phase, record, epsilon):
    d, _, _ = modules()
    readings = []
    for row, feature in ((0, 0), (1, 1), (2, 2), (3, 0)):
        outer, _ = bernstein(polynomials['cells'][row][feature], phase)
        legal = outer.intersect(d.I(0, 1))
        accepted = legal.intersect(interval(record['conditional'][row][feature]['interval'])) if legal is not None else None
        require(accepted is not None, 'retained_relevant_probability_disjoint')
        readings.append(accepted)
    losses = readings[1:]
    ch = readings[0]-sum(losses, d.I(0))
    lower, cost = ((1-epsilon)/2)**2, epsilon*(1-epsilon)
    natural = [lower*ch-cost*loss for loss in losses]
    outer = [bernstein(hp, phase) for hp in polynomials['H']]
    ranges = [bound.intersect(target) for (bound, _), target in zip(outer, natural)]
    return ranges, [coefficients for _, coefficients in outer], natural


def check_phase(part, polynomial_rows, records, epsilon):
    d, _, _ = modules()
    phase = interval(part['phase'])
    pmap = {p['N']: p for p in polynomial_rows}
    rmap = {r['identity']['pulse_count']: r for r in records}
    status, reason = part['status'], part['reason']
    require(status in ('excluded', 'retained'), 'invalid_phase_disposition')
    if status == 'retained':
        require(reason == 'necessary_outer_region' and len(part['h_cuts']) == 4, 'unpaid_retained_H_inventory')
        for witness, record in zip(part['h_cuts'], records):
            n = record['identity']['pulse_count']
            equal(witness['N'], n, 'retained_H_window_changed')
            ranges, _, _ = support_ranges(pmap[n], phase, record, epsilon)
            require(all(value is not None for value in ranges), 'retained_source_H_identity_empty')
            equal(witness['H_ranges'], serialized(ranges), 'retained_source_H_bound_changed')
            cut = F(record['contrast']['h_bracket']['lower'])
            equal(witness['h_lower'], str(cut), 'retained_H_cut_changed')
            require(any(F(value.hi, d.SCALE) > cut for value in ranges), 'false_retained_H_disposition')
        return 'retained'
    n = integer(part['N'], 1)
    require(n in pmap, 'foreign_phase_window')
    polynomial, record = pmap[n], rmap[n]
    if reason == 'strict_conditional_probability_violation':
        row = integer(part['row'])
        require(row < 4 and part['feature'] in d.FEATURES, 'foreign_conditional_feature')
        feature = d.FEATURES.index(part['feature'])
        expected = polynomial['cells'][row][feature]
        bound, coefficients = bernstein(expected, phase)
        ci = interval(record['conditional'][row][feature]['interval'])
        equal(part['polynomial'], serialized(expected), 'exclusion_polynomial_not_same_source')
        equal(part['bernstein_coefficients'], serialized(coefficients), 'exclusion_Bernstein_coefficients_changed')
        equal(part['range'], serialized(bound), 'exclusion_Bernstein_range_changed')
        equal(part['conditional_interval'], serialized(ci), 'exclusion_conditional_interval_changed')
        legal = bound.intersect(d.I(0, 1))
        require(legal is None or legal.intersect(ci) is None, 'false_probability_exclusion')
    elif reason in ('strict_source_h_identity_violation', 'all_three_source_H_upper_at_or_below_lower'):
        ranges, coefficients, natural = support_ranges(polynomial, phase, record, epsilon)
        equal(part['H_polynomials'], serialized(polynomial['H']), 'exclusion_H_not_same_source')
        equal(part['H_bernstein_coefficients'], serialized(coefficients), 'exclusion_H_Bernstein_changed')
        equal(part['natural_H_ranges'], serialized(natural), 'exclusion_natural_H_changed')
        if reason == 'strict_source_h_identity_violation':
            require(any(value is None for value in ranges), 'false_source_identity_exclusion')
        else:
            cut = F(record['contrast']['h_bracket']['lower'])
            equal(part['H_ranges'], serialized(ranges), 'exclusion_H_range_changed')
            equal(part['h_lower'], str(cut), 'exclusion_source_cut_changed')
            require(all(value is not None and F(value.hi, d.SCALE) <= cut for value in ranges), 'false_whole_phase_H_exclusion')
    else:
        raise ValueError('unregistered_phase_exclusion_reason')
    return 'excluded'


def check_tree_structure(cover):
    d, _, _ = modules()
    nodes = cover['nodes']
    require(type(nodes) is list and len(nodes) == 1035, 'domain_node_inventory_changed')
    ids = [integer(n['id']) for n in nodes]
    require(len(set(ids)) == len(nodes) and set(ids) == set(range(len(nodes))), 'duplicate_or_missing_node')
    nmap = {n['id']: n for n in nodes}
    equal(cover['roots'], list(range(11)), 'old_source_root_inventory_changed')
    visited, queue, incoming = set(), list(cover['roots']), Counter()
    while queue:
        index = queue.pop()
        require(index not in visited and index in nmap, 'cycle_or_missing_child')
        visited.add(index)
        node = nmap[index]
        require(node['status'] in ('split', 'retained', 'excluded'), 'invalid_node_disposition')
        integer(node['depth']); integer(node['root_index'])
        if index < 11:
            equal((node['parent'], node['depth'], node['root_index']), (None, 0, index), 'old_source_root_metadata_changed')
        if node['status'] != 'split':
            require('children' not in node, 'terminal_node_has_children')
            continue
        children = node['children']
        require(type(children) is list and len(children) == 2 and children[0] != children[1], 'binary_children_required')
        for child in children:
            integer(child)
            require(child in nmap and child >= 11, 'foreign_child')
            incoming[child] += 1
            equal((nmap[child]['parent'], nmap[child]['root_index'], nmap[child]['depth']),
                  (index, node['root_index'], node['depth']+1), 'child_lineage_changed')
        require(node['split_axis'] in d.geometry.AXES, 'foreign_split_axis')
        axis = d.geometry.AXES.index(node['split_axis'])
        box = [interval(p) for p in node['contracted_box']]
        require(len(box) == 5, 'source_coordinate_inventory_changed')
        mid = F(node['split_at'])*d.SCALE
        require(mid.denominator == 1 and box[axis].lo < mid < box[axis].hi, 'invalid_scaled_split')
        left, right = list(box), list(box)
        left[axis], right[axis] = d.I.raw(box[axis].lo, int(mid)), d.I.raw(int(mid), box[axis].hi)
        for child, expected in zip(children, (left, right)):
            equal(nmap[child]['input_box'], serialized(expected), 'child_partition_gap_or_overlap')
            equal(nmap[child]['input_k'], node['surviving_k_hull'], 'child_phase_carrier_changed')
        queue.extend(children)
    require(visited == set(nmap) and all(incoming[i] == 1 for i in range(11, len(nodes))), 'tree_orphan_or_duplicate_parent')
    equal(integer(cover['split_count']), 512, 'source_split_cap_changed')
    equal(Counter(n['status'] for n in nodes), Counter(split=512, retained=314, excluded=209), 'domain_status_count_changed')
    return nmap


def check_phase_partition(parts, common):
    d, _, _ = modules()
    expected = [d.I.raw(common.lo+common.width*i//8, common.lo+common.width*(i+1)//8) for i in range(8)]
    equal([part['phase'] for part in parts], serialized(expected), 'phase_partition_gap_or_loss')


def check_record_identities(actual, expected):
    require(type(actual) is list and len(actual) == 4, 'source_record_inventory_changed')
    for record in actual:
        require(integer(record['identity']['pulse_count'], 1) in (1, 3, 5, 7)
                and integer(record['total_trials'], 1) == sum(record['setting_trials'])
                and len(record['setting_trials']) == 4
                and all(integer(value, 1) > 0 for value in record['setting_trials']),
                'source_window_or_relevant_only_exposure_changed')
    equal(actual, expected, 'source_window_or_relevant_only_exposure_changed')


def check_tree(report, roots, native, initial, const, endpoints, records, config, old_config):
    d, _, _ = modules()
    cover = report['cover']
    nmap = check_tree_structure(cover)
    equal(report['input_domains'], serialized(roots), 'old_retained_source_boxes_changed')
    means = {'alpha': [native[0], native[2]], 'beta': [native[1], native[3]], 'joint': []}
    constraints = d.geometry.linear_constraints(means, const)
    equal(cover['linear_constraints'], serialized(constraints), 'source_linear_constraints_changed')
    widths = [v.width or 1 for v in initial]
    split_count, phase_counts, leaf_records = 0, Counter(), []
    for node in cover['nodes']:
        raw, inherited = [interval(v) for v in node['input_box']], interval(node['input_k'])
        require(len(raw) == 5 and node['root_index'] < 11, 'source_coordinate_or_root_changed')
        if node['id'] < 11:
            root = roots[node['id']]
            equal(node['input_box'], serialized(root['source_box']), 'old_root_box_changed')
            equal(node['input_k'], serialized(root['common_k']), 'old_root_phase_changed')
        box, contraction = d.geometry.linear_contract(raw, constraints)
        equal(node['contracted_box'], serialized(box), 'unpaid_source_linear_contraction')
        equal(node['contraction'], serialized(contraction), 'linear_contractor_witness_changed')
        if box is None:
            equal((node['status'], node['reason']), ('excluded', 'strict_new_single_or_loss_halfspace_violation'), 'false_single_exclusion')
            continue
        pop = d.geometry.population(box)
        if pop is None:
            equal((node['status'], node['reason']), ('excluded', 'strict_source_PSD_violation'), 'false_PSD_exclusion')
            continue
        boundary = False
        try:
            common, slabs, _ = d.legacy.common_phase(box, pop, const, means, endpoints, old_config)
            equal(node['phase_slabs_sha256'], d.geometry.sha(d.geometry.canonical(slabs)), 'same_source_phase_slabs_changed')
            common = common.intersect(inherited) if common is not None else None
            if common is None:
                equal((node['status'], node['reason']), ('excluded', 'strict_old_new_common_phase_empty'), 'false_common_phase_exclusion')
                equal(node['phase_slabs'], serialized(slabs), 'common_phase_exclusion_witness_changed')
                continue
            polynomial_rows = source_polynomials(box, pop, const, means, records, F(config['epsilon']))
        except (ArithmeticError, ValueError) as error:
            # Only a recorded numerical boundary may retain the entire inherited phase.
            parts = node.get('phase_partitions', [])
            require(len(parts) == 1 and parts[0]['status'] == 'retained'
                    and parts[0]['reason'] == 'boundary_arithmetic_unresolved'
                    and parts[0]['detail'] == str(error), 'uncertified_boundary_fallback')
            common = inherited.intersect(d.I.raw(-pop['T2'].sqrt().hi, pop['T2'].sqrt().hi))
            common = inherited if common is None else common
            equal(parts[0]['phase'], serialized(inherited), 'boundary_phase_lost')
            boundary = True
        equal(node['common_k'], serialized(common), 'same_source_common_phase_changed')
        parts = node['phase_partitions']
        if not boundary:
            check_phase_partition(parts, common)
            for part in parts:
                phase_counts[check_phase(part, polynomial_rows, records, F(config['epsilon']))] += 1
        retained = [interval(part['phase']) for part in parts if part['status'] == 'retained']
        if not retained:
            equal((node['status'], node['reason']), ('excluded', 'complete_phase_partition_excluded'), 'false_complete_phase_exclusion')
            continue
        hull = d.I.raw(min(p.lo for p in retained), max(p.hi for p in retained))
        equal(node['surviving_k_hull'], serialized(hull), 'surviving_phase_hull_changed')
        relative = [F(value.width, width) for value, width in zip(box, widths)]
        axis = max(range(5), key=lambda j: (relative[j], -j))
        mid = (box[axis].lo+box[axis].hi)//2
        can_split = (split_count < config['source_split_cap'] and node['depth'] < old_config['max_depth']
                     and relative[axis] > F(old_config['normalized_width_stop']) and box[axis].lo < mid < box[axis].hi)
        if can_split:
            equal(node['status'], 'split', 'false_resource_cap_retention')
            equal((node['split_axis'], node['split_at']), (d.geometry.AXES[axis], str(F(mid, d.SCALE))), 'existing_split_witness_changed')
            split_count += 1
        else:
            equal((node['status'], node['reason']), ('retained', 'cap_depth_width_or_boundary_preserved'), 'dropped_cap_or_boundary_leaf')
            leaf_records.append({'node_id': node['id'], 'root_index': node['root_index'], 'source_box': serialized(box),
                                 'phase_components': serialized(retained), 'necessary_outer_only': True})
        if (node['id']+1) % 128 == 0:
            print(json.dumps({'existing_nodes_checked': node['id']+1, 'phase_witnesses_checked': sum(phase_counts.values())}), flush=True)
    equal(cover['leaves'], leaf_records, 'retained_leaf_inventory_changed')
    equal(split_count, 512, 'split_witness_count_changed')
    return {'old_retained_source_boxes': 11, 'node_count': 1035, 'new_split_count': 512,
            'excluded_source_nodes': 209, 'retained_source_leaves': 314,
            'node_status_counts': {'excluded': 209, 'retained': 314, 'split': 512},
            'phase_witness_counts': dict(phase_counts)}


def member_qualification(member, endpoints, records, original_ci):
    d, _, _ = modules()
    windows, checks = member['windows'], []
    for endpoint in endpoints:
        for row in range(4):
            for field, name in d.legacy.FIELDS:
                require(interval(windows[str(endpoint['N'])][row][name]).within_exact(endpoint['original_CI'][field][row]),
                        'old_native_member_original_CI_changed')
    for ci in original_ci:
        n = 5 if ci['identity'] == 'old_cut_N5' else int(ci['identity'].split('full_N')[1])
        name = {'j': 'j', 'sA_cell': 'sA', 'sB_cell': 'sB'}[ci['field']]
        require(interval(windows[str(n)][ci['row']][name]).within_exact(ci['interval']), 'canonical_72_CI_not_preserved')
    for record in records:
        n, cells = record['identity']['pulse_count'], windows[str(record['identity']['pulse_count'])]
        for row, cell in enumerate(cells):
            features = [interval(p) for p in cell['outcomes']]+[interval(cell['sA']), interval(cell['sB'])]
            for feature, prediction in enumerate(features):
                target = record['conditional'][row][feature]['interval']
                checks.append({'N': n, 'row': row, 'feature': d.FEATURES[feature], 'prediction': prediction,
                               'contained': prediction.within_exact(target), 'disjoint': prediction.disjoint_exact(target)})
    h_checks, epsilon = [], F(modules()[0].statistics.configuration()['epsilon'])
    for record in records:
        n = record['identity']['pulse_count']; cells = windows[str(n)]
        losses = [interval(cells[1]['outcomes'][1]), interval(cells[2]['outcomes'][2]), interval(cells[3]['j'])]
        ch = interval(cells[0]['j'])-sum(losses, d.I(0))
        lower, cost = ((1-epsilon)/2)**2, epsilon*(1-epsilon)
        branches = [lower*ch-cost*loss for loss in losses]
        h = d.I.raw(max(v.lo for v in branches), max(v.hi for v in branches))
        cut = F(record['contrast']['h_bracket']['lower'])
        h_checks.append({'N': n, 'H_ranges': branches, 'h': h, 'lower': cut,
                         'strictly_above_lower': F(h.lo, d.SCALE) > cut,
                         'wholly_rejected': F(h.hi, d.SCALE) <= cut})
    require(len(original_ci) == 72 and len(checks) == 96 and len(h_checks) == 4, 'incomplete_native_member_checks')
    return {'qualified': all(c['contained'] for c in checks) and all(h['strictly_above_lower'] for h in h_checks),
            'old_CI_containments': 72, 'new_conditional_checks': checks, 'new_h_checks': h_checks}


def check_member_identity(candidate, sealed, identity):
    equal(candidate['origin'], 'previously_certified_native_Gamma_Fock', 'fresh_or_unsealed_native_member')
    require(candidate['native_Fock_recomputed'] is False, 'native_Fock_recomputed_at_check')
    equal(candidate['source'], sealed['source'], 'native_source_not_original_recipe')
    equal(candidate['recipe'], sealed['recipe'], 'native_recipe_changed')
    equal(candidate['native_windows'], sealed['windows'], 'phase_after_window_or_native_readout_changed')
    equal(candidate['reuse_identity'], identity, 'native_qualification_identity_changed')


def check_members(report, sealed, endpoints, records, original_ci):
    expected, qualified = [], []
    for member in sealed:
        proof = member_qualification(member, endpoints, records, original_ci)
        identity = {'implementation': member['implementation'], 'old_member_id': member['old_member_id'],
                    'recipe_sha256': hashlib.sha256(json.dumps(member['recipe'], sort_keys=True).encode()).hexdigest(),
                    **proof}
        expected.append(serialized(identity))
        if proof['qualified']:
            qualified.append((member, serialized(identity)))
    equal(report['reused_member_checks'], expected, 'all_32_old_source_qualifications_changed')
    require(len(expected) == 32 and len(qualified) == len(report['members']) == 8, 'native_member_inventory_changed')
    for index, (candidate, (member, identity)) in enumerate(zip(report['members'], qualified)):
        equal(integer(candidate['id']), index, 'native_member_id_changed')
        check_member_identity(candidate, member, identity)
    return {'old_native_members_checked': 32, 'qualified_native_members': 8,
            'old_CI_containments_checked': 32*72, 'conditional_member_checks': 32*96,
            'source_h_member_checks': 32*4, 'fresh_Fock_evaluations': 0}


def verify_witness():
    started = time.monotonic()
    d, v, s = modules()
    config = d.statistics.configuration()
    statistical = v.validate_statistics(s.consume())
    kernel = v.kernel_consume()
    path = HERE/'domain-first.json.xz'
    identity = d.statistics.frozen(path)
    report = d.load(path)
    check_scope(report)
    for row in report['bindings']:
        binding_check(row)
    old_verifier = d.statistics.module('_sc_domain_old_cover_intake', d.MW/'source_verify.py')
    old = old_verifier.consume()
    require(old['evidence_valid'] is True and old['source_outer_cover_and_all_72_CI_certified'] is True,
            'old_source_cover_authority_not_valid')
    old_config, _ = d.legacy.configuration()
    const = d.geometry.constants(old_config)
    primary = d.load(HERE/'statistics-primary-first.json.xz')
    records = d.new_records(primary)
    d.validate_statistics_cross(statistical, d.statistics.frozen(HERE/'statistics-primary-first.json.xz'))
    expected_records = [{'identity': r['identity'], 'total_trials': r['total_trials'], 'setting_trials': r['setting_trials'],
                         'h_lower': str(F(r['contrast']['h_bracket']['lower']))} for r in records]
    check_record_identities(report['records'], expected_records)
    roots, endpoints, original_means, initial, sealed_members = d.old_material()
    native, ratios = check_means(report, original_means, records, const)
    joined = d.joined_endpoints(endpoints, records)
    summary = check_tree(report, roots, native, initial, const, joined, records, config, old_config)
    summary.update(check_members(report, sealed_members, endpoints, records, statistical['original_CI72']))
    summary['native_mean_width_ratios'] = ratios
    summary['native_mean_axes'] = ['Alice0', 'Bob0', 'Alice1', 'Bob1']
    summary['old_native_mean_domain'] = report['old_native_mean_domain']
    summary['new_native_mean_domain'] = report['new_native_mean_domain']
    equal(report['summary'], {k: summary[k] for k in ('old_retained_source_boxes', 'node_count', 'new_split_count',
          'node_status_counts', 'retained_source_leaves', 'qualified_native_members')}, 'producer_summary_not_checked')
    n5 = next(r for r in records if r['identity']['pulse_count'] == 5)
    hcut = F(n5['contrast']['h_bracket']['lower'])
    epsilon = F(config['epsilon']); pl = ((1-epsilon)/2)**2
    min_loss = min(max(F(0), F(n5['conditional'][row][feature]['interval']['exact_lower']))
                   for row, feature in ((1, 1), (2, 2), (3, 0)))
    lower_bound = (hcut+epsilon*(1-epsilon)*min_loss)/pl
    require(hcut > 0 and min_loss >= 0 and lower_bound > 0, 'uniform_positive_source_CH_bound_not_generated')
    paths = [HERE/name for name in ('criterion.md', 'sources.json', 'domain_verify.py', 'test_domain_verify.py',
        'domain.py', 'test_domain.py', 'domain-first.json.xz', 'verify.py', 'statistics_verify.py',
        'statistics-primary-first.json.xz', 'statistics-cross-verification.json', 'kernel-certification-first.json')]
    bindings = [d.statistics.frozen(p) for p in paths]
    for row in report['bindings']:
        if row not in bindings:
            bindings.append(row)
    bindings += [d.statistics.frozen(d.MW/'source_verify.py')]
    return {'schema': SCHEMA, 'version': VERSION, **{name: True for name in POSITIVE},
            **{name: False for name in NEGATIVE}, 'status': 'certified_existing_source_domain_witness',
            'source_summary': summary, 'uniform_CH_N5_lower_bound': str(lower_bound),
            'uniform_CH_N5_bound_inputs': {'h_lower': str(hcut), 'minimum_loss_lower': str(min_loss),
                                         'pLower': str(pl), 'epsilon': str(epsilon)},
            'uniform_CH_N5_lower_bound_scope': 'every legal common source satisfying the complete new confidence constraints; retained outer leaves are not members',
            'all_11_old_source_roots_checked': True, 'all_1035_existing_nodes_checked': True,
            'all_314_cap_leaves_preserved': True, 'all_209_exclusion_dispositions_checked': True,
            'all_32_original_native_source_identities_checked': True, 'all_8_qualified_native_members_checked': True,
            'four_native_mean_intersections_checked': True, 'bound_helpers_shared': SHARED_HELPERS,
            'statistical_budget': statistical['budget'], 'source_kernel_owned_declarations': kernel['owned_declarations'],
            'bindings': bindings, 'domain_first_identity': identity, 'runtime_seconds': time.monotonic()-started,
            'tree_solver_calls': 0, 'member_search_calls': 0, 'Fock_producer_calls': 0,
            'statistics_or_CI_producer_calls': 0, 'bell_event_files_read': 0}


def certificate_check(report):
    require(report['schema'] == SCHEMA and report['version'] == VERSION
            and all(report[name] is True for name in POSITIVE)
            and all(report[name] is False for name in NEGATIVE), 'domain_certificate_scope_changed')
    for name in ('tree_solver_calls', 'member_search_calls', 'Fock_producer_calls',
                 'statistics_or_CI_producer_calls', 'bell_event_files_read'):
        require(integer(report[name]) == 0, 'domain_check_crossed_producer_boundary')
    summary = report['source_summary']
    for name, expected in (('old_retained_source_boxes', 11), ('node_count', 1035), ('new_split_count', 512),
                           ('excluded_source_nodes', 209), ('retained_source_leaves', 314),
                           ('old_native_members_checked', 32), ('qualified_native_members', 8), ('fresh_Fock_evaluations', 0)):
        equal(integer(summary[name]), expected, 'domain_certificate_inventory_changed')
    equal(summary['node_status_counts'], {'excluded': 209, 'retained': 314, 'split': 512}, 'domain_certificate_status_changed')
    require(type(report['uniform_CH_N5_lower_bound']) is str and F(report['uniform_CH_N5_lower_bound']) > 0,
            'domain_certificate_positive_bound_changed')
    inputs = report['uniform_CH_N5_bound_inputs']
    eps, pl, cut, loss = (F(inputs[name]) for name in ('epsilon', 'pLower', 'h_lower', 'minimum_loss_lower'))
    require(eps == F(3, 1000) and pl == ((1-eps)/2)**2 and cut > 0 and loss >= 0
            and F(report['uniform_CH_N5_lower_bound']) == (cut+eps*(1-eps)*loss)/pl,
            'domain_certificate_uniform_bound_not_source_generated')
    require(report['bound_helpers_shared'] == SHARED_HELPERS, 'domain_checker_helper_scope_changed')
    for old, new, ratio in zip(summary['old_native_mean_domain'], summary['new_native_mean_domain'], summary['native_mean_width_ratios']):
        old_width = F(old['exact_upper'])-F(old['exact_lower'])
        new_width = F(new['exact_upper'])-F(new['exact_lower'])
        require(old_width > 0 and 0 < new_width <= old_width and F(ratio) == new_width/old_width,
                'domain_certificate_mean_ratio_changed')
    require(len(summary['old_native_mean_domain']) == len(summary['new_native_mean_domain'])
            == len(summary['native_mean_width_ratios']) == 4, 'four_complete_mean_domains_required')


def consume(certificate_path=None, disabled=False):
    empty = {'schema': SCHEMA, 'version': VERSION, **{name: False for name in (*POSITIVE, *NEGATIVE)},
             'tree_solver_calls': 0, 'member_search_calls': 0, 'Fock_producer_calls': 0,
             'statistics_or_CI_producer_calls': 0, 'bell_event_files_read': 0}
    if disabled:
        return {**empty, 'status': 'disabled'}
    d, _, _ = modules()
    canonical = HERE/'domain-verification.json'
    d.statistics.frozen(canonical)
    raw = canonical.read_bytes()
    path = canonical if certificate_path is None else Path(certificate_path)
    require(path.read_bytes() == raw, 'lookalike_domain_certificate')
    report = json.loads(raw)
    certificate_check(report)
    for row in report['bindings']:
        binding_check(row)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--disabled', action='store_true')
    args = parser.parse_args()
    if args.output is not None:
        require(not args.output.exists() and args.output.resolve() == (HERE/'domain-verification.json').resolve()
                and args.certificate is None and not args.disabled, 'new_canonical_domain_certificate_required')
        report = verify_witness()
        certificate_check(report)
        args.output.write_text(json.dumps(report, indent=2, sort_keys=True, allow_nan=False)+'\n')
    else:
        report = consume(args.certificate, args.disabled)
    print(json.dumps({k: report[k] for k in ('schema', 'evidence_valid', 'status')}
                     | ({'source_summary': report['source_summary'], 'uniform_CH_N5_lower_bound': report['uniform_CH_N5_lower_bound']}
                        if report['evidence_valid'] else {}), indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
