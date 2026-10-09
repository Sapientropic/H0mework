"""A continuous detector box carries its complete observed quantum fibre.

The incoming state may vary with the fixed hardware parameter.  Its common
centre and uniform old error enter the source CP family once.  No probability
prior over hardware or average of normalized vertex posteriors is introduced.
"""
from fractions import Fraction as Q
from itertools import product

import fluorescence_channel as channel
import projected_window_cem as projected
import window_cem_source as window
import window_detector_family as native


SCHEMA = 'stage10-continuous-detector-observed-state-box/v1'


def _selected(state, clicks):
    return {(i,j):value for (mark,i,j),value in state.items() if mark.clicks == clicks}


def _weights(a, b, backgrounds):
    result = {}
    for i,j,noise in product(range(4),range(4),native.BACKGROUND_VERTICES):
        weight = a[i]*b[j]
        for bit,probability in zip(noise,backgrounds):
            weight *= probability if bit else 1-probability
        result[i,j,noise] = weight
    return result


def condition_box(family, report, *, clicks, q_a_box=None, q_b_box=None, background_box=None):
    """Generate a uniform full-state bound for every parameter in one exact box.

    For each parameter theta the source input differs from the common report
    input by at most oldE.  A CP event restriction contracts that error.  The
    remaining parameter variation is bounded before the event is normalized.
    Positive physical inputs are supplied by the upstream source.
    """
    channel._require(type(family) is native.WindowDetectorFamily,
                     'closed source-generated continuous detector family required')
    channel._require(type(clicks) is tuple and clicks in window.REGISTRATION_ORDER and
                     all(type(bit) is int for bit in clicks), 'original complete CEM outcome required')
    envelope = family.enclose(report,q_a_box=q_a_box,q_b_box=q_b_box,background_box=background_box)
    outcome = next(row for row in envelope['outcomes'] if tuple(row['clicks']) == clicks)
    lower,upper = map(Q,outcome['unnormalized_mass_bounds'])
    parameters = {'q_A_vertices':envelope['q_A_simplex_box_vertices'],
                  'q_B_vertices':envelope['q_B_simplex_box_vertices'],
                  'background_endpoints':envelope['background_box_endpoints']}
    base = {'schema':SCHEMA,'source_family':family.record(),'source_recipe':report['source_recipe'],
            'initial_marked_state':report['initial_marked_state'], 'clicks':list(clicks),
            'parameter_domain':parameters,'observed_event_mass_bounds':list(map(str,(lower,upper))),
            'incoming_states_may_depend_on_theta':True,
            'incoming_uniform_trace_norm_error':report['upstream_trace_norm_error'],
            'old_error_paid_once':True,'hardware_prior_used':False,
            'normalized_vertex_average_used':False,'parameter_domain_removed':False,
            'positive_source_input_required':True,'input_positivity_certified_here':False,
            'source_recipe_is_provenance_certificate':False,
            'actual_hardware_uniquely_identified':False,'controller_advance':False}
    if lower <= 0:
        return {**base,'status':'whole_parameter_box_event_normalizer_unresolved',
                'normalized_state_box_generated':False}
    aa = tuple(tuple(map(Q,row)) for row in parameters['q_A_vertices'])
    bb = tuple(tuple(map(Q,row)) for row in parameters['q_B_vertices'])
    backgrounds = tuple(tuple(map(Q,row)) for row in parameters['background_endpoints'])
    a0 = tuple(sum((row[i] for row in aa),Q(0))/len(aa) for i in range(4))
    b0 = tuple(sum((row[i] for row in bb),Q(0))/len(bb) for i in range(4))
    noise0 = tuple((min(row[i] for row in backgrounds)+max(row[i] for row in backgrounds))/2
                   for i in range(2))
    weights0 = _weights(a0,b0,noise0)
    vertices = family.vertex_states(report)
    norms = {}
    for i,j,noise in product(range(4),range(4),native.BACKGROUND_VERTICES):
        state = native._noise(vertices[i,j]['state'],noise)
        norms[i,j,noise] = projected.bsm._entry_norm(_selected(state,clicks))
    variation = Q(0)
    for a,b,noise in product(aa,bb,backgrounds):
        weights = _weights(a,b,noise)
        # Absolute value is convex in each parameter block separately.  The
        # exact simplex-product corners therefore cover its whole maximum.
        candidate = sum((abs(weights[key]-weights0[key])*norms[key] for key in weights),Q(0))
        variation = max(variation,candidate)
    centre = family.evaluate(report,a0,b0,noise0)
    selected = _selected(centre['state'],clicks)
    mass,rounding = native._trace(selected)
    channel._require(mass > 0,'the source-generated centre misses its positive event box')
    error = Q(envelope['whole_trace_norm_error_upper'])+variation+rounding
    norm = projected.bsm._entry_norm(selected)
    price = error/lower+norm*error/(lower*mass)
    normalized = {key:value*(1/mass) for key,value in selected.items()}
    return {**base,'status':'whole_parameter_box_normalized_state_generated',
            'normalization_centre_parameter':{'q_A':list(map(str,a0)),'q_B':list(map(str,b0)),
                                             'backgrounds':list(map(str,noise0)),
                                             'actual_hardware_value_selected':False},
            'unnormalized_centre':channel._input_record(selected),
            'normalizer_centre':str(mass),'parameter_variation_entry_norm_upper':str(variation),
            'uniform_unnormalized_trace_norm_error':str(error),
            'normalized_complete_state_centre':channel._input_record(normalized),
            'uniform_posterior_trace_norm_error':str(price),'normalized_state_box_generated':True,
            'whole_event_normalization_bound': 'epsilon/lo+norm(C0)*epsilon/(lo*mass(C0))',
            'parameter_variation_coverage':'separately convex weighted full-matrix norm over exact simplex-product vertices'}


def verify_condition_box(value, family, report, *, q_a_box=None, q_b_box=None, background_box=None):
    channel._require(type(value) is dict and value.get('schema') == SCHEMA,
                     'source-generated complete detector parameter state box required')
    expected = condition_box(family,report,clicks=tuple(value['clicks']),q_a_box=q_a_box,
                            q_b_box=q_b_box,background_box=background_box)
    channel._require(value == expected,'continuous parameter domain, state, source or error price changed')
    return True
