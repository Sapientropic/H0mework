"""Exact detector realizations and whole-confidence raw-hardware constraints.

O=mu I+u X+z Z is the signed readout.  The physical click effect is
(I-O)/2=d I+k J with k=(1-d) eta.  A CSV polarity is never inferred here.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations

from atomic_dose import square_root_lower
from model import Effect, rational


@dataclass(frozen=True)
class AtomicEffect:
    trace: Q
    x: Q
    z: Q

    def __post_init__(self):
        for key in ('trace', 'x', 'z'):
            object.__setattr__(self, key, rational(getattr(self, key)))
        radius = self.x ** 2 + self.z ** 2
        if not 0 <= self.trace <= 2 or radius > min(self.trace, 2-self.trace) ** 2:
            raise ValueError('Physical atomic effect required')


def forward(atom, background, efficiency):
    d, eta = map(rational, (background, efficiency))
    if type(atom) is not AtomicEffect or not 0 <= d <= 1 or not 0 <= eta <= 1:
        raise ValueError('Physical atomic effect and detector probabilities required')
    k = (1-d) * eta
    return Effect(1-2*d-k*atom.trace, -k*atom.x, -k*atom.z)


def inverse(effect, background, detection):
    """Every positive-k detector realization, with exact cone membership."""
    d, k = map(rational, (background, detection))
    if type(effect) is not Effect or not 0 <= d < 1 or not 0 < k <= 1-d:
        raise ValueError('Positive physical detector factor required')
    atom = AtomicEffect((1-effect.mu-2*d)/k, -effect.u/k, -effect.z/k)
    eta = k / (1-d)
    if forward(atom, d, eta) != effect:
        raise ValueError('Inverse does not realize the source effect')
    return {'background': d, 'detection': k, 'fragment_efficiency': eta, 'atom': atom}


def admits(effect, background, detection):
    """Complete realization domain, including the zero-factor stratum."""
    d, k = map(rational, (background, detection))
    if type(effect) is not Effect or not 0 <= d <= 1 or not 0 <= k <= 1-d:
        return False
    if k == 0:
        return effect.u == effect.z == 0 and effect.mu == 1-2*d
    t = 1-effect.mu-2*d
    r2 = effect.u**2 + effect.z**2
    return 0 <= t <= 2*k and r2 <= t*t and r2 <= (2*k-t)**2


def interval(row, lower, upper):
    if type(row) not in (tuple, list) or len(row) != 2:
        raise ValueError('Two interval endpoints required')
    lo, hi = map(rational, row)
    if not lower <= lo <= hi <= upper:
        raise ValueError('Ordered physical interval required')
    return lo, hi


def necessary_bounds(gain_lower, bias_interval):
    g = rational(gain_lower)
    lo, hi = interval(bias_interval, -1, 1)
    if not 0 < g <= 1:
        raise ValueError('Positive original gain lower bound required')
    b = max(abs(lo), abs(hi))
    h = 2*g/(1+b+g)
    square = 4*h/7
    return {'gain_lower': str(g), 'bias_interval': list(map(str, (lo, hi))),
            'bias_absolute_upper': str(b), 'eta_lower': str(h), 'lambda_max_lower': str(h),
            'eta_times_lambda_max_lower': str(h), 'eta_times_area_squared_lower': str(square),
            'area_lower_squared': str(square), 'area_lower': str(square_root_lower(square)),
            'dark_background_upper': str((1+b-g)/2), 'click_polarity_selected': False}


def confidence_domain(shared_run, bias_run, joint_run):
    if shared_run['run'] != bias_run['run'] or shared_run['run'] != joint_run['run']:
        raise ValueError('Same original confidence run required')
    if (shared_run.get('parent_factor_sequence_sha256') is not None and
            joint_run.get('parent_factor_sequence_sha256') != shared_run['parent_factor_sequence_sha256']):
        raise ValueError('Same original trial factor sequence required')
    roles = (('alice',0),('alice',1),('bob',0),('bob',1))
    gains, biases = shared_run['shared_response_envelopes'], bias_run['bias_envelopes']
    for rows in (gains,biases):
        if (type(rows) is not list or any(type(row['setting']) is not int for row in rows) or
                [(row['side'],row['setting']) for row in rows] != list(roles)):
            raise ValueError('Same ordered original confidence roles required')
    individual = [dict(side=side,setting=setting,**necessary_bounds(interval(g['canonical_gain'],0,1)[0],b['mu_outer_interval']))
                  for (side,setting),g,b in zip(roles,gains,biases)]
    rays=joint_run['joint_response_rays']
    if [r['ray'] for r in rays]!=['uniform','alice','bob']:
        raise ValueError('All original low-orthant exclusions required')
    joint=[]
    for row in rays:
        indices=range(4) if row['ray']=='uniform' else (0,1) if row['ray']=='alice' else (2,3)
        b=max(Q(individual[i]['bias_absolute_upper']) for i in indices)
        g=interval(row['profile_threshold_bracket'],0,1)[0]
        if row['entire_lower_orthant_excluded'] is not True or not 0<g<=1:
            raise ValueError('Strict original joint gain exclusion required')
        h=2*g/(1+b+g)
        square=4*h/7
        joint.append({'ray':row['ray'],'source_max_gain_strict_lower':str(g),
                      'group_bias_absolute_upper':str(b),'maximum_eta_times_lambda_max_strict_lower':str(h),
                      'maximum_eta_times_area_squared_strict_lower':str(square),
                      'maximum_area_strict_lower':str(square_root_lower(square))})
    return {'run':shared_run['run'],'individual_hardware_constraints':individual,'joint_hardware_constraints':joint}


def hardware_gain_cap(eta_upper, area_squared_upper, bias_absolute_upper):
    eta, area2, b = map(rational, (eta_upper, area_squared_upper, bias_absolute_upper))
    if not 0 <= eta <= 1 or area2 < 0 or not 0 <= b <= 1:
        raise ValueError('Physical upper hardware box required')
    s = eta * min(Q(1), 7*area2/4)
    return min(Q(1), (1+b)*s/(2-s))


def halfplane_vertices(constraints):
    """Closed bounded polygon; pair intersections also retain segment/point faces."""
    rows = [tuple(map(rational, row)) for row in constraints]
    if any(len(row) != 3 for row in rows):
        raise ValueError('Linear detector halfplanes required')
    vertices = set()
    for (a,b,c), (x,y,z) in combinations(rows, 2):
        det = a*y-x*b
        if det:
            d, k = (c*y-z*b)/det, (a*z-x*c)/det
            if all(p*d+q*k <= r for p,q,r in rows):
                vertices.add((d,k))
    return tuple(sorted(vertices))


def atomic_detector_polygons(gain_lower, bias_interval, bright, dark):
    """Necessary domains for a raw response box, keeping both click polarities.

    The response box may relax correlations between its trace and gap.  Empty
    branches exclude the entire box; nonempty branches retain necessary scope.
    """
    g = rational(gain_lower)
    lo, hi = interval(bias_interval, -1, 1)
    if not 0 < g <= 1:
        raise ValueError('Positive original gain lower bound required')
    bl, bu = interval(bright, 0, 1)
    dl, du = interval(dark, 0, 1)
    tl, tu = bl+dl, bu+du
    gap = max(abs(bl-du), abs(bu-dl))
    branches = []
    for polarity, (l,u) in ((1,(lo,hi)), (-1,(-hi,-lo))):
        rows = [(Q(-1),Q(0),Q(0)), (Q(0),Q(-1),Q(0)), (Q(1),Q(1),Q(1)),
                (Q(0),-gap,-g), (Q(2),tl,1-l), (Q(-2),-tu,-(1-u))]
        vertices = halfplane_vertices(rows)
        branches.append({'polarity': polarity, 'constraints': [list(map(str,r)) for r in rows],
                         'vertices': [list(map(str,p)) for p in vertices], 'empty': not vertices})
    return {'branches': branches, 'entire_atomic_response_box_excluded': all(row['empty'] for row in branches),
            'click_polarity_selected': False, 'necessary_projection_only': True}
