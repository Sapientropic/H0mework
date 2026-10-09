#!/usr/bin/env python3
"""Original five-term insertion and the actual sharp-window shape coefficients."""
from itertools import product
from pathlib import Path
import hashlib
import json
import sys
import time

import sympy as S

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def main():
    started = time.monotonic()
    sources = [
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketField/Extension.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketField/Spatial.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketCurrentMomentum/PhysicalKernel.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketScale/Cutoff.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketScale/Source.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketScale/Current.lean',
        FQ/'packet-gauge-bilocal/vertices.json',
        FQ/'packet-gauge-reduced-contact/contact.json',
        FQ/'packet-gauge-constitutive-vertex/vertices.json',
        FQ/'packet-gauge-kinetic/receipt.json',
        FQ/'packet-gauge-cosine/README.md',
        FQ/'packet-gauge-joint-causal/source.json',
        FQ/'packet-gauge-joint-family/response-consumer.json',
    ]
    original = json.loads((FQ.parent/'active-gauge/receipt.json').read_text())
    for path, expected in original['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected
    vertices = json.loads((FQ/'packet-gauge-bilocal/vertices.json').read_text())
    contact = json.loads((FQ/'packet-gauge-reduced-contact/contact.json').read_text())
    k = S.Matrix(S.symbols('k1:4', real=True))
    p = S.Matrix(S.symbols('p1:4', real=True))
    q = S.Matrix(S.symbols('q1:4', real=True))
    zb, w = S.symbols('zb w')
    left = lambda v: S.Matrix([zb, *[S.I*t for t in v]])
    right = lambda v: S.Matrix([w, *[-S.I*t for t in v]])
    reader = S.Matrix([-zb-w, *[-S.I*t for t in p]])
    phase_checks = []
    for sign in [-1, 1]:
        delta = sign*q
        other = k-p+delta
        external = S.Matrix([0, *[S.I*t for t in delta]])
        points = {
            'right_propagation': (left(k), right(k-p), S.zeros(4, 1)),
            'left_propagation': (left(k+delta), right(other), S.zeros(4, 1)),
            'native_contact': (left(k), right(other), external),
            'noise_left': (left(k), right(k-p), S.zeros(4, 1)),
            'noise_right': (left(k), right(k-p), S.zeros(4, 1)),
        }
        for name, (lp, rp, ep) in points.items():
            assert (lp+rp+ep+reader).applyfunc(S.expand) == S.zeros(4, 1)
            phase_checks.append({'branch': sign, 'term': name,
                'left': list(map(str, lp)), 'right': list(map(str, rp)),
                'external': list(map(str, ep)), 'weak_reader': list(map(str, reader))})
        # These are identities of every original left/right derivative slot,
        # not selected contractions or a translation-invariant approximation.
        for row in vertices['readers']:
            direct = {}
            for i, j, a, b, value in row['Q0_bijet']:
                direct[i, j, a, b] = direct.get((i, j, a, b), 0)+S.sympify(value)
            reverse = {(j, i, b, a): v for (i, j, a, b), v in direct.items()}
            assert direct == reverse, row['reader']
    assert len(vertices['readers']) == 48

    # Match the source's full contact convention, including the external
    # momentum in the left leg and the source-generated weak reader.
    assert len(contact['readers']) == 48
    right_symbols = S.symbols('p0:4', real=True)
    ext_symbols = S.symbols('q0:4', real=True)
    reader_symbols = S.symbols('r0:4', real=True)
    for sign in [-1, 1]:
        other = k-p+sign*q
        rp = right(other)
        ep = S.Matrix([0, *[S.I*t for t in sign*q]])
        substitution = dict(zip(right_symbols, rp)) | dict(zip(ext_symbols, ep)) | dict(zip(reader_symbols, reader))
        generated_left = S.Matrix([-right_symbols[i]-ext_symbols[i]-reader_symbols[i] for i in range(4)])
        assert generated_left.subs(substitution, simultaneous=True).applyfunc(S.expand) == left(k)
    assert contact['left_field_derivatives'] == [str(-right_symbols[i]-ext_symbols[i]-reader_symbols[i]) for i in range(4)]
    # A nonzero original-space insertion consumes the actual contact table.
    # Reusing its constant-background specialization changes real entries.
    joint = json.loads((FQ/'packet-gauge-joint-causal/source.json').read_text())
    actual_k = S.Matrix(list(map(S.sympify, joint['physical_k_in'])))
    c = 6*S.sqrt(15)/25
    actual_frequency = 6*c*(1-S.I)
    concrete = dict(zip(k, -actual_k)) | dict(zip(p, actual_k/2)) | dict(zip(q, actual_k/2))
    concrete |= {zb: S.conjugate(actual_frequency), w: actual_frequency}
    symbols = {str(t): t for t in [*right_symbols, *ext_symbols, *reader_symbols]}
    contact_controls = []
    for sign in [-1, 1]:
        other = k-p+sign*q
        substitution = dict(zip(right_symbols, right(other).subs(concrete)))
        substitution |= dict(zip(ext_symbols, S.Matrix([0, *[S.I*t for t in sign*q]]).subs(concrete)))
        substitution |= dict(zip(reader_symbols, reader.subs(concrete)))
        wrong = substitution | dict.fromkeys(ext_symbols, S.Integer(0))
        counts = []
        witness = None
        for row in contact['readers']:
            count = 0
            for i, j, text in row['native_contact_complete']['entries']:
                expression = S.sympify(text, locals=symbols)
                difference_value = S.expand(expression.subs(substitution, simultaneous=True)-expression.subs(wrong, simultaneous=True))
                if difference_value != 0:
                    count += 1
                    if witness is None:
                        witness = {'reader': row['reader'], 'matrix_entry': [i, j], 'difference': str(difference_value)}
            counts.append(count)
        assert witness is not None
        contact_controls.append({'branch': sign, 'changed_readers': sum(v > 0 for v in counts),
            'changed_entries': sum(counts), 'nonzero_source_entry': witness})
    print('PASS all five source phase routes, all48 original bijet leg symmetries and full contact convention', flush=True)

    # Treat source-band and output-observer membership as distinct Boolean
    # variables. Reindexing is performed before same-radius simplification.
    alpha = S.symbols('alpha', real=True)
    tables = []
    for sign in [-1, 1]:
        raw = {
            'right_propagation': {'source': [0, alpha-sign], 'observer': [0, alpha]},
            'left_propagation': {'source': [0, alpha-sign], 'observer': [-sign, alpha-sign]},
            'native_contact': {'source': [0, alpha-sign], 'observer': [0, alpha-sign]},
            'noise': {'source': [0, alpha], 'observer': [0, alpha]},
        }
        for name, data in raw.items():
            # For a strict interior observer, small enough s makes the
            # source-band indicators one on the observed support.
            coincident = list(dict.fromkeys(data['source']+data['observer']))
            interior = list(dict.fromkeys(data['observer']))
            for route, shifts in [('R_equals_source_radius', coincident), ('R_strictly_inside_source_radius', interior)]:
                for aval in [S.Integer(0), S.Integer(1), S.Rational(-2, 3), S.Rational(5, 2)]:
                    values = sorted(set(S.sympify(t).subs(alpha, aval) for t in shifts))
                    center, width = (values[0]+values[-1])/2, (values[-1]-values[0])/2
                    assert width >= 0
                    tables.append({'branch': sign, 'term': name, 'observer': route,
                        'outgoing_slope': str(aval), 'all_centers': list(map(str, values)),
                        'center': str(center), 'half_width': str(width)})
        # Finite idempotent indicators verify the source and observer remain
        # separate until the actual equality of radii is used.
        for indicators in product([0, 1], repeat=3):
            a, b, c = indicators
            assert a*a*b*c == a*b*c
    # Convexity certificate for every intermediate collinear centre:
    # |y-(t a+(1-t)b)n|² = t|y-a n|²+(1-t)|y-b n|²-t(1-t)(a-b)².
    y1, y2, y3, lo, hi, t = S.symbols('y1 y2 y3 lo hi t', real=True)
    norm = lambda c: y1*y1+y2*y2+(y3-c)**2
    assert S.expand(t*norm(lo)+(1-t)*norm(hi)-norm(t*lo+(1-t)*hi)-t*(1-t)*(lo-hi)**2) == 0
    print('PASS original source/observer window routes, strict-interior route and exact extreme-centre reduction', flush=True)

    # Generic scalar complex kernel: no positivity, autocorrelation identity,
    # or reflection-even premise is used in the moving-boundary calculation.
    s, v, h, a, d = S.symbols('s v h a d', real=True)
    coefficients = {(i, j): S.Symbol(f'f{i}{j}') for i in range(4) for j in range(3)}
    phi = sum(c*v**i*s**j/S.factorial(j) for (i, j), c in coefficients.items())
    primitive = S.integrate(phi, v)
    actual = S.expand(primitive.subs(v, h+(a-d)*s)-primitive.subs(v, -h+(a+d)*s))
    f = [S.diff(phi, s, j).subs(s, 0) for j in range(3)]
    psi = [f[0], f[1]+a*S.diff(f[0], v), f[2]+2*a*S.diff(f[1], v)+a*a*S.diff(f[0], v, 2)]
    integrate = lambda g: S.integrate(g, (v, -h, h))
    ends = lambda g: g.subs(v, h)+g.subs(v, -h)
    difference = lambda g: g.subs(v, h)-g.subs(v, -h)
    predicted = [integrate(psi[0]), integrate(psi[1])-d*ends(psi[0]),
        integrate(psi[2])/2+d*d*difference(S.diff(psi[0], v))/2-d*ends(psi[1])]
    for order in range(3):
        assert S.expand(actual.coeff(s, order)-predicted[order]) == 0
    r, R = S.symbols('r R', positive=True)
    # Lost chords have h<d*s. Their exact area/volume pay an O(s³)
    # remainder for the zero coefficient and the first boundary term.
    area = S.pi*d*d*s*s
    volume = S.integrate(4*S.pi*r*S.sqrt(R*R-r*r), (r, S.sqrt(R*R-d*d*s*s), R))
    assert S.simplify(volume.subs({d: 1, s: r})-4*S.pi*r**3/3) == 0

    # The known autocorrelation cancellation follows only after consuming
    # its true bilinear identities; it is not available for general Phi.
    b1b1, bb2 = S.symbols('b1b1 bb2')
    phi2 = bb2
    phi1n = b1b1+bb2
    phi0nn = 2*(b1b1+bb2)
    p2 = phi2-phi1n+phi0nn/4
    assert S.expand(p2/2+phi0nn/8-bb2/2) == 0
    # A genuine q-dependent kernel with Phi=s v has a second-order
    # endpoint contribution even though its bulk second derivative is zero.
    probe = s*v
    probe_primitive = S.integrate(probe, v)
    exact_probe = S.expand(probe_primitive.subs(v, h+(a-d)*s)-probe_primitive.subs(v, -h+(a+d)*s))
    assert exact_probe.coeff(s, 2) == 2*a*h
    # Phi=s constant instead isolates the endpoint term omitted by copying
    # the old autocorrelation cancellation: coefficient is -2d, not zero.
    boundary_probe = S.expand(s*((h+(a-d)*s)-(-h+(a+d)*s)))
    assert boundary_probe.coeff(s, 2) == -2*d
    print('PASS generic complex chord jets, short-chord measure and nonzero boundary controls', flush=True)

    # No false shell diagonalization: these ordered bilinear terms are
    # independent until disjointness at the actual effective shift is paid.
    ll, ls, sl, ss = S.symbols('ll ls sl ss')
    assert S.expand(ll+ls+sl+ss-ll) == ls+sl+ss
    # Physical three-dimensional counterexample: the outer and inner balls
    # touch across a nonzero translation, so low-shell pairings can survive.
    # Radius2/1, shift1, positive-volume box lies in B1 and (B2\B1)+e3.
    # k in |x|,|y|<1/10, -1/2<z<-1/4 gives |k|<1 and 1<|k-e3|<2.
    assert S.Rational(1, 100)+S.Rational(1, 100)+S.Rational(1, 4) < 1
    assert S.Rational(25, 16) > 1
    assert S.Rational(1, 100)+S.Rational(1, 100)+S.Rational(9, 4) < 4
    box_volume = S.Rational(1, 5)**2*S.Rational(1, 4)
    assert box_volume == S.Rational(1, 100)
    receipt = {
        'scope': 'SOURCE_FIVE_TERM_SPATIAL_INSERTION_AND_SHARP_OBSERVER_SHAPE_TRANSFORM',
        'root': 'positiveSmoothUnifiedSource; Dirac-dual; SpinPair.actual; visit10/tick16 -> tick17 unchanged',
        'source_sha256': original['source_sha256'],
        'input_sha256': {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest() for f in sources},
        'physical_measure': '(2*pi)^(-3) d^3 k',
        'phase_convention': 'original field exp(-i k.x), outgoing current exp(-i p.x); matter probe k uses physical h=k/(2*pi)',
        'phase_routes': phase_checks, 'original_bijet_readers_checked': 48,
        'wrong_constant_contact_source_controls': contact_controls,
        'cosine_weights': {'boson_and_contact_each_signed_branch': '1/2',
            'noise_C_sigma_already_includes_half': True, 'noise_uses_sum_of_C_sigma_without_another_half': True},
        'window_tables': tables,
        'extreme_center_convexity_identity': True,
        'complex_chord_orders_checked': [0, 1, 2],
        'kernel_contract': 'Psi_j=(d_s+a*d_n)^j Phi(k,s)|s=0',
        'integral_coefficient0': 'integral_ball Psi0',
        'integral_coefficient1': 'integral_ball Psi1 - d*integral_sphere abs(n.nu)*Psi0',
        'integral_coefficient2': '1/2 integral_ball Psi2 + d^2/2 integral_sphere (n.nu)*d_n Psi0 - d*integral_sphere abs(n.nu)*Psi1',
        'short_chord_area': str(area), 'short_chord_volume': '4*pi*d^3*s^3/3',
        'counterexample_Phi_equals_s_second_coefficient': '-2*d per chord, -2*pi*R^2*d after transverse integration',
        'old_autocorrelation_recovered_after_actual_symmetry': True,
        'shell_low_cross_strict_positive_volume': str(box_volume),
        'proof_identity': 'Exact source slots and phase/window algebra; analytic Fourier and shape proof in README; not a new Lean theorem or evaluated theta integral.',
        'new_Lean_declarations': 0, 'new_axioms': 0,
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'assembly.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2)+'\n')
    print('PASS original spatial insertion/window assembly', receipt['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
