#!/usr/bin/env python3
"""Actual cosine gauge source: both shifted flows and both current legs.

The finite blocks below generate first variational kernels; they do not truncate
the finite-epsilon spatial evolution to a finite momentum lattice.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    started = time.monotonic()
    original = load(FQ / 'packet-noise/source_kernel.py', 'cosine_original_packet')
    record, (N, omega, H0, Hj, CI, K, w) = original.exact_source()
    clean, zero, decode, encode = original.clean, original.zero, original.decode, original.encode
    c = s.expand(N * s.sqrt(2))
    occupied = json.loads((BASE / 'occupied-response/receipt.json').read_text())
    vertices = json.loads((BASE / 'matter-vertices/receipt.json').read_text())
    full = json.loads((FQ / 'receipt.json').read_text())
    frame = decode(occupied['occupied_frame'])
    density = decode(next(v['operator'] for v in vertices['primitive_vertices']
        if v['group'] == 'gauge_A' and v['coordinate'] == [1, 1]))
    Vfull = clean(-s.I * decode(full['time_principal_inverse']) * density / N)
    V = clean(frame.H * Vfull * frame)
    zero(Vfull * frame - frame * V)
    zero(frame.H * Vfull - V * frame.H)
    zero(V.H - V)
    zero(K * V - V * K)
    zero(K * K - 2 * s.eye(12))
    projection = clean(V * V / N**2)
    zero(projection * projection - projection)
    zero(projection.H - projection)
    assert projection.rank() == 8
    fullH = decode(full['original_H_full'])
    assert clean(fullH - fullH.H).todok()
    pvar = s.symbols('p1:4', real=True)
    kvar = s.symbols('k1:4', real=True)
    hp = clean(H0 + sum((pvar[j] * Hj[j] for j in range(3)), s.zeros(12)))
    hk = clean(sum((kvar[j] * Hj[j] for j in range(3)), s.zeros(12)))
    zero(hp.H - hp)
    zero(K * hp - hp * K)
    zero(hk * hk - N**2 * sum(x*x for x in kvar) * s.eye(12))
    zero(hp.subs({pvar[j]: pvar[j] + kvar[j] for j in range(3)}, simultaneous=True) - hp - hk)
    print('PASS primitive density/N, full252 two-sided reducing, Hermitian12 and K commutation', flush=True)

    causal_path = FQ / 'packet-gauge-causal/source.json'
    causal = json.loads(causal_path.read_text())
    kin = s.Matrix(list(map(s.sympify, causal['physical_momentum'])))
    q = kin / 2
    kout = 3 * kin / 2
    rho = s.sympify(causal['rho'])
    assert s.expand(kin.dot(kin) - 2*rho**2) == 0
    assert all(x != 0 for x in q)
    zero(kout - kin - q)
    v = clean(V / N)
    kb = clean(K / s.sqrt(2))

    def h(momentum):
        value = clean((H0 + sum((momentum[j] * Hj[j] for j in range(3)), s.zeros(12))) / c)
        assert all(x.as_real_imag()[0].is_Rational and x.as_real_imag()[1].is_Rational
            for x in value.todok().values())
        return value

    def expjets(A, sign, order):
        result = [s.eye(12)]
        for n in range(1, order + 1):
            result.append(clean(sign * s.I * A * result[-1] / n))
        return result

    def wavejets(left, right, order):
        er = expjets(right, -1, order)
        d = [s.zeros(12)]
        for n in range(1, order + 1):
            d.append(clean(-s.I * (left * d[-1] + v * er[n-1]) / n))
        # Direct noncommuting matrix powers of the 24x24 variational generator.
        lp, rp = [s.eye(12)], [s.eye(12)]
        for n in range(1, order + 1):
            lp.append(clean(lp[-1] * left))
            rp.append(clean(rp[-1] * right))
            term = sum((lp[n-1-j] * v * rp[j] for j in range(n)), s.zeros(12))
            zero(d[n] - (-s.I)**n * term / s.factorial(n))
        return d

    def currentjets(incoming, shift, sigma, order):
        hr, hl = h(incoming), h(incoming + shift)
        hpr, hout = h(incoming + sigma*q), h(incoming + shift + sigma*q)
        A, Ashift = clean(kb * (hl + hr)), clean(kb * (hout + hpr))
        b, bs = [A], [Ashift]
        C = [clean(kb * v)]
        for n in range(order):
            b.append(clean(s.I * (hl*b[n] - b[n]*hr) / (n+1)))
            bs.append(clean(s.I * (hout*bs[n] - bs[n]*hpr) / (n+1)))
            C.append(clean(s.I * (hout*C[n] - C[n]*hr +
                (v*b[n] - bs[n]*v)/2) / (n+1)))
        ep, eo = expjets(hr, -1, order), expjets(hout, 1, order)
        dm, dp = wavejets(hl, hout, order), wavejets(hpr, hr, order)
        for n in range(order + 1):
            literal = s.zeros(12)
            for j in range(n+1):
                m = n-j
                literal += eo[j]*kb*v*ep[m] + dm[j].H*A*ep[m]/2 + eo[j]*Ashift*dp[m]/2
            zero(literal - C[n])
        zero(C[1] - s.I*kb*(v*(hl-hr) + (hl-hr)*v)/2)
        return C

    incoming = s.sqrt(2) * s.Matrix([s.Rational(2, 2**18), -s.Rational(1, 2**18), s.Rational(3, 2**18)])
    tests = []
    for label, shift in [('quantum_in', -kin), ('quantum_out', -kout), ('zero_current_probe', s.zeros(3, 1))]:
        for sigma in [-1, 1]:
            jets = currentjets(incoming, shift, sigma, 4)
            if label == 'zero_current_probe':
                for coefficient in jets[1:]:
                    zero(coefficient)
            tests.append({'current_probe': label, 'sigma': sigma,
                'physical_transfer': list(map(str, shift + sigma*q)),
                'orders': list(range(5)), 'nonzero_entries_per_order': [len(x.todok()) for x in jets]})
    print('PASS both cosine transfers and both literal current legs through time order4', flush=True)

    selected_path = FQ / 'packet-gauge-noise/selected.json'
    selected = json.loads(selected_path.read_text())
    zero(2*K*V/N**2 - decode(selected['C_selected']))
    zero(c*decode(selected['C_selected'])/2 - 2*kb*v)
    Hq = clean(sum((q[j]*Hj[j] for j in range(3)), s.zeros(12)))
    anticommutator = clean(V*Hq + Hq*V)
    packet_injection = clean(CI*w)
    zero(H0*H0*packet_injection - omega**2*packet_injection)
    raw0 = clean(-s.I*(s.I*s.eye(12)+H0)*packet_injection/(1+omega**2))
    zero((s.I*s.eye(12)-H0)*raw0 - s.I*packet_injection)
    witness = clean(K*anticommutator*raw0/N**2)
    assert witness.todok()
    zero((K*anticommutator).H - K*anticommutator)
    print('PASS original t0 splice, k=0 exact conservation and actual packet wrong-shift witness', flush=True)

    # The wave Laplace transform keeps both source Hamiltonians. This inverse
    # has no energy-difference denominator, including at spectral crossings.
    zbar = 6*(1-s.I)
    block_tests = []
    for sigma in [-1, 1]:
        hr, hl = h(incoming), h(incoming + sigma*q)
        Ar, Al = zbar*s.eye(12)+s.I*hr, zbar*s.eye(12)+s.I*hl
        Rr, Rl = Ar.inv(method='DM'), Al.inv(method='DM')
        zero(Ar*Rr-s.eye(12)); zero(Rr*Ar-s.eye(12))
        zero(Al*Rl-s.eye(12)); zero(Rl*Al-s.eye(12))
        D = clean(-s.I*Rl*v*Rr)
        zero(Al*D+s.I*v*Rr)
        zero(D*Ar+Rl*s.I*v)
        incorrect = clean(D+s.I*Rr*v*Rr)
        assert incorrect.todok()
        block_tests.append({'sigma': sigma, 'left_momentum': list(map(str, incoming+sigma*q)),
            'right_momentum': list(map(str, incoming)),
            'two_sided_24x24_inverse': True,
            'equal_fibre_wrong_kernel_nonzero_entries': len(incorrect.todok())})
    print('PASS actual nonzero-q two-sided wave Laplace inverse; wrong equal-fibre inverse fails', flush=True)

    paths = [BASE/'occupied-response/receipt.json', BASE/'matter-vertices/receipt.json',
        FQ/'receipt.json', selected_path, causal_path,
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketGaugeNoise/Profiles.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketGaugeNoise/Transfer.lean']
    result = {
        'scope': 'STRIKE_ACTUAL_SPATIAL_COSINE_GAUGE_FULL_TIME_SOURCE_VARIATION',
        'source_sha256': record['source_sha256'],
        'source_inputs_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'primitive': 'A_epsilon=actualA+epsilon*cos(q.x)*dx1*S01; fixed original psi/P/sourceFilter and physical time',
        'N': str(N), 'c': str(c), 'omega': str(omega),
        'kin': list(map(str, kin)), 'kout': list(map(str, kout)), 'q': list(map(str, q)),
        'rho_in': str(rho), 'frequency': str(c*zbar),
        'quantum_phase_transfers': {'left': list(map(str, -kin)), 'right': list(map(str, -kout))},
        'V': encode(V), 'K': encode(K), 'H0': encode(H0), 'Hj': list(map(encode, Hj)),
        'source_full252_double_reduction': True, 'source_sector12_Hermitian': True,
        'cosine_preserves_fixed_sector_by_scalar_multiplication': True,
        'unrestricted_full252_Hermitian_claim': False,
        'explicit_wave_kernel': '-i/2 integral E_(p+sigma*q)(t-s) V E_p(s) ds, sigma=-1,+1',
        'wave_laplace_kernel': '-i/2 (z+i*h(p+sigma*q))^-1 V (z+i*h(p))^-1',
        'normalization_of_test_jets': 'tau=c*t; hbar=h/c, vbar=V/N, Kbar=K/sqrt2; C_physical=(2/c)*C_test',
        'incoming_physical_momentum': list(map(str, incoming)), 'time_jet_tests': tests,
        'wave_laplace_tests': block_tests,
        'full_time_zero_probe_identity': 'B_epsilon,0(t)=2*K*(H+epsilon*cos(q.x)*V)/N^2 for every real epsilon,t',
        'wrong_shift_control': {
            'difference_initial_time_slope': 'K/N^2 * M_k*sin(q.x)*{V,H_q}',
            'source_anticommutator_rank': anticommutator.rank(),
            'raw_internal_packet_factor_at0': encode(raw0), 'actual_nonzero_witness': encode(witness),
            'packet_factor_at0': 'Multiply the displayed internal factor by the original unit-ball Fourier value at zero and divide by the fixed positive filtered norm; both scalars are nonzero.',
            'centered_nonzero_argument': 'At k=0 the slope difference is Hermitian sine multiplication by a nonzero finite matrix. The actual packet witness and continuity give nonzero output; a nonzero L2 eigenvector with nonzero eigenvalue would be supported on null sine level sets. Therefore (1-P) times the slope difference is also nonzero.'},
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS cosine source construction', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
