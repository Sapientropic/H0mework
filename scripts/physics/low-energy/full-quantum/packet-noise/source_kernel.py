#!/usr/bin/env python3
"""Actual unit-ball packet filtered by the original Dirac Green.

E=0, eta=1 is evaluated through an exact angular reduction and an exact
unit-ball overlap integral.  Nonzero transfer uses a controlled continuum
bound, retaining the common packet and all shifted overlaps.  No UV cutoff
or independently prepared momentum sectors are introduced.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
import mpmath as mp
import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1]
ROOT = HERE.parents[4]
sys.path.insert(0, str(BASE / 'nonlinear-contact'))
from slice_checks import source_matrices  # noqa: E402


def decode(record, **symbols):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals=symbols)
        for i, j, value in record['entries']})


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def zero(matrix):
    remainder = clean(matrix).todok()
    assert not remainder, list(remainder.items())[:4]


def encode(matrix):
    return {'shape': list(matrix.shape), 'entries': [[int(i), int(j), str(value)]
        for (i, j), value in sorted(clean(matrix).todok().items())]}


def exact_source():
    source_matrices(ROOT)
    phase = json.loads((BASE / 'full-phase/receipt.json').read_text())
    full = json.loads((HERE.parent / 'receipt.json').read_text())
    occupied = json.loads((BASE / 'occupied-response/receipt.json').read_text())
    hashes = phase['source_sha256']
    assert full['source_sha256'] == occupied['source_sha256'] == hashes
    for path, expected in hashes.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path
    N, omega = map(s.sympify, (phase['source_lapse'], phase['source_frequency']))
    spin = s.sqrt(2)
    frame = decode(occupied['occupied_frame'])
    w = decode(occupied['source_prepared'])
    Q = decode(occupied['occupied_phase_charge'])
    H0 = decode(occupied['original_H_constant'])
    Hj = list(map(decode, occupied['H_spatial_coefficients']))
    C = list(map(decode, phase['principal_coefficients']))
    C0inv = decode(full['time_principal_inverse'])
    gamma0 = clean(N * C[0] / s.I)
    Hfull0 = decode(full['original_H_full'])
    Hfullj = [clean(-N * gamma0 * C[j+1] / s.I) for j in range(3)]
    Ytime = decode(full['original_H_yukawa'])
    assert Ytime.todok()  # The actual one-way vertex was not set to zero.
    zero(Ytime * frame); zero(frame.H * Ytime)
    zero(frame.H * frame - s.eye(12))
    for large, small in zip([Hfull0] + Hfullj, [H0] + Hj):
        zero(large * frame - frame * small)
        zero(frame.H * large - small * frame.H)
        zero(small.H-small)
        zero(small*Q-Q*small)
    G0 = clean(frame.H*gamma0*frame)
    C0 = clean(frame.H*C[0]*frame)
    Cinv = clean(frame.H*C0inv*frame)
    zero(C0*Cinv-s.eye(12)); zero(Cinv-s.I*N*G0)
    zero(C0inv*frame-frame*Cinv); zero(gamma0*frame-frame*G0)
    zero(G0.H+G0); zero(G0*G0+s.eye(12))
    zero(w.H*w-s.ones(1)); zero(Q*Q-s.eye(12))
    K = spin*Q
    zero(spin*s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63))*frame-frame*K)
    p = s.symbols('p1:4', real=True)
    radius2 = sum(x*x for x in p)
    z = s.symbols('z')
    H = clean(H0+sum((p[j]*Hj[j] for j in range(3)), s.zeros(12)))
    spatial = clean(H-H0)
    zero(spatial*spatial-N*N*radius2*s.eye(12))
    smallD = clean(-s.I*C0*(z*s.eye(12)-H))
    B, Y = map(decode, (phase['original_constant_B'], phase['original_Y']))
    fullD = clean(-s.I*z*C[0]+B+Y+sum((s.I*p[j]*C[j+1] for j in range(3)), s.zeros(252)))
    zero(fullD*frame-frame*smallD)
    # The source vectors generate a two-dimensional cyclic block in each chirality.
    columns = []; chirality_records = []
    for sign in [-1, 1]:
        seed = clean((s.eye(12)+sign*Q)*G0*w/2)
        partner = clean((sign*H-omega*s.eye(12))*seed/N)
        zero(seed.H*seed-s.ones(1)/2)
        zero(seed.H*partner)
        zero(partner.H*partner-radius2*s.ones(1)/2)
        zero(H*seed-sign*(omega*seed+N*partner))
        zero(H*partner-sign*(N*radius2*seed+3*omega*partner))
        numerator = clean((z-3*sign*omega)*seed+sign*N*partner)
        denominator = (z-sign*omega)*(z-3*sign*omega)-N*N*radius2
        zero((z*s.eye(12)-H)*numerator-denominator*seed)
        assert s.simplify(s.im(denominator.subs(z,s.I))+4*sign*omega)==0
        at_i = numerator.subs(z,s.I)
        zero(at_i.H*at_i-(1+9*omega**2+N*N*radius2)*s.ones(1)/2)
        zero(at_i.H*K*H*at_i-
            spin*omega*(1+9*omega**2-3*N*N*radius2)*s.ones(1)/2)
        columns.append(numerator/denominator)
        chirality_records.append({'sign': sign, 'seed': encode(seed),
            'partner': encode(partner), 'denominator': str(s.expand(denominator))})
    raw = -N*sum(columns,s.zeros(12,1))
    zero((smallD*raw-w).applyfunc(s.cancel))
    A0 = clean(2*K*H/N**2)
    zero(A0.H-A0); zero(A0.H*A0-8*H*H/N**4)
    r = s.symbols('r',nonnegative=True)
    den = (1-3*omega**2+N*N*r*r)**2+16*omega**2
    norm = s.factor(N*N*(1+9*omega**2+N*N*r*r)/den)
    mean = s.factor(2*spin*omega*(1+9*omega**2-3*N*N*r*r)/den)
    # The ball overlap identity gives the exact half-line radial integral.
    kappa = s.symbols('kappa',nonzero=True)
    x = s.symbols('x',real=True)
    overlap = x-s.Rational(3,4)*x*x+x**4/s.Integer(16)
    J = (2*kappa**3-3*kappa**2+3-3*(kappa+1)**2*s.exp(-2*kappa))/(2*kappa**5)
    primitive = s.integrate(overlap*s.exp(-kappa*x), x)
    assert s.simplify(primitive.subs(x,2)-primitive.subs(x,0)-J)==0
    assert s.integrate(overlap,(x,0,2))==s.Rational(2,5)
    record = {'source_sha256': hashes,'lapse':str(N),'frequency':str(omega),
        'full252_to_original12_both_sides':True,'original_nonzero_Y_reducing_not_deleted':True,
        'original_Dirac_inverse_side':'R(z,p)=i (z-H(p))^-1 C0^-1 = -N (z-H(p))^-1 gamma0',
        'original_D_R_w_rational_identity':True,
        'regular_domain':'Both (z-sign*omega)(z-3*sign*omega)-N^2*|p|^2 are nonzero. At z=i and real p their imaginary parts are -4*sign*omega, so the selected domain is all real momenta.',
        'source_chiral_cyclic_blocks':chirality_records,
        'cyclic_matrix_in_normalized_basis':'sign * [[omega,N*r],[N*r,3*omega]]',
        'source_chiral_norms':'||seed||^2=1/2; ||partner||^2=|p|^2/2; inner(seed,partner)=0',
        'zero_transfer_raw_norm_integrand':str(norm),
        'zero_transfer_raw_mean_integrand':str(mean),
        'zero_transfer_second_moment_identity':'8/(N^2*n^2)-8/N^4',
        'second_moment_scope':'The quadratic form ||A_h psi||^2; no claim that psi belongs to D(A_h^2).',
        'ball_fourier_physical':'bhat(p)=4*pi*(sin(r)-r*cos(r))/(r^3*sqrt(4*pi/3)); r=|p|; p=2*pi*xi',
        'ball_radial_measure':'6/pi*(sin(r)-r*cos(r))^2/r^4 dr',
        'ball_overlap_J':str(J),
        'closed_filtered_observables':{'kappa':'sqrt((1-3*omega^2+4*i*omega)/N^2), Re kappa>0',
            'Z':'(i-3*omega)*J(kappa)','norm_squared':'n^2=Im Z',
            'mean':'mu_0=(2*sqrt(2)/N^2)*Re Z/Im Z',
            'centered_noise':'8/(N^2*n^2)-8/N^4-mu_0^2'},
        'overlap_derivation':'Normalized ball overlap is 1-3r/4+r^3/16 on 0<=r<=2. The Yukawa kernel e^-kappa*r/(4*pi*r) gives J=integral_0^2 r*overlap*e^-kappa*r dr.',
        'finite_overlap_primitive_checked':True}
    return record, (N,omega,H0,Hj,Cinv,K,w)


def interval_values(dps):
    iv=mp.iv;iv.dps=dps
    N=iv.sqrt(iv.mpf(54)/125); spin=iv.sqrt(2); omega=3*N*spin/5
    real=(1-3*omega**2)/N**2;imag=4*omega/N**2
    modulus=iv.sqrt(real**2+imag**2)
    kappa=iv.mpc(iv.sqrt((modulus+real)/2),iv.sqrt((modulus-real)/2))
    J=(2*kappa**3-3*kappa**2+3-3*(kappa+1)**2*iv.exp(-2*kappa))/(2*kappa**5)
    Z=(iv.j-3*omega)*J
    n2=Z.imag
    mean=2*spin/N**2*Z.real/n2
    second=8/(N**2*n2)-8/N**4
    variance=second-mean**2
    assert n2.a>0 and n2.b<N**2
    assert variance.a>0 and mean.b<0
    # All physical-space estimates use the same response-filtered packet.
    radius_moment=iv.sqrt(iv.mpf(3)/5)
    xpsi=(iv.sqrt(3)*N**2+N*radius_moment)/iv.sqrt(n2)
    xHpsi=xpsi+N*radius_moment/iv.sqrt(n2)
    lipschitz=2*spin/N**2*xHpsi+spin/N
    physical_transfer=iv.mpf(1)/65536
    error=(lipschitz*physical_transfer).b
    # Interval endpoints are kept as outward MP intervals, not rounded floats.
    mean_h=iv.mpf([mean.a-error,mean.b+error])
    second_h=iv.mpf([(iv.sqrt(second).a-error)**2,(iv.sqrt(second).b+error)**2])
    variance_h=iv.mpf([(iv.sqrt(variance).a-2*error)**2,(iv.sqrt(variance).b+2*error)**2])
    assert iv.sqrt(variance).a>2*error and variance_h.a>0
    return {'interval_decimal_precision':dps,'method':'mpmath.iv outward interval arithmetic on exact closed overlap formula',
        'kappa_real':str(kappa.real),'kappa_imaginary':str(kappa.imag),
        'raw_filtered_norm_squared':str(n2),'normalized_packet_norm_squared':'[1,1]',
        'current_mean_h0':str(mean),'current_second_moment_h0':str(second),'centered_noise_h0':str(variance),
        'nonzero_transfer':{'physical_q':['0','0','1/65536'],'Fourier_shift_h':['0','0','1/(131072*pi)'],
            'current_vector_error_upper':str(error),'mean_enclosure':str(mean_h),
            'second_moment_enclosure':str(second_h),'centered_noise_enclosure':str(variance_h)},
        'continuum_control':{'unit_ball_position_moment':'sqrt(3/5)',
            'weighted_filtered_packet_bound':str(xpsi),'weighted_H_packet_bound':str(xHpsi),
            'current_Lipschitz_constant_upper':str(lipschitz.b),
            'proof':'On the actual reducing sector: ||R||<=N, ||d_pj R||<=N^2, Hj^2=N^2. Thus |||x|psi||<=(sqrt(3)N^2+N sqrt(3/5))/n and |||x|Hpsi||<=(sqrt(3)N^2+2N sqrt(3/5))/n. A_q-A_0=2 K(M_q-1)H/N^2+[H,M_q]K/N^2, with ||[H,M_q]||<=N|q|. Hence ||(A_q-A_0)psi||<=L|q|, |mu_q-mu_0|<=L|q| and |sqrt(var_q)-sqrt(var_0)|<=2L|q|.'}}


def build_numeric_kernel(data):
    """Actual shared packet and current functions; all momenta are physical p=2*pi*xi."""
    import numpy as np
    N,omega,H0,Hj,Cinv,K,w=data
    N=float(N);omega=float(omega)
    H0=np.array(H0.evalf(),dtype=complex);Hj=[np.array(x.evalf(),dtype=complex) for x in Hj]
    Cinv=np.array(Cinv.evalf(),dtype=complex);K=np.array(K.evalf(),dtype=complex);w=np.array(w,dtype=complex).ravel()
    def H(p):return H0+sum((float(p[j])*Hj[j] for j in range(3)),np.zeros((12,12),complex))
    def ball(p):
        r=float(np.linalg.norm(p))
        if r<1e-3:return np.sqrt(4*np.pi/3)*(1-r*r/10+r**4/280-r**6/15120)
        return 4*np.pi*(np.sin(r)-r*np.cos(r))/(r**3*np.sqrt(4*np.pi/3))
    def raw(p):return 1j*np.linalg.solve(1j*np.eye(12)-H(p),Cinv@w)*ball(p)
    def current_raw(p,q):
        out=H(p); result=np.zeros(12,complex)
        for sign in (-1,1):
            incoming=np.asarray(p)-sign*np.asarray(q)
            result+=(K@H(incoming)+out.conj().T@K)@raw(incoming)/(2*N*N)
        return result
    return {'H':H,'ball_fourier':ball,'raw_packet':raw,'current_raw':current_raw,'C0inv':Cinv,'prepared':w,'K':K,'lapse':N}


def numeric_probes(data):
    import numpy as np
    kernel=build_numeric_kernel(data)
    H,ball,raw,current_raw=[kernel[name] for name in ['H','ball_fourier','raw_packet','current_raw']]
    Cinv,w=kernel['C0inv'],kernel['prepared']
    probes=[]
    for point in ([0.,0.,0.],[1/7,-2/11,3/13],[2.,-1.,.5]):
        q=np.array([0.,0.,1/65536]);p=np.array(point)
        Rw=raw(p);D=-1j*np.linalg.inv(Cinv)@(1j*np.eye(12)-H(p))
        direct_zero=2*kernel['K']@H(p)@Rw/kernel['lapse']**2
        assert np.linalg.norm(current_raw(p,np.zeros(3))-direct_zero)<2e-13
        residual=float(np.linalg.norm(D@Rw-ball(p)*w));assert residual<2e-13
        probes.append({'physical_p':list(point),'Dirac_equation_residual':residual,
            'raw_packet_norm_squared':float(np.vdot(Rw,Rw).real),
            'nonzero_transfer_current_norm_squared':float(np.vdot(current_raw(p,q),current_raw(p,q)).real)})
    return probes


def radial_crosscheck(data):
    """Independent physical-Fourier quadrature; the main evaluator remains the exact overlap formula."""
    import numpy as np
    from scipy.integrate import quad
    N,omega=float(data[0]),float(data[1])
    radius=96.0
    def radial(r):
        if r<1e-3:
            bessel=r/3-r**3/30+r**5/840
        else:
            bessel=(np.sin(r)-r*np.cos(r))/(r*r)
        denominator=(1-3*omega*omega+N*N*r*r)**2+16*omega*omega
        green_norm=N*N*(1+9*omega*omega+N*N*r*r)/denominator
        return 6/np.pi*bessel*bessel*green_norm
    value,error=quad(radial,0,radius,epsabs=2e-13,epsrel=2e-13,limit=1000)
    # For r>=radius>=6 omega/N: ||R w||^2<=4/r^2.
    assert radius>=6*omega/N
    tail=8/np.pi*(1+1/radius)**2/radius**3
    mp.mp.dps=45
    n=mp.sqrt(mp.mpf(54)/125);o=3*n*mp.sqrt(2)/5;k=mp.sqrt((1-3*o*o+4j*o)/(n*n))
    J=(2*k**3-3*k**2+3-3*(k+1)**2*mp.exp(-2*k))/(2*k**5)
    closed=float(mp.im((1j-3*o)*J))
    assert -10*error<=closed-value<=tail+10*error
    return {'finite_diagnostic_radius':radius,'finite_radial_norm_squared':value,
        'quadrature_reported_error':error,'positive_infinite_tail_upper':tail,
        'closed_minus_finite':closed-value,
        'tail_derivation':'For r>=R>=6omega/N, resolvent norm gives g(r)<=4/r^2 and (sin r-r cos r)^2/r^4<=(1+1/R)^2/r^2; integrate to infinity.',
        'radius_is_only_a_check_parameter_not_a_UV_cutoff':True,
        'reported_quadrature_error_is_not_used_for_main_interval_certification':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--dps',type=int,default=50)
    args=parser.parse_args();started=time.monotonic()
    exact,data=exact_source()
    # Exact source values establish the constants used in interval evaluation.
    assert s.simplify(data[0]**2-s.Rational(54,125))==0
    assert s.simplify(data[1]-3*data[0]*s.sqrt(2)/5)==0
    intervals=interval_values(args.dps)
    probes=numeric_probes(data)
    radial=radial_crosscheck(data)
    result={'scope':'ORIGINAL_CONTINUUM_UNIT_BALL_DIRAC_FILTERED_CURRENT_NOISE',
        'spectral_parameters':{'E':0,'eta':1},'exact_source':exact,'evaluations':intervals,'direct_kernel_probes':probes,'independent_Fourier_radial_check':radial,
        'general_nonzero_shift_kernel':{'raw_packet':'psi_raw(p)=i*(i-H(p))^-1*C0^-1*w*bhat(p)',
            'current':'(A_h psi)(p)=sum_sign [K H(p-sign*q)+H(p)^dagger K]/(2N^2) * psi(p-sign*q); q=2*pi*h',
            'mean':'integral psi(p)^dagger (A_h psi)(p) d^3p/(2*pi)^3',
            'centered_noise':'integral ||(A_h psi)(p)-mu_h psi(p)||^2 d^3p/(2*pi)^3',
            'shared_packet_overlap_retained':True,'same_sign_terms_removed':False},
        'claim_level':'Exact finite source algebra, analytic radial/overlap derivation, interval evaluation and explicit nonzero-shift bounds; no new Lean integral theorem is claimed.',
        'no_UV_cutoff_or_experimental_units':True,'no_new_vacuum_or_momentumwise_preparation':True,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source-kernel-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    summary=f'''# 原连续波包电流核

原单位球 preparedPacket 经原 Dirac Green（E=0,η=1）滤波，保留 R=i(z−H)⁻¹C0⁻¹ 和同一空间准备。

- 滤波归一化 n²≈0.208904454900。
- h=0 的真实均值 μ≈−0.701355479214，**不是零**。
- h=0 的中心化噪声≈45.287036020565，严格为正。
- 非零物理转移 q=(0,0,1/65536)，h=q/(2π)：μ∈[−0.701775,−0.700936]；中心化噪声∈[45.27575,45.29832]。

原 H12 和制备向量自动生成旋转不变的两维循环块。径向积分精确化为单位球重叠的有限指数积分 J(κ)，没有 UV 截断；独立物理 Fourier 径向积分亦通过带无限尾界的复核。非零转移范围由实际空间矩与 cosine commutator 界产生，完整保留共同波包平移重叠。

source_kernel.py 校验全252→原12双侧身份、原 i/C0、全部符号动量循环块和原Dirac方程，并输出 {args.dps} 位 outward interval enclosure。build_numeric_kernel 返回可直接消费的 H、原波包和重叠 current 函数。积分与非零转移界是已给出的解析推导；不冒充新增 Lean 积分定理。精确公式与完整区间见 source-kernel-receipt.json。
'''
    (HERE/'source-kernel-summary.md').write_text(summary)
    print(json.dumps({'scope':result['scope'],'evaluations':intervals,'elapsed_seconds':result['elapsed_seconds']},indent=2),flush=True)


if __name__=='__main__':main()
