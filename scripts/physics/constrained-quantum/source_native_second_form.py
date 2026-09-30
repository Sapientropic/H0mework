#!/usr/bin/env python3
"""Original native inverse curvature and literal adjoint-square return."""
from pathlib import Path
import hashlib
import json
import time
import sympy as s
from source_live_differential_hamiltonian import SourceLiveDifferentialHamiltonian, clean, full, DifferentialCAR
from source_joint_ccr_car_ports import NormalSymbol
from source_gauss_quantum_current import apply_superposition, weighted_sum
from source_joint_form_hamiltonian import read_bound
from source_spatial_active_phase_splice import DOMAIN
from dynamic import decode, HERE, ROOT, ROOT_ID


def inverse_curvature_audit(m):
    c=m.source; E=m.embedding[6:,6:]; L=[A[6:,6:] for A in m.L]
    I=c.inverse[:12,6:].col_join(c.inverse[18:,6:]); alpha,beta=I[:12,:],I[12:,:]
    raw=c.inverse_second.rep
    nonzero_corrections=0
    for v in range(106):
        Lie=clean(sum((alpha[a,v]*L[a] for a in range(12) if alpha[a,v]),s.zeros(106)))
        dV=clean(s.Matrix.hstack(*(A*E*beta[:,v] for A in L)))
        partial=clean(-I*dV*alpha)
        transport=clean(-I*Lie)
        bracket=clean(sum((alpha[a,v]*m.structure[a] for a in range(12) if alpha[a,v]),s.zeros(12))*alpha/2)
        predicted=clean(partial+transport+bracket.col_join(s.zeros(94,106)))
        expected=s.SparseMatrix(106,106,{(r,w):DOMAIN.to_sympy(raw.get(r if r<12 else r+6,{}).get(112*(v+6)+(w+6),DOMAIN.zero))
            for r in range(106) for w in range(106)
            if raw.get(r if r<12 else r+6,{}).get(112*(v+6)+(w+6),DOMAIN.zero)})
        assert not clean(predicted-expected).todok(),v
        nonzero_corrections+=bool(clean(transport+bracket.col_join(s.zeros(94,106))).todok())
    assert nonzero_corrections
    print('PASS entire native106 inverse Hessian, all106x106 input pairs; moving-index correction directions',nonzero_corrections,flush=True)
    return {'all_native106_output_rows':True,'all_11236_native_input_pairs':True,
            'nonzero_moving_index_correction_directions':nonzero_corrections}


def native_form_audit(raw, point=None, time_column=None):
    physical=read_bound('source_native_chi_euler_forcing')['source']
    word=tuple(physical['values'][0][0]); value={word:s.S.One}
    g=decode(physical['gradient100'][0][1]); H=decode(physical['Hessian100'][0][1])
    z=raw.source_configuration if point is None else tuple(point)
    time_column=raw.source_time if time_column is None else tuple(time_column)
    base=clean(raw.full.offset+raw.full.embedding*s.Matrix(z))
    E=raw.E; V=clean(s.Matrix.hstack(*(L*base[6:,:] for L in raw.L)))
    I=clean(V.row_join(E).inv(method='DM')); alpha,beta=I[:12,:],I[12:,:]
    d=raw._four_energies(base,tuple(base[:6,:]),base[76:,:].reshape(3,12),time_column)
    G=d['weight']; shift=d['shift']; ds=d['shift_derivative']
    ell=s.zeros(94,1); logH=s.zeros(94)
    for axis,power in raw.density_axes.items():
        ell[axis-6]=power/z[axis]; logH[axis-6,axis-6]=-power/z[axis]**2
    curvature=[]
    for k in range(94):
        dV=clean(s.Matrix.hstack(*(L*E[:,k] for L in raw.L)))
        curvature.append(clean(-I*dV.row_join(s.zeros(106,94))*I))
    divergence=s.Matrix([sum(curvature[k][12+k,j] for k in range(94)) for j in range(106)])
    unitR=[apply_superposition(A,value) for A in raw.full.R]
    def rho(column,f):
        return weighted_sum((column[a],apply_superposition(raw.full.R[a],f)) for a in range(12) if column[a])
    kappa=clean(beta.T*ell)
    inner=[weighted_sum([(-s.I*(beta[:,j].T*g[6:,:])[0]-shift[j]+s.I*kappa[j],value),
        (-s.I,rho(alpha[:,j],value))]) for j in range(106)]
    result=[]
    for (i,j),weight in G.todok().items():
        vi=beta[:,i]; vj=beta[:,j]
        di=clean(sum((vi[k]*curvature[k] for k in range(94) if vi[k]),s.zeros(106)))
        da=di[:12,j]; db=di[12:,j]
        vi_g=(vi.T*g[6:,:])[0]
        derivative=weighted_sum([
            (-s.I*((db.T*g[6:,:])[0]+(vj.T*H[6:,6:]*vi)[0])+
             s.I*((db.T*ell)[0]+(vj.T*logH*vi)[0])-(ds[j,:]*vi)[0]+(s.I*kappa[j]-shift[j])*vi_g,value),
            (-s.I,rho(da,value)),(-s.I*vi_g,rho(alpha[:,j],value))])
        outer=weighted_sum([(-s.I,derivative),(-s.I,rho(alpha[:,i],inner[j])),
            (-shift[i]-s.I*(divergence[i]+kappa[i]),inner[j])])
        result.append((weight/2,outer))
    result.append((d['potential'],value)); actual=weighted_sum(result)
    total=raw.coefficients(z,time_column); cf=d['coframe']; n=time_column[0]; vol=z[0]*z[2]*z[5]
    P=clean(alpha*G*alpha.T/2)
    zero=total.zero
    one=clean(zero.one_body-d['matter_CAR']-full(cf['one_body']+cf['correction'])-
        n*s.Rational(21,16)/vol*raw.identity)
    reduced=NormalSymbol(zero.scalar-n*(s.Rational(3,2)/vol+3*vol),one,zero.pairs[1:1+len(P.todok())])
    principal=total.principal.copy();principal[:6,:6]=s.zeros(6)
    first=total.first.copy();first[:6,:]=s.zeros(6,1)
    currents=(s.zeros(504),)*6+total.current[6:]
    expected=DifferentialCAR(principal,first,currents,reduced).apply(value,{word:g},{word:H})
    residual=weighted_sum([(1,actual),(-1,expected)])
    assert not residual,residual
    print('PASS original native Pi-dagger G Pi, full density/trace/current/CAR terms, literal source H return',len(actual),'output words',flush=True)
    return actual


def main():
    began=time.monotonic(); raw=SourceLiveDifferentialHamiltonian()
    curvature=inverse_curvature_audit(raw.full)
    source=native_form_audit(raw)
    off=read_bound('source_live_differential_hamiltonian')['off_source']
    shifted=native_form_audit(raw,tuple(map(s.sympify,off['configuration100'])),
        tuple(map(s.sympify,off['time4'])))
    deps=('source_native_core_momentum','source_live_differential_hamiltonian',
        'source_common_temporal_form','independent_source_common_temporal_form',
        'source_gauss_history_domain','independent_source_gauss_history_domain',
        'source_full_gauss_section','independent_source_full_gauss_section',
        'source_native_chi_euler_forcing','independent_source_native_chi_euler_forcing')
    for name in deps: read_bound(name)
    paths=[Path(__file__)]+[HERE/(name+'.json') for name in deps]
    paths += [HERE/(name+'.lean') for name in (
        'GaussInverseSecond','GaussSecondCore','GaussDensityCore','GaussFockWeights',
        'GaussScalarTransport','GaussFockPair','GaussMomentumAdjoint')]
    paths += [HERE/name for name in ('source_live_differential_hamiltonian.py',
        'source_gauss_quantum_current.py','source_joint_ccr_car_ports.py')]
    report={'root':ROOT_ID,'scope':'ORIGINAL_GAUSS100_NATIVE_MOMENTUM_ADJOINT_AND_SECOND_CORE',
        'source_sha256':raw.full.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_curvature':curvature,
        'adjoint_square':{'source_output_words':len(source),'off_source_four_time_output_words':len(shifted),
            'all_original_native_trace_density_current_and_normal_CAR_terms_return':True,
            'algorithm':'Literal nested Pi-dagger G Pi/2+V, including derivatives and source half-density, versus the original coefficient-left Hamiltonian and its normal CAR product formula. The original coframe/contact/matter terms are separately identified before comparison.'},
        'kernel_contract':'Original exponential orbit first/second derivatives and full inverse-curvature transport; complete compact Fock second differential; computed density and variable-direction transpose returned to actual weighted SectorHilbert; original native504 Number-weighted current skew; concrete FormalAdjointPair of original momentum and its generated adjoint on the same dense Gauss100 core.',
        'scope':'The full original H0 coefficient/form assembly remains the direct consumer. These are actual source differential/core producers, not an alternate Hamiltonian, a supplied formal-pairing witness, or a completed two-leg/nonlinear time history.',
        'controller':'Original source/root/current and whole ledger unchanged; subordinate producer.',
        'seconds':round(time.monotonic()-began,3)}
    (HERE/'source_native_second_form.json').write_text(json.dumps(report,separators=(',',':'))+'\n')
    print('PASS source native second core and actual momentum adjoint',report['seconds'],'seconds',flush=True)


if __name__ == '__main__': main()
