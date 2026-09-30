"""Exact coframe form re-expression; consumer is the original full-CAR H0."""
from pathlib import Path
import hashlib
import json
import time
from dynamic import HERE, ROOT, ROOT_ID
import sympy as s
from source_live_differential_hamiltonian import SourceLiveDifferentialHamiltonian, clean
from source_lorentz_contact import GAMMA, PAIRS


def run(raw):
    q=raw.q; n=raw.source_time[0]; v=q[0]*q[2]*q[5]
    time_at=dict(zip(raw.family.y,raw.source_time))
    def ev(x):
        if isinstance(x,list):return [ev(y) for y in x]
        y=x.subs(time_at)
        return clean(y) if isinstance(y,s.MatrixBase) else s.cancel(y)
    cf={k:ev(raw.family.cf[k]) for k in ('K','M','W','J','one_body','correction','drift')}
    B=[]
    for i in range(3):
        P=GAMMA[0]*GAMMA[i+1]/2
        B.append(s.diag(P,P.conjugate()))
    for j,k in ((2,3),(3,1),(1,2)):
        P=s.I*GAMMA[j]*GAMMA[k]/2
        B.append(s.diag(P,-P.conjugate()))
    P=s.diag(1,1,-1,-1)/2
    B.append(s.diag(P,-P.conjugate()))
    weights=(-s.Rational(3,4),)*3+(-s.S.One,)*3+(s.Rational(3,4),)
    assert all(clean(b.H-b)==s.zeros(8) for b in B)
    Jflat=s.Matrix.hstack(*(J.reshape(64,1) for J in cf['J']))
    tensor=clean(Jflat*cf['W']*Jflat.T)
    predicted=clean(n/v*sum((c*(b.reshape(64,1)*b.reshape(64,1).T) for b,c in zip(B,weights)),s.zeros(64)))
    assert clean(tensor-predicted)==s.zeros(64)
    correction=clean(sum((c*b*b for b,c in zip(B,weights)),s.zeros(8)))
    assert correction==-s.Rational(9,8)*s.eye(8)
    assert clean(cf['one_body']+cf['correction']+s.Rational(9,4)*n/v*s.eye(8))==s.zeros(8)
    Mh=[clean((M+M.H)/2) for M in cf['M']]
    predicted_M=[s.zeros(8),n*q[0]/v*B[5],s.zeros(8),
        n/v*(q[1]*B[3]-q[0]*B[4]),n*q[2]/v*B[3],s.zeros(8)]
    assert all(clean(a-b)==s.zeros(8) for a,b in zip(Mh,predicted_M))
    g=s.Matrix([1/q[j] if j in (0,2,5) else 0 for j in range(6)])
    assert all(clean(Mh[j].diff(q[j]))==s.zeros(8) for j in range(6))
    assert clean(sum((g[j]*Mh[j] for j in range(6)),s.zeros(8)))==s.zeros(8)
    Kpoly=s.Matrix([
        [-q[0]**2,q[0]*q[1],q[0]*q[2],q[0]*q[3],q[0]*q[4],q[0]*q[5]],
        [q[0]*q[1],-4*q[0]**2-q[1]**2,-q[1]*q[2],q[1]*q[3],q[1]*q[4],q[1]*q[5]],
        [q[0]*q[2],-q[1]*q[2],-q[2]**2,q[2]*q[3],q[2]*q[4],q[2]*q[5]],
        [q[0]*q[3],q[1]*q[3],q[2]*q[3],-4*q[0]**2-4*q[1]**2-q[3]**2,-4*q[1]*q[2]-q[3]*q[4],-q[3]*q[5]],
        [q[0]*q[4],q[1]*q[4],q[2]*q[4],-4*q[1]*q[2]-q[3]*q[4],-4*q[2]**2-q[4]**2,-q[4]*q[5]],
        [q[0]*q[5],q[1]*q[5],q[2]*q[5],-q[3]*q[5],-q[4]*q[5],-q[5]**2]])
    assert clean(cf['K']-n/(4*v)*Kpoly)==s.zeros(6)
    number=s.Symbol('N',integer=True,nonnegative=True); alpha=(number+2)/2
    divergence=s.Matrix([sum(cf['K'][i,j].diff(q[i]) for i in range(6)) for j in range(6)])
    h=s.hessian(s.log(v),q)
    shift=s.cancel(alpha*((divergence+(number+2)*cf['K']*g).T*g)[0]-alpha**2*(g.T*cf['K']*g)[0]
        +alpha*sum(value*h[i,j] for (i,j),value in cf['K'].todok().items()))
    assert s.cancel(shift-3*n*(number+2)*(number+4)/(16*v))==0
    assert s.cancel(shift-9*n*number/(8*v)-n/v*(3*number**2/16+s.Rational(3,2)))==0
    e=raw.family.e.subs(time_at)
    ports=raw.full.native.joint.coframe.model.lorentz.raw_matter_ports(e)
    Qi=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]]).inv(method='DM')
    for i in range(3):
        source_spin=clean(-s.I*ports['E'].inv(method='DM')*ports['oriented_principals'][i+1])
        predicted_spin=clean(s.I*n*sum((Qi[i,b]*GAMMA[0]*GAMMA[b+1] for b in range(3)),s.zeros(4)))
        assert clean(source_spin-predicted_spin)==s.zeros(4)
    print('PASS original Dirac spatial principal all6q, retaining full native12 and independent-dual sign',flush=True)
    print('PASS all6q coframe K, complete96-entry normal tensor, seven original Clifford currents, full one-body/half-density and Number cancellation',flush=True)
    return dict(K=cf['K'],generators=B,weights=weights,Mh=Mh,tensor=tensor,half_density=shift)


def action_returns(raw, symbolic):
    from source_joint_form_hamiltonian import read_bound
    from source_coframe_live_ordering import verify_jet_action, full
    from source_gauss_quantum_current import apply_superposition, weighted_sum
    source=raw.source_configuration
    off=tuple(map(s.sympify,read_bound('source_live_differential_hamiltonian')['off_source']['configuration100']))
    records=[]
    for point in (source,off):
        q=point[:6]; v=q[0]*q[2]*q[5]; n=raw.source_time[0]
        at=dict(zip(raw.q,q))|dict(zip(raw.family.y,raw.source_time))
        def ev(x):
            if isinstance(x,list):return [ev(y) for y in x]
            y=x.subs(at)
            return clean(y) if isinstance(y,s.MatrixBase) else s.cancel(y)
        cf={k:ev(x) for k,x in raw.family.cf.items()}
        dl=s.Matrix([1/q[j] if j in (0,2,5) else 0 for j in range(6)])
        hl=s.diag(*[-1/q[j]**2 if j in (0,2,5) else 0 for j in range(6)])
        div=ev(s.Matrix([sum(symbolic['K'][i,j].diff(raw.q[i]) for i in range(6)) for j in range(6)]))
        for word in ((),(0,315),(63,126,252)):
            count=len(word);alpha=s.Rational(count+2,2); f0=s.Rational(3,2)
            g=s.Matrix([s.I*s.Rational(j+1,17) for j in range(6)])
            H=s.Matrix(6,6,lambda i,j:s.Rational((i+1)*(j+1),23)+(1 if i==j else 0))
            old=verify_jet_action(cf,word,f0,g-alpha*dl*f0,
                H-alpha*(dl*g.T+g*dl.T)+alpha**2*dl*dl.T*f0-alpha*hl*f0)
            original={tuple(w):s.sympify(c) for w,c in old['raw_nested_square']}
            unit={word:s.S.One}
            scalar=-sum(c*H[i,j] for (i,j),c in cf['K'].todok().items())-(div.T*g)[0]
            scalar+=(n/v*(s.Rational(3,16)*count**2+s.Rational(3,2))+3*n*v)*f0
            terms=[(scalar,unit)]
            terms += [(-s.I*g[j],apply_superposition(full(ev(symbolic['Mh'][j])),unit)) for j in range(6)]
            terms += [(n/v*c*f0,apply_superposition(full(B),apply_superposition(full(B),unit)))
                for B,c in zip(symbolic['generators'],symbolic['weights'])]
            generated=weighted_sum(terms)
            assert not weighted_sum([(1,generated),(-1,original)])
            records.append({'number':count,'output_words':len(generated),'original_nested_square_return':True})
    print('PASS source/off-source coframe Fock actions N=0,2,3, full moving half-density and both branches',flush=True)
    return records


def main(raw=None):
    began=time.monotonic();raw=SourceLiveDifferentialHamiltonian() if raw is None else raw
    d=run(raw);records=action_returns(raw,d)
    from source_joint_form_hamiltonian import read_bound
    deps=('source_native_energy','source_native_second_form','source_live_differential_hamiltonian',
        'source_temporal_coframe_pairing','independent_source_temporal_coframe_pairing',
        'source_full_quantum_adjoint','source_coframe_legendre','source_lorentz_contact')
    for name in deps:read_bound(name)
    names=('GaussCoframeCore','GaussQuantumMultiplier','GaussCoframeSpin','GaussCoframeKinetic',
        'GaussCoframeForm','GaussMatterCore','GaussDiagonalHistory')
    paths=[Path(__file__)]+[HERE/(name+'.lean') for name in names]
    paths += [HERE/(name+'.json') for name in deps]
    paths += [HERE/name for name in ('source_coframe_live_ordering.py','source_live_differential_hamiltonian.py',
        'source_gauss_quantum_current.py','WeakCoreEvolution.lean','GaussNativeForm.lean')]
    report={'root':ROOT_ID,'scope':'ORIGINAL_H0_CORE_AND_RETARDED_WEAK_HISTORY',
        'source_sha256':raw.full.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'all6_coframe_variables':True,'entire_normal_CAR_tensor_entries':len(d['tensor'].todok()),
        'original_clifford_currents':7,'current_square_weights':list(map(str,d['weights'])),
        'whole_Number_half_density_return':True,'Dirac_spatial_principals_all6q_return':True,
        'Fock_action_returns':records,
        'source_operator':'Literal native + coframe/contact/volume + original Dirac spatial matter_noY, on the same weighted Gauss100 compact full-Fock core. Source-time restriction follows full action variation.',
        'time_contract':'Concrete H0 generates strongly continuous contractions, initial identity, all-time core derivative, original left-test equation and retarded distribution source. No abstract Hamiltonian/symmetry/dense-domain witness is supplied to this source mouth.',
        'time_scope':'Original homogeneous physical k=0 diagonal action; vector weak history does not assert a group law or a two-leg Heisenberg history.',
        'controller':'Original source/root/current and whole ledger unchanged; subordinate producer.',
        'seconds':round(time.monotonic()-began,3)}
    (HERE/'source_diagonal_core_history.json').write_text(json.dumps(report,separators=(',',':'))+'\n')
    print('PASS original concrete H0 core and retarded weak history',report['seconds'],'seconds',flush=True)


if __name__=='__main__':main()
