#!/usr/bin/env python3
"""Original light-leg cubic from cofactor minors and native matrix commutators."""
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[5]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
u,q=s.symbols('u q',real=True);p=s.symbols('p0:4',real=True)
START=time.monotonic()


@lru_cache(None)
def norm(x):return s.expand(x)
def clean(M):return s.SparseMatrix(M).applyfunc(norm)
def zero(M):
    rest=clean(M).todok();assert not rest,list(rest.items())[:4]
def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
def pairblock(M):
    A=M.applyfunc(s.re);B=M.applyfunc(s.im)
    return s.SparseMatrix(A.row_join(-B).col_join((-B).row_join(-A)))
def poly_mul(A,B):
    result={}
    for (i,j),a in A.items():
        for (k,l),b in B.items():
            if i+k<=1 and j+l<=1:result[i+k,j+l]=result.get((i+k,j+l),0)+a*b
    return {key:norm(v) for key,v in result.items() if v!=0}
def parity(perm):return (-1)**sum(a>b for i,a in enumerate(perm) for b in perm[i+1:])


def main():
    actual=json.loads((BASE/'active-gauge/receipt.json').read_text())
    field=json.loads((BASE/'full-quantum/light-modes/field-receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())['primitive_vertices']
    bare_frozen=json.loads((HERE.parent/'vertices-receipt.json').read_text())['vertices']
    contact_frozen=json.loads((HERE.parent/'contact-receipt.json').read_text())['all48_current_coefficients']
    total_frozen=json.loads((HERE.parent/'total-receipt.json').read_text())['all48_total_source_cubics']
    for path,digest in actual['source_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    core=ROOT/'Lean/SaturationMonoid/PhysicsCore';gamma=[]
    text=(core/'DiracCliffordRepresentation.lean').read_text()
    for name in ['Zero','One','Two','Three']:
        raw=text.split('def diracGamma'+name+' : DiracMatrix :=',1)[1].split(']',1)[0].split('!![',1)[1]
        gamma.append(s.Matrix([[s.sympify(v.replace('Complex.I','I')) for v in row.split(',')] for row in raw.split(';')]))
    bits=load(BASE/'mixed-symbol/audit/independent_check.py','independent_exterior_bits')
    native=load(BASE/'exact_readout.py','native_original_inventory')
    _,vacuum,_,_=native.parse_source(ROOT)
    raw_generators=native.generators([(0,1,2),(3,4)])
    fundamental=[s.Matrix(m)*(s.I if imaginary else 1) for _,imaginary,m in raw_generators]
    assert fundamental[1]==s.diag(s.Matrix([[0,s.I],[s.I,0]]),s.zeros(5))
    b2=bits.basis(2);triplet=[b2.index((i,5)) for i in range(3)]
    actions=[bits.exterior(A,2).extract(triplet,triplet) for A in fundamental]
    vb=s.Matrix([vacuum.get(word,0) for word in bits.basis(4)])
    orbit=[bits.exterior(A,4)*vb for A in fundamental]
    pairs=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
    wedge=s.Matrix(6,6,lambda i,j:0 if len(set(pairs[i]+pairs[j]))<4 else parity(pairs[i]+pairs[j]))
    N=s.sympify(actual['source_lapse']);e0=s.diag(N,1,1,1)
    indices={(x['group'],tuple(x['coordinate'])):i for i,x in enumerate(actual['fields'])}
    leg=s.SparseMatrix(289,1,{(i,j):s.sympify(v,locals={'u':u,'q':q}) for i,j,v in field['axial_original289_pole_leg']['entries']})
    minus=leg.subs({u:-u,q:-q},simultaneous=True)
    pi=[indices['primal_H',(im,sp,col)] for im in range(2) for sp in range(4) for col in range(3)]
    ci=[indices['dual_H',(im,sp,col)] for im in range(2) for sp in range(4) for col in range(3)]
    xp,xm=leg[pi,:],minus[pi,:];cp,cm=leg[ci,:],minus[ci,:]
    psi=s.Matrix(list(map(s.sympify,actual['actual_background']['primal_H'])))
    exchange=s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),s.eye(3))
    chi=s.sqrt(2)*psi.T*exchange
    x0=psi.applyfunc(s.re).col_join(psi.applyfunc(s.im))
    c0=chi.T.applyfunc(s.re).col_join(chi.T.applyfunc(s.im))
    dualGraph=s.sqrt(2)*s.diag(exchange,-exchange)
    zero(cp-dualGraph*xp);zero(cm-dualGraph*xm)
    badcp=dualGraph*xp.conjugate();badcm=dualGraph*xm.conjugate()

    # All158: realify the primitive coefficient matrices before external Fourier substitution.
    inside=[(d,t) for d in [6,2,4] for t in itertools.combinations(range(7),d)]
    occ=[63*sp+inside.index((2,(col,5))) for sp in range(4) for col in range(3)]
    where={v:i for i,v in enumerate(occ)};bare=[]
    ph={p[0]:N*s.sqrt(2)*u,p[1]:0,p[2]:0,p[3]:s.I*s.sqrt(2)*q}
    for record,expected in zip(vertices,bare_frozen):
        A=s.SparseMatrix(12,12,{(where[i],where[j]):s.sympify(v,locals=dict(zip(map(str,p),p)))
            for i,j,v in record['operator']['entries'] if i in where and j in where})
        B=pairblock(A).subs(ph,simultaneous=True);Bm=B.subs({u:-u,q:-q},simultaneous=True)
        value=norm((cm.T*B*xp+cp.T*Bm*xm)[0])
        assert norm(value-s.sympify(expected['polynomial'],locals={'u':u,'q':q}))==0
        bare.append(value)
    assert sum(v!=0 for v in bare)==18
    assert all(value==0 for value,record in zip(bare,vertices) if record['group']=='scalar')
    print('PASS all158 original bilinear vertices through real block matrices; 18 nonzero and all70 scalar zero',flush=True)

    ep=s.Matrix(4,4,lambda i,j:leg[indices['coframe',(i,j)]])
    em=s.Matrix(4,4,lambda i,j:minus[indices['coframe',(i,j)]])
    zero(ep-em)
    # Cofactor minors generate independent s,t Taylor coefficients; no inverse/Hessian formula is supplied.
    entries=[[{key:v for key,v in [((0,0),e0[i,j]),((1,0),ep[i,j]),((0,1),em[i,j])] if v!=0}
        for j in range(4)] for i in range(4)]
    adj={}
    for mu,a in itertools.product(range(4),repeat=2):
        rows=[i for i in range(4) if i!=a];cols=[j for j in range(4) if j!=mu];terms={}
        for perm in itertools.permutations(range(3)):
            term={(0,0):s.Integer((-1)**(mu+a)*parity(perm))}
            for i in range(3):term=poly_mul(term,entries[rows[i]][cols[perm[i]]])
            for key,value in term.items():terms[key]=terms.get(key,0)+value
        adj[mu,a]={key:norm(value) for key,value in terms.items() if norm(value)!=0}
    def pair_series(B,leftp,leftm):
        return {(0,0):(c0.T*B*x0)[0],(1,0):(leftp.T*B*x0+c0.T*B*xp)[0],
            (0,1):(leftm.T*B*x0+c0.T*B*xm)[0],(1,1):(leftp.T*B*xm+leftm.T*B*xp)[0]}
    Ap=[sum((leg[indices['gauge_A',(mu,j)]]*fundamental[j] for j in range(12)),s.zeros(7)) for mu in range(4)]
    Am=[sum((minus[indices['gauge_A',(mu,j)]]*fundamental[j] for j in range(12)),s.zeros(7)) for mu in range(4)]
    Bp=[sum((leg[indices['gauge_B',(pair,j)]]*fundamental[j] for j in range(12)),s.zeros(7)) for pair in range(6)]
    Bm=[sum((minus[indices['gauge_B',(pair,j)]]*fundamental[j] for j in range(12)),s.zeros(7)) for pair in range(6)]
    for mu in range(4):
        zero(sum((leg[indices['gauge_A',(mu,j)]]*orbit[j] for j in range(12)),s.zeros(35,1)))
        zero(sum((minus[indices['gauge_A',(mu,j)]]*orbit[j] for j in range(12)),s.zeros(35,1)))
    zero(leg[:9,:]);zero(minus[:9,:]);zero(orbit[1])
    # Native U1 pairing is1 rather than mother trace2; all these algebraic curvature
    # directions have exactly zero U1 component, so the direct trace agrees here.
    Y=fundamental[-1]
    for A in fundamental:
        for B in fundamental:assert s.trace(Y*(A*B-B*A))==0
    outputs=[]
    for gen in range(12):
        pairing=[pairblock(s.I*s.kronecker_product(gamma[a],actions[gen])) for a in range(4)]
        ps=[pair_series(B,cp,cm) for B in pairing]
        badps=[pair_series(B,badcp,badcm) for B in pairing]
        for mu in range(4):
            matter=norm(sum(poly_mul(adj[mu,a],ps[a]).get((1,1),0) for a in range(4)))
            wrong_matter=norm(sum(poly_mul(adj[mu,a],badps[a]).get((1,1),0) for a in range(4)))
            def curvature(A):
                return [(fundamental[gen]*A[b]-A[b]*fundamental[gen] if mu==a else s.zeros(7))+
                    (A[a]*fundamental[gen]-fundamental[gen]*A[a] if mu==b else s.zeros(7)) for a,b in pairs]
            fp,fm=curvature(Ap),curvature(Am)
            bf=norm(sum(-wedge[i,j]*s.trace(Bp[i]*fm[j]+Bm[i]*fp[j]) for i,j in itertools.product(range(6),repeat=2) if wedge[i,j]))
            total=norm(matter+bf)
            expected=next(row for row in total_frozen if row['coordinate']==[mu,gen])
            oldcontact=next(row for row in contact_frozen if row['coordinate']==[mu,gen])
            assert norm(matter-s.sympify(expected['matter'],locals={'u':u,'q':q}))==0
            assert norm(bf-s.sympify(expected['gauge_BF'],locals={'u':u,'q':q}))==0
            assert norm(total-s.sympify(expected['total'],locals={'u':u,'q':q}))==0
            oldbare=bare[next(i for i,v in enumerate(vertices) if v['group']=='gauge_A' and v['coordinate']==[mu,gen])]
            contact=norm(matter-oldbare)
            assert norm(contact-s.sympify(oldcontact['contact_polynomial'],locals={'u':u,'q':q}))==0
            outputs.append({'coordinate':[mu,gen],'total':total,'matter':matter,'BF':bf,'contact':contact,'bare':oldbare,
                'fake_Fourier_adjoint_difference':norm(wrong_matter-matter)})
    assert sum(row['total']!=0 for row in outputs)==6
    selected=next(row for row in outputs if row['coordinate']==[1,1])
    assert selected['fake_Fourier_adjoint_difference']!=0
    print('PASS all48 complete source cubics from cofactor minors and literal native BF commutators; 6 nonzero, selected external-adjoint control fails',flush=True)
    result={'status':'PASS','source_sha256_verified':26,'all158_bare_vertices_equal':True,'bare_nonzero':18,
        'all70_scalar_bare_zero':True,'all48_complete_cubics_equal':True,'complete_nonzero':6,
        'coframe_method':'s,t coefficient convolution of true 3x3 cofactor minors',
        'BF_method':'literal7x7 commutators and oriented four-index wedge; native central correction proved zero',
        'scalar_zero_on_affine_light_connection_path':True,'original_source_generator':'A1(S01)=2 sourceColorP286Generator0',
        'internal_canonical_graph_is_true_on_this_leg':True,
        'external_Fourier_conjugation_changes_selected_read':True,
        'selected':{key:(value if key=='coordinate' else str(value)) for key,value in selected.items()},
        'seconds':round(time.monotonic()-START,3)}
    (HERE/'source-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='selected'},indent=2),flush=True)


if __name__=='__main__':main()
