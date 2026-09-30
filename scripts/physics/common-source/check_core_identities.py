#!/usr/bin/env python3
"""Finite matrix/arithmetic checks of the paper's displayed formulas.

No Lean build, no runtime replay, no Bell event data, no statistical refitting.
Run with the existing figtools environment; output is a separate editorial check.
"""
from __future__ import annotations
import hashlib
import itertools
import json
from pathlib import Path
import numpy as np

H = 'e60a86058abcb74b7f2225f2383c182be8343785'
k = np.sqrt(2.0); a = 3*k/5; N = np.sqrt(54/125); sigma = .5
omega = 3*N*(k-a)/2
I2 = np.eye(2); Z2 = np.zeros((2,2))
pauli = [np.array([[0,1],[1,0]]), np.array([[0,-1j],[1j,0]]), np.diag([1,-1])]
gamma = [np.block([[Z2,I2],[-I2,Z2]])] + [np.block([[Z2,s],[s,Z2]]) for s in pauli]
tau = [1j*s/2 for s in pauli]
pairs = [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
complement = [3,4,5,0,1,2]
eta = np.array([-1,1,1,1]); eps = np.array([-1,-1,-1,1,1,1])
J = np.block([[np.zeros((3,3)),np.eye(3)],[-np.eye(3),np.zeros((3,3))]])
e = np.diag([N,1,1,1]); B = np.block([[np.zeros((3,3)),np.eye(3)],[-N*np.eye(3),np.zeros((3,3))]])
lam = np.diag([-N]*3+[k*k-1]*3)
spin = np.zeros((4,4,4))
for mu,(i,j) in enumerate(pairs[3:],1): spin[mu,i,j] = k; spin[mu,j,i] = -k
G8 = [np.kron(g,I2) for g in gamma]
S8 = np.kron(np.block([[Z2,I2],[I2,Z2]]),I2)
errs: dict[str,float] = {}
evaluations: dict[str,int] = {}
def check(name: str, actual, expected=0):
    error=float(np.max(np.abs(np.asarray(actual)-np.asarray(expected))))
    errs[name]=max(errs.get(name,0.0),error)
    evaluations[name]=evaluations.get(name,0)+1

def wedge_e(f):
    return np.array([[f[i,m]*f[j,n]-f[i,n]*f[j,m] for m,n in pairs] for i,j in pairs])
def Wtop(x,y): return np.sum(eps[:,None]*x*y[:,complement])

for mu,nu in itertools.product(range(4),repeat=2):
    check('clifford',gamma[mu]@gamma[nu]+gamma[nu]@gamma[mu],2*(eta[mu] if mu==nu else 0)*np.eye(4))
Fraw=np.array([[eta[i]*(spin[m]@spin[n]-spin[n]@spin[m])[i,j] for m,n in pairs] for i,j in pairs])
Fhat=eps[:,None]*Fraw
check('spin_curvature',Fhat,np.diag([0]*3+[-k*k]*3))
check('simplicity',B,J@wedge_e(e))
check('gravity_auxiliary',Fhat-J@B+lam)
Hodge=np.block([[np.zeros((3,3)),np.eye(3)/N],[-N*np.eye(3),np.zeros((3,3))]])
for i in range(3):
    check('gauge_curvature',a*a*(tau[(i+1)%3]@tau[(i+2)%3]-tau[(i+2)%3]@tau[(i+1)%3]),-a*a*tau[i])
check('gauge_threeform_balance',2*a**3/(sigma*N)-4*N*k)
check('hodge_squared',Hodge@Hodge,-np.eye(6))
# Full original coframe directions, with all other field values frozen.
T=np.diag([4*k*omega]+[-2*k*(k-a)]*3)
for row,col in itertools.product(range(4),repeat=2):
    D=np.zeros((4,4));D[row,col]=1
    dSigma=wedge_e(e+D)-wedge_e(e)-wedge_e(D)
    grav=-Wtop(lam,J@dSigma)
    inv=np.linalg.inv(e)
    matter=N*np.sum((-inv@D@inv).T*T)
    gauge=a**4/(4*sigma*N*N)*(3*D[0,0]-N*np.trace(D[1:,1:]))
    expected_grav=(3 if row==0 else -N) if row==col else 0
    check('coframe_gravity_16',grav,expected_grav)
    check('coframe_total_16',grav+matter+gauge)
# 252-dimensional embedding uses the declared exterior basis, not a fitted map.
wedges2=list(itertools.combinations(range(7),2)); E=np.zeros((252,8),complex)
for r,s in itertools.product(range(4),range(2)): E[r*63+7+wedges2.index((s,5)),r*2+s]=1
P=E.conj().T
check('occupied_embedding',P@E,np.eye(8))
rng=np.random.default_rng(20260920)
angles=[0,np.pi/4,np.pi/2,3*np.pi/4,np.pi]+list(rng.uniform(-10,10,7))
for theta in angles:
    u,v=np.exp(1j*theta),np.exp(-1j*theta)
    psi=np.array([0,u,-u,0,0,v,-v,0]); chi=k*psi; state=psi/2
    check('occupied_normalization',np.vdot(state,state),1)
    check('dual_coefficient_bridge',chi,2*k*np.conj(S8@state))
    dpsi=1j*omega*np.array([1]*4+[-1]*4)*psi
    Dpsi=[dpsi]
    Qrow=np.zeros(8,complex)
    for i,(b,c) in enumerate(pairs[3:]):
        R=np.kron(gamma[b]@gamma[c],I2)
        charge=np.kron(np.eye(4),tau[i])
        check('spin_color_lock',charge@psi,-R@psi/2)
        Dpsi.append((k-a)*R@psi/2)
        Qrow+=N*chi@(1j*G8[i+1])@((k-a)*R/2)
        check('same_current',N*chi@(1j*G8[i+1])@charge@psi,2*N*k)
    check('primal_dirac',(1j/N)*G8[0]@Dpsi[0]+sum(1j*G8[j]@Dpsi[j] for j in range(1,4)))
    dchi=k*dpsi
    check('independent_dual',Qrow,dchi@(1j*G8[0]))
    computedT=np.array([[np.real(chi@(1j*G8[mu])@Dpsi[nu]) for nu in range(4)] for mu in range(4)])
    check('kinetic_load_16',computedT,T)
    for mu,I in itertools.product(range(4),range(6)):
        b,c=pairs[I]
        val=np.real(.5j*chi@np.kron(gamma[mu]@gamma[b]@gamma[c],I2)@psi)
        check('cartan_spin_24',val,-2*k if (mu,I) in [(1,3),(2,4),(3,5)] else 0)
    A=(rng.normal(size=(252,252))+1j*rng.normal(size=(252,252)))/252
    motherpsi=E@psi; motherchi=chi@P
    check('golden_full_nonhermitian_252',motherchi@A@motherpsi,4*k*np.vdot(state,S8@P@A@E@state))
    # The incorrectly omitted exchange: current control at all these times.
    raw=np.vdot(state,1j*np.kron(gamma[1],tau[0])@state)
    check('dark_control_curve',raw,.5*np.cos(2*theta))
report={'source_revision':H,'scope':__doc__.strip(),'status':'passed','absolute_tolerance':1e-10,
        'families':len(errs),'evaluations':sum(evaluations.values()),'family_evaluations':evaluations,
        'max_residual':max(errs.values()),'residuals':errs,'numpy_version':np.__version__,
        'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'coframe_gauge_check':'uses the source-derived first-variation coefficient (4.17); not a new symbolic derivation of the Hodge variation',
        'excluded':['Lean rebuild','source runtime execution','full Fock CAR rerun','Bell event scoring','calibration fitting']}
if report['max_residual']>report['absolute_tolerance']: raise AssertionError(report)
out=Path(__file__).with_name('core-identity-checks.json');out.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['status','families','evaluations','max_residual']},ensure_ascii=False))
