#!/usr/bin/env python3
"""The actual exchanged field returned to the native full252 matter action.

This is a finite-field reaction producer.  It consumes the existing four-block
field, rebuilds adj(e), det(e), connections and Yukawa before taking the temporal
Legendre inverse, and computes the resulting current feedback.  No companion
pole is reinterpreted as an interacting many-body spectral pole.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, SourceExchange, decode


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    assert not clean(left-right).todok()


def encode(matrix):
    return {"shape":list(matrix.shape), "entries":[[int(i),int(j),str(v)]
        for (i,j),v in sorted(clean(matrix).todok().items())]}


def scalar(value):
    return s.expand(s.radsimp(s.expand(value)))


class NativeMatterReaction:
    """Coordinates are the original fields, never independently chosen couplings."""
    def __init__(self):
        self.source=SourceExchange()
        self.phase=json.loads((BASE/'full-phase/receipt.json').read_text())
        assert self.phase['source_sha256']==self.source.vertices['source_sha256']
        self.active=self.source.active
        self.N=self.source.N
        self.omega=self.source.omega
        self.C=list(map(decode,self.phase['principal_coefficients']))
        self.Gamma=[clean(-s.I*self.N*self.C[0])]+[clean(-s.I*x) for x in self.C[1:]]
        self.gamma=[x.extract([63*j for j in range(4)],[63*j for j in range(4)]) for x in self.Gamma]
        for full,small in zip(self.Gamma,self.gamma):
            equal(full,s.kronecker_product(small,s.eye(63)))
        self.Q=decode(self.phase['phase_generator'])
        self.Y=decode(self.phase['original_Y'])
        self.primitive={(v['group'],tuple(v['coordinate'])):decode(v['operator'])
                        for v in self.source.vertices['primitive_vertices']}
        self.E0=clean(self.N*self.C[0])
        inverse4=self.E0.extract([63*j for j in range(4)],[63*j for j in range(4)]).inv()
        self.E0inv=clean(s.kronecker_product(inverse4,s.eye(63)))
        equal(self.E0*self.E0inv,s.eye(252))
        self.rho=[clean(self.E0inv*self.primitive['gauge_A',(0,a)]) for a in range(12)]
        self.spin=[clean(self.E0inv*self.primitive['Lorentz',(0,a)]) for a in range(6)]
        bg=self.active['actual_background']
        self.e0=s.Matrix(bg['coframe']).applyfunc(s.sympify)
        self.A0=s.Matrix(bg['gauge_connection']).applyfunc(s.sympify)
        self.O0=s.Matrix(bg['lowered_Lorentz_connection']).applyfunc(s.sympify)
        self.vertices={v['field']:decode(v['operator']) for v in self.source.vertices['active_289_bosonic_source_operators']}

    def configuration(self, field):
        e,A,O,Y=self.e0.copy(),self.A0.copy(),self.O0.copy(),self.Y.copy()
        for index in self.source.order:
            value=field[index]
            if value==0: continue
            entry=self.active['fields'][index]
            group,coord=entry['group'],entry['coordinate']
            if group=='coframe': e[tuple(coord)]+=value
            elif group=='gauge_A': A[tuple(coord)]+=value
            elif group=='Lorentz': O[tuple(coord)]+=value
            elif group=='scalar_J': Y+=value*self.vertices[index]/self.N
            else: raise AssertionError(group)
        return e,A,O,clean(Y)

    def densitized(self, field, momentum):
        e,A,O,Y=self.configuration(field)
        adj=clean(e.adjugate(method='berkowitz'))
        volume=scalar(e.det(method='berkowitz'))
        connections=[clean(sum((A[mu,a]*self.rho[a] for a in range(12)),s.zeros(252))+
                          sum((O[mu,a]*self.spin[a] for a in range(6)),s.zeros(252))) for mu in range(4)]
        contracted=[clean(sum((adj[mu,a]*s.I*self.Gamma[a] for a in range(4)),s.zeros(252))) for mu in range(4)]
        E=contracted[0]
        K=clean(sum((contracted[mu]*connections[mu] for mu in range(4)),s.zeros(252))+
                sum((contracted[j+1]*(s.I*momentum[j]) for j in range(3)),s.zeros(252))+
                sum((adj[0,a]*self.omega*self.Gamma[a]*self.Q for a in range(4)),s.zeros(252))+volume*Y)
        E4=E.extract([63*j for j in range(4)],[63*j for j in range(4)])
        equal(E,s.kronecker_product(E4,s.eye(63)))
        return {'coframe':e,'adjugate':adj,'volume':volume,'E':E,'E4':E4,'K':K,
                'contracted':contracted,'connections':connections,'Y':Y}

    def temporal(self, data):
        square=clean(data['E4']*data['E4'])
        norm=square[0,0]
        assert norm!=0
        equal(square,norm*s.eye(4))
        inverse4=data['E4'].applyfunc(lambda x:scalar(x/norm))
        equal(data['E4']*inverse4,s.eye(4))
        equal(inverse4*data['E4'],s.eye(4))
        inverse=clean(s.kronecker_product(inverse4,s.eye(63)))
        H=clean(-s.I*inverse*data['K'])
        equal(data['E']*(-s.I*H)+data['K'],s.zeros(252))
        return H,inverse

    def canonical_ports(self, field, momentum):
        """Full native matter flow and the action-owned boson feedback ports.

        For canonical CAR momentum p=-i*zeta*E, the source is -p*W_a*xi.
        Thus a caller supplies an actual field/state, never a coupling matrix.
        The retarded field equation subsequently uses b=-G_ret*j.
        """
        data=self.densitized(field,momentum)
        H,inverse=self.temporal(data)
        ports={}
        for field_index in self.source.order:
            Ea,Ka=self.primitive_tangent(data,field_index,momentum)
            W=clean(-inverse*Ea*H-s.I*inverse*Ka)
            equal(data['E']*(-s.I*W)+Ea*(-s.I*H)+Ka,s.zeros(252))
            equal(s.I*W,inverse*(Ka-s.I*Ea*H))
            ports[field_index]=W
        return {'primal_generator':clean(-s.I*H),'dual_right_generator':clean(s.I*H),
                'Hamiltonian':H,'source_current_matrices':{i:-W for i,W in ports.items()},
                'principal':data['E']}

    def primitive_tangent(self, data, field_index, momentum):
        entry=self.active['fields'][field_index]
        group,coord=entry['group'],entry['coordinate']
        Ea=s.zeros(252)
        if group=='gauge_A': Ka=clean(data['contracted'][coord[0]]*self.rho[coord[1]])
        elif group=='Lorentz': Ka=clean(data['contracted'][coord[0]]*self.spin[coord[1]])
        elif group=='scalar_J': Ka=clean(data['volume']*self.vertices[field_index]/self.N)
        elif group=='coframe':
            t=s.Symbol('t',real=True)
            shifted=data['coframe'].copy();shifted[tuple(coord)]+=t
            da=clean(shifted.adjugate(method='berkowitz').diff(t).subs(t,0))
            dv=s.diff(shifted.det(method='berkowitz'),t).subs(t,0)
            deriv=[clean(sum((da[mu,a]*s.I*self.Gamma[a] for a in range(4)),s.zeros(252))) for mu in range(4)]
            Ea=deriv[0]
            Ka=clean(sum((deriv[mu]*data['connections'][mu] for mu in range(4)),s.zeros(252))+
                     sum((deriv[j+1]*(s.I*momentum[j]) for j in range(3)),s.zeros(252))+
                     sum((da[0,a]*self.omega*self.Gamma[a]*self.Q for a in range(4)),s.zeros(252))+dv*data['Y'])
        else: raise AssertionError(group)
        return clean(Ea),clean(Ka)


def main():
    started=time.monotonic()
    native=NativeMatterReaction()
    current=json.loads((HERE/'dynamic.json').read_text())
    assert current['root']==ROOT_ID
    assert current['source_sha256']==native.source.vertices['source_sha256']
    sample=next(x for x in current['samples'] if x['name']=='energy_transfer')
    response=decode(sample['response']['field289'])
    # The response solves H Y=j; the stationary field in S2+b*j is b=-Y.
    # Its real Fourier coefficient is an actual real field direction.  The
    # phase and amplitude here come from the source response, not a coupling.
    field=clean(-response.applyfunc(s.re))
    assert field.todok()
    momentum=s.sqrt(2)*s.Matrix(list(map(s.sympify,sample['scaled_momenta'][0])))
    original=native.densitized(s.zeros(289,1),momentum)
    p=list(s.symbols('p0:4'))
    original_symbol=native.source.D.subs(dict(zip(p,[0,*[s.I*v for v in momentum]])))
    equal(original['E'],native.N*native.C[0])
    equal(original['K'],native.N*original_symbol)
    H0,E0inv=native.temporal(original)
    print('PASS full252 original adjugate/volume/connection action',flush=True)
    live=native.densitized(field,momentum)
    assert live['volume']!=0 and live['E4'].det()!=0
    H1,E1inv=native.temporal(live)
    print('PASS actual four-block field returned to full252 finite matter action',flush=True)
    difference=clean(H1-H0)
    assert difference.todok()
    occupied=json.loads((BASE/'occupied-response/receipt.json').read_text())
    assert occupied['source_sha256']==native.source.vertices['source_sha256']
    prepared=clean(decode(occupied['occupied_frame'])*decode(occupied['source_prepared']))
    equal(prepared.H*prepared,s.ones(1))
    psi=2*prepared
    chi=clean(2*s.sqrt(2)*prepared.H*native.source.S)
    p0=clean(-s.I*chi*original['E'])
    p1=clean(-s.I*chi*live['E'])
    equal(psi.H*psi,4*s.ones(1))
    assert scalar((chi*native.source.S*psi)[0]-4*s.sqrt(2))==0
    background_momentum=s.zeros(3,1)
    background_original=native.densitized(s.zeros(289,1),background_momentum)
    background_live=native.densitized(field,background_momentum)
    H0_background,_=native.temporal(background_original)
    H1_background,_=native.temporal(background_live)
    equal(H0_background*psi,s.zeros(252,1))
    background_difference=clean(H1_background-H0_background)
    actual_reaction=clean(background_difference*psi)
    assert actual_reaction.todok()
    tangent_sum=s.zeros(252)
    feedback=[]
    actual_feedback=[]
    phase_p=dict(zip(p,[0,*[s.I*v for v in momentum]]))
    for field_index in native.source.order:
        Ea,Ka=native.primitive_tangent(original,field_index,momentum)
        original_vertex=native.vertices[field_index]
        equal(Ea,original_vertex.diff(p[0]))
        equal(Ka,original_vertex.subs(phase_p))
        W0=clean(-E0inv*Ea*H0-s.I*E0inv*Ka)
        equal(original['E']*(-s.I*W0)+Ea*(-s.I*H0)+Ka,s.zeros(252))
        tangent_sum+=field[field_index]*W0
        # Independent primal/dual canonical variables have opposite flows;
        # i[H,W] is the exact derivative of pi*W*xi at this finite field.
        # Gauge currents suffice to expose a real reaction, without replacing
        # the complete97-field action by that test.
        Eb,Kb=native.primitive_tangent(live,field_index,momentum)
        W1=clean(-E1inv*Eb*H1-s.I*E1inv*Kb)
        equal(live['E']*(-s.I*W1)+Eb*(-s.I*H1)+Kb,s.zeros(252))
        equal(s.I*W1,E1inv*(Kb-s.I*Eb*H1))
        E0a,K0a=native.primitive_tangent(background_original,field_index,background_momentum)
        E1a,K1a=native.primitive_tangent(background_live,field_index,background_momentum)
        W0_background=clean(-E0inv*E0a*H0_background-s.I*E0inv*K0a)
        W1_background=clean(-E1inv*E1a*H1_background-s.I*E1inv*K1a)
        original_current=scalar((-p0*W0_background*psi)[0])
        live_current=scalar((-p1*W1_background*psi)[0])
        equal(-p1*W1_background*psi,chi*(E1a*(-s.I*H1_background)+K1a)*psi)
        derivative_change=scalar((-s.I*p1*(background_difference*W1_background-W1_background*background_difference)*psi)[0])
        current_change=scalar(live_current-original_current)
        if s.re(current_change)!=0 or s.re(derivative_change)!=0:
            actual_feedback.append({'field':field_index,'group':native.active['fields'][field_index]['group'],
                'coordinate':native.active['fields'][field_index]['coordinate'],
                'original_action_current':str(original_current),'finite_action_current':str(live_current),
                'real_current_change':str(s.re(current_change)),
                'real_matter_flow_derivative_change':str(s.re(derivative_change))})
        if native.active['fields'][field_index]['group']=='gauge_A':
            change=clean(s.I*(difference*W1-W1*difference))
            if change.todok():
                key,value=next(iter(sorted(change.todok().items())))
                feedback.append({'field':field_index,'coordinate':native.active['fields'][field_index]['coordinate'],
                                 'nonzero_entries':len(change.todok()),'first_entry':[key[0],key[1],str(value)]})
    nonlinear=clean(difference-tangent_sum)
    assert nonlinear.todok() and feedback and actual_feedback
    print('PASS all97 original tangents; genuine finite coframe reaction and changed canonical currents',flush=True)
    paths=[HERE/'dynamic.json',BASE/'full-phase/receipt.json',BASE/'matter-vertices/receipt.json',BASE/'active-gauge/receipt.json',BASE/'occupied-response/receipt.json']
    output={'root':ROOT_ID,'source_sha256':native.source.vertices['source_sha256'],
        'scope':'ACTUAL_FOUR_BLOCK_FIELD_TO_FINITE_NATIVE_FULL252_MATTER_REACTION',
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'source_response_sample':'energy_transfer; real Fourier coefficient; physical b=-Re(Y)',
        'source_field':encode(field),'physical_momentum':encode(momentum),
        'action':'Re[zeta*(sum adj(e)[mu,a]*i Gamma[a]*(d_mu+Omega_mu)+sum adj(e)[0,a]*omega Gamma[a]*Q+det(e)*Y)*xi]',
        'canonical_variables':'pi_action=zeta*E(e); p_CAR=-i*pi_action; xi_dot=-i H xi; pi_action_dot=i pi_action H',
        'source_current_conventions':'j_a=i*pi_action*W_a*xi=-p_CAR*W_a*xi; real part supplies the real source; pi_action alone is not unit-CAR normalized',
        'current_feedback_convention':'at fixed finite field, the tabulated i[H_live-H0,W_live] is the matter-flow derivative change of pi_action W_live xi; the action source adds its explicit factor i; spacetime evolution also retains partial_t W and spatial-flux terms',
        'full252_hamiltonian':'H=-i E(e)^-1 K(e,A,Omega,phi,k)',
        'coframe':encode(live['coframe']),'volume':str(live['volume']),
        'temporal_principal4':encode(live['E4']),'temporal_principal4_determinant':str(scalar(live['E4'].det())),
        'finite_hamiltonian':encode(H1),'finite_reaction':encode(difference),
        'nonlinear_beyond_linear_tangent_nonzero_entries':len(nonlinear.todok()),
        'original97_action_tangents_recovered':True,'finite97_canonical_action_current_identities':True,'full252_temporal_equation_exact':True,
        'canonical_current_feedback_nonzero_fields':len(feedback),'canonical_current_feedback':feedback,
        'actual_prepared_consumer':{'prepared_unit':encode(prepared),'psi':encode(psi),'chi':encode(chi),
            'source_bilinear_amplitude':'4*sqrt(2)','physical_momentum':[0,0,0],'original_stationary_source_H0_psi_zero':True,'reaction_on_actual_psi':encode(actual_reaction),
            'nonzero_reaction_entries':len(actual_reaction.todok()),'nonzero_real_current_feedback_fields':len(actual_feedback),
            'current_feedback':actual_feedback},
        'returned_to_source':'Feed the evolved independent primal/dual canonical current into the same constrained four-block retarded response; the current is no longer its prescribed free216 time orbit.',
        'native_feedback_API':'NativeMatterReaction.canonical_ports(field289,k) returns full252 primal/dual generators and all97 canonical source-current matrices; no caller coupling or self-energy',
        'tree_retarded_feedback_equations':['for each frozen local symbol: xi_dot=-i H(b,k) xi','for the same frozen local symbol: p_CAR_dot=i p_CAR H(b,k)','j_a=Re[-p_CAR W_a(b) xi]','physical field b=-G_ret*prepared(j), with existing Ward initial completion and all derivative contacts retained'],
        'feedback_equation_scope':'Native finite-field matter reaction coupled to the existing quadratic four-block bosonic response; the simultaneous constrained evolution and its quantum spectral realization are downstream producers.',
        'source_field_readback_scope':'The generated real Fourier coefficient gives a finite local source configuration; this is one reaction step, not a solved global selfconsistent spacetime solution.',
        'spectral_consumer':'The current-driven K(z) is a tree response readout. Native reaction replaces the prescribed-free-current loop before an interacting spectral generator can be asserted.',
        'full_interacting_generator':'SOURCE_NATIVE_SELFCONSISTENT_CURRENT_FIELD_EVOLUTION_REQUIRED',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'spectral_splice.json').write_text(json.dumps(output,separators=(',',':'))+'\n')
    print('PASS source-current -> four-block field -> exact finite full252 reaction -> nonzero current feedback',flush=True)


if __name__=='__main__':
    main()
