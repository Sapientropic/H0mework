#!/usr/bin/env python3
"""Original canonical time constraint derivative and its Schur Hessian.

The carrier consists of original canonical field and momentum variations,
not the thirteen compressed invariant arguments. This is a classical source
phase derivative; no interacting quantum spectrum is inferred from it.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_spatial_active_phase_splice import SpatialActiveSplice, dm, mul, DOMAIN, field_element
from source_full_linear_split import decode, P, K, coefficients
from source_coframe_live_ordering import FREE, DEPENDENT
from source_stabilizer_phase_reduction import canonical_J
from source_lorentz_contact import clean, equal, encode
from retained_hamiltonian_reduction import null, identity
from source_common_retarded_phase import load_common_fiber, read_bound
from source_forced_hamiltonian_reduction import poly, Z, POLY as ZPOLY


def zero(A):
    if isinstance(A, DM): assert A.is_zero_matrix
    else: equal(clean(A), s.zeros(*A.shape))


POLY = DOMAIN.poly_ring(*K)


def pdm(matrix):
    if isinstance(matrix, DM): return matrix.convert_to(POLY)
    rows = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        element = POLY.zero
        for powers, coefficient in s.Poly(s.expand(value), *K).terms():
            term = POLY.convert(field_element(coefficient), DOMAIN)
            for variable, power in zip(POLY.gens, powers): term *= variable**power
            element += term
        if element: rows.setdefault(i, {})[j] = element
    return DM(rows, matrix.shape, POLY).to_sparse()


def adjoint(A):
    convert = pdm if A.domain == POLY else dm
    return convert(A.to_Matrix().conjugate().T)


def evaluate(A, momentum):
    return dm(A.to_Matrix().subs(dict(zip(K, momentum))))


def selector(indices, columns):
    return s.SparseMatrix(len(indices), columns, {(i, j): 1 for i, j in enumerate(indices)})


class SourceCanonicalTemporalHessian:
    def __init__(self):
        self.source = SpatialActiveSplice()
        self.record = self.source.retained
        self.fields = self.record['retained_fields']
        self.field_index = {(row['group'], tuple(row['coordinate'])): j for j, row in enumerate(self.fields)}
        self.time_rows = [self.field_index['coframe', (a, 0)] for a in range(4)]
        self.A0_rows = [self.field_index['gauge_A', (0, a)] for a in range(12)]
        self.scalar_rows = [self.field_index['scalar_J', (a,)] for a in range(9)]
        self.Lorentz_rows = [self.field_index['coframe', (j//4, j%4)] for j in DEPENDENT]

    def canonical_field_reader(self):
        """Original BF, gauge and independent-dual momenta before time removal."""
        m = self.source; index = m.index
        lift = s.eye(289)
        e = s.Matrix.vstack(*(lift[index['coframe', (a, mu)], :] for a in range(4) for mu in range(4)))
        omega = s.Matrix.vstack(*(lift[index['Lorentz', (mu, a)], :] for mu in range(4) for a in range(6)))
        A = s.Matrix.vstack(*(lift[index['gauge_A', (mu, a)], :] for mu in range(4) for a in range(12)))
        matter = lambda name: s.Matrix.vstack(*(lift[index[name, (im, spin, color)], :]
            for im in range(2) for spin in range(4) for color in range(3)))
        Pi_e = clean(m.Gt.T*omega+m.dGt_omega*e)
        Bmag = s.Matrix.vstack(*(lift[index['gauge_B', (pair, a)], :] for pair in range(3, 6) for a in range(12)))
        Pi_A = clean(s.kronecker_product(s.eye(3), m.c.gauge.gram)*Bmag)
        O = m.current_real_frame
        Pi_m = clean(O.T*(m.p_from_chi*O*matter('dual_H')+m.p_from_e*e))
        q = e[list(FREE), :].col_join(A[12:, :]).col_join(matter('primal_H'))
        momentum_map = Pi_e[list(FREE), :].col_join(Pi_A).col_join(Pi_m)
        return clean(q.col_join(momentum_map))

    def canonical_reader_matrix(self, momentum):
        lift = clean(self.source.lift.subs(dict(zip(P[1:], [s.I*k for k in momentum]))))
        reader = clean(self.canonical_field_reader()*lift)
        matrices = [reader.applyfunc(lambda v: s.expand(v).coeff(P[0], j)) for j in (0, 1)]
        zero(reader-matrices[0]-P[0]*matrices[1])
        return clean(matrices[0].row_join(matrices[1]))

    def canonical_reader(self, momentum):
        return dm(self.canonical_reader_matrix(momentum))

    def all_momenta(self):
        m = self.source
        section = dm(m.old_matrix('velocity_quotient_section', 1))
        retraction = dm(m.old_matrix('velocity_quotient_retraction', 1))
        omega242 = pdm(decode(self.record['presymplectic_form']))
        energy242 = pdm(decode(self.record['Legendre_energy_hessian']))
        radical = pdm(identity(242)-section*retraction)
        zero(omega242*radical); zero(energy242*radical)
        sectionP = pdm(section)
        Omega = adjoint(sectionP)*omega242*sectionP
        E = adjoint(sectionP)*energy242*sectionP
        z = pdm(self.canonical_reader_matrix(K))*sectionP
        y = pdm(selector(self.time_rows, 242))*sectionP
        A0 = pdm(selector(self.A0_rows, 242))*sectionP
        fixed_rows = self.scalar_rows+[121+j for j in self.scalar_rows]+self.Lorentz_rows
        fixed = dm(selector(fixed_rows, 242))*section
        chart = null(fixed); assert chart.shape == (172, 148)
        coordinates = DM.vstack(z, y, A0)*pdm(chart)
        C0 = evaluate(coordinates, (0, 0, 0)); C0i = pdm(C0.inv())
        shear = C0i*(coordinates-pdm(C0))
        zero(shear*shear)
        inverse = (pdm(identity(148))-shear)*C0i
        zero(coordinates*inverse-pdm(identity(148)))
        zero(inverse*coordinates-pdm(identity(148)))
        embedding = pdm(chart)*inverse
        zero(DM.vstack(z, y, A0)*embedding-pdm(identity(148)))
        zero(pdm(fixed)*embedding)
        zero(adjoint(embedding)*Omega*embedding-pdm(s.diag(-canonical_J(66), s.zeros(16))))
        energy = adjoint(embedding)*E*embedding
        zero(energy-adjoint(energy))
        print('PASS all-three-k original canonical132/time4/A0-12 map and source nilpotent shear inverse', flush=True)
        W = m.c.graph.select.row_join(m.c.graph.stabilizer)
        basis = pdm(s.diag(s.eye(136), W))
        energy = adjoint(basis)*energy*basis
        bb = energy.extract(range(136, 145), range(136, 145))
        bb0 = evaluate(bb, (0, 0, 0)); zero(bb-pdm(bb0))
        keep = [*range(136), *range(145, 148)]
        bR = energy.extract(range(136, 145), keep)
        b_graph = -pdm(bb0.inv())*bR
        scalar_embedding = s.zeros(148, 139)
        for j, row in enumerate(keep): scalar_embedding[row, j] = 1
        scalar_embedding[136:145, :] = b_graph.to_Matrix()
        scalar_embedding = pdm(scalar_embedding)
        zero(energy.extract(range(136, 145), range(148))*scalar_embedding)
        reduced = adjoint(scalar_embedding)*energy*scalar_embedding
        zero(reduced-adjoint(reduced))
        zero(reduced.extract(range(136, 139), range(132, 139)))
        H = reduced.extract(range(136), range(136))
        Hyy = H.extract(range(132, 136), range(132, 136))
        Hyy0 = evaluate(Hyy, (0, 0, 0)); zero(Hyy-pdm(Hyy0))
        Hyz = H.extract(range(132, 136), range(132))
        Hzz = H.extract(range(132), range(132))
        yz = -pdm(Hyy0.inv())*Hyz
        schur = Hzz-adjoint(Hyz)*pdm(Hyy0.inv())*Hyz
        zero(Hyy*yz+Hyz); zero(schur-adjoint(schur))
        print('PASS all-three-k source time Jacobian, complete4x132 derivative and132x132 canonical Schur Hessian', flush=True)
        return {'canonical_embedding': embedding, 'canonical_with_A0_energy': energy, 'H': H, 'Hyy': Hyy, 'Hyz': Hyz,
            'Hzz': Hzz, 'y_z': yz, 'Schur': schur, 'A0_basis': basis,
            'scalar_embedding': scalar_embedding, 'broken_A0_block': bb,
            'source_shear': shear, 'reduced_with_stabilizer': reduced,
            'descriptor_section': sectionP, 'Gauss': reduced.extract(range(136, 139), range(132))}


    def complete_canonical_carrier(self):
        m = self.source; O = m.current_real_frame
        E = s.zeros(1214, 132)
        for i in range(6): E[i, i] = 1; E[607+i, 66+i] = 1
        for i in range(36): E[67+i, 6+i] = 1; E[607+67+i, 66+6+i] = 1
        E[103:607, 42:66] = O; E[607+103:1214, 66+42:132] = O
        Xtail = dm(m.tail); E = dm(E); Ractive = adjoint(E)
        Rtail = -dm(m.tail_omega_inverse)*adjoint(Xtail)*dm(m.c.J)
        X, R = DM.hstack(E, Xtail), DM.vstack(Ractive, Rtail)
        zero(R*X-identity(1214)); zero(X*R-identity(1214))
        zero(-adjoint(X)*dm(m.c.J)*X-dm(s.diag(-canonical_J(66), m.tail_omega)))
        # Direct sparse source vertices, before momentum substitution, prove
        # that the whole original temporal constraint has no tail column.
        split = m.split; checked = 0
        for row, V in zip(split.vertices['primitive_vertices'], split.V):
            if row['group'] == 'coframe' and row['coordinate'][1] == 0:
                for coefficient in coefficients(V):
                    zero(split.C.H*coefficient*split.psi0)
                    zero(split.chi0*coefficient*split.C)
                    checked += 1
            if row['group'] == 'scalar': zero(split.chi0*V*split.psi0)
        for mu in range(4):
            T = clean(sum((split.A[mu, a]*split.common.scalar.rho[a] for a in range(12)), s.zeros(70)))
            zero(T*split.common.scalar.vacuum)
        zero(Ractive*Xtail)
        assert checked == 20
        return dict(active_embedding=E, active_reader=Ractive, tail_embedding=Xtail,
                    tail_reader=Rtail, source_time_vertex_coefficients=checked)

    def response_consumer(self, result, carrier, sign):
        fiber = load_common_fiber(sign); k = fiber['k']; m = self.source
        H = evaluate(result['Schur'], k); y_z = evaluate(result['y_z'], k)
        X = dm(fiber['X']); Xa = X.extract(range(1214), range(126))
        active = carrier['active_reader']*Xa
        zero(carrier['active_embedding']*active-Xa)
        omega = -adjoint(active)*dm(canonical_J(66))*active
        zero(omega-dm(fiber['Omega_split']).extract(range(126), range(126)))
        physical = adjoint(active)*H*active
        zero(physical-dm(fiber['active_H']))
        original = json.loads((HERE/'source_spatial_active_phase_splice.json').read_text())['fibers'][0 if sign == 1 else 1]
        field = dm(decode(original['original289_field_map']))*dm(m.old_matrix('quotient_section', sign))
        time_rows = [m.index['coframe', (a, 0)] for a in range(4)]
        true_time = field.extract(time_rows, range(126))
        zero(y_z*active-true_time)
        whole_H = dm(s.diag(physical.to_Matrix(), fiber['tail_H']))
        whole_Omega = dm(fiber['Omega_split'])
        whole_A = dm(fiber['A_split'])
        zero(whole_Omega*whole_A-whole_H)
        # The old whole response now consumes the new original canonical
        # Schur energy, including every tail coefficient and scalar-dual cross.
        R = dm(fiber['R']); J = dm(fiber['J'])
        ambient_H = adjoint(R)*whole_H*R
        zero(J*ambient_H*X-X*whole_A)
        assert y_z.nnz() and true_time.nnz()
        print('PASS actual126+1082 full original energy, time-graph derivative and common generator', sign, flush=True)
        return {'momentum': list(map(str, k)), 'active_canonical132_embedding': encode(active.to_Matrix()),
                'source_time_graph_on_active126': encode(true_time.to_Matrix()),
                'complete1208_energy_and_generator_equal': True,
                'whole_source_time_graph_tail_zero': True}, fiber, active


    def original_affine_source(self, k, sign, j, frequency):
        """Source polynomial division before consuming any Green response."""
        m = self.source
        saved = read_bound('source_forced_hamiltonian_reduction.json')['source_momenta'][0 if sign == 1 else 1]
        source = poly(j)
        force_poly = poly(decode(saved['physical_forcing']))*source
        field_lift = poly(decode(saved['full289_field_lift']))
        field_particular = poly(decode(saved['full289_field_particular']))*source
        section = poly(m.native_slice_reader(k))
        ward = poly(m.ward.subs(dict(zip(P,[Z,*[s.I*v for v in k]]))))
        minor = (section*ward).convert_to(DOMAIN)
        fixed = lambda value: value-ward*poly(minor.inv())*section*value
        field_lift, field_particular = fixed(field_lift), fixed(field_particular)
        Q = poly(self.canonical_field_reader())*field_lift
        matrix = Q.to_Matrix()
        degree = max((s.degree(v,Z) for v in matrix.todok().values()),default=0)
        coefficients = [dm(matrix.applyfunc(lambda v:s.expand(v).coeff(Z,n))) for n in range(degree+1)]
        A = dm(m.old_matrix('Hamiltonian_generator',sign)); remainder = coefficients[-1]
        quotient = DM.zeros(Q.shape,ZPOLY)
        for n in range(len(coefficients)-2,-1,-1):
            quotient = quotient.scalarmul(ZPOLY.gens[0])+poly(remainder)
            remainder = coefficients[n]+remainder*A
        generator = poly(identity(126)).scalarmul(ZPOLY.gens[0])-poly(A)
        zero(Q-poly(remainder)-quotient*generator)
        affine = poly(self.canonical_field_reader())*field_particular+quotient*force_poly
        at = lambda value:dm(value.to_Matrix().subs(Z,frequency))
        return at(affine), at(force_poly), remainder


    def onshell_consumer(self, result, carrier, sign, nonzero_frequency=False):
        name = 'source_nonzero_frequency_onshell_response.json' if nonzero_frequency else 'source_onshell_phase_forcing.json'
        record = read_bound(name)
        slot = 0 if sign == 1 else 1
        source = record['currents'][slot]
        saved = record['consumers' if nonzero_frequency else 'common_phase_consumers'][slot]
        frequency = s.sympify(saved['actual_time_frequency']) if nonzero_frequency else s.S.Zero
        j = dm(decode(source['factored_current289' if nonzero_frequency else 'scaled_current289']))
        source_factor = s.sympify(source['physical_current_factor'])
        k = tuple(map(s.sympify, saved['momentum'])); m = self.source
        at = dict(zip(P, [frequency, *[s.I*v for v in k]]))
        field = dm(decode(saved['factored_full289_response' if nonzero_frequency else 'factored_full289_source_response']))
        force = dm(decode(saved['factored_source_forcing126' if nonzero_frequency else 'factored_physical_forcing126']))
        response = dm(decode(saved['factored_source_response126' if nonzero_frequency else 'factored_physical_response126']))
        affine132, actual_force, canonical_embedding126 = self.original_affine_source(k,sign,j,frequency)
        zero(actual_force-force)
        affine = carrier['active_embedding']*affine132
        phase = carrier['active_embedding']*(canonical_embedding126*response+affine132)
        if nonzero_frequency:
            for key, value in [('factored_affine_phase1214',affine),('factored_common_phase1214_response',phase)]:
                old = saved[key]
                assert old['complete_vector_dimension'] == 1214
                zero(value.extract(old['source_rows'],[0])-dm(decode(old['values'])))
        else:
            zero(affine-dm(decode(saved['factored_affine_phase_polynomial']).subs(Z,frequency)))
            zero(phase-dm(decode(saved['factored_full_source_phase'])))
        source_readback = dm(decode(self.record['retained_source_readback']).subs(at))
        section = evaluate(result['descriptor_section'], k)
        descriptor_source = adjoint(section)*DM.vstack(source_readback*j, DM.zeros((121, 1), DOMAIN))
        embedding = evaluate(result['canonical_embedding'], k)
        basis = evaluate(result['A0_basis'], k)
        s148 = adjoint(basis)*adjoint(embedding)*descriptor_source
        scalar_embedding = evaluate(result['scalar_embedding'], k)
        s139 = adjoint(scalar_embedding)*s148
        # The actual canonical BF/matter momentum includes the original
        # auxiliary contact source. It is removed only for coordinates of
        # the homogeneous Legendre chart, then restored in every response.
        reader = dm(self.canonical_field_reader())
        contact = dm(decode(self.record['auxiliary_only_contact']).subs(at))
        contact_z = reader*contact*j
        actual_z = carrier['active_reader']*phase
        zero(actual_z-reader*field)
        z0 = actual_z-contact_z
        time_rows = [m.index['coframe', (a, 0)] for a in range(4)]
        A0_rows = [m.index['gauge_A', (0, a)] for a in range(12)]
        actual_y = field.extract(time_rows, [0])
        W = dm(m.c.graph.select.row_join(m.c.graph.stabilizer))
        actual_A0 = W.inv()*field.extract(A0_rows, [0])
        u148 = DM.vstack(z0, actual_y, actual_A0)
        E148 = evaluate(result['canonical_with_A0_energy'], k)
        Omega148 = dm(s.diag(-canonical_J(66), s.zeros(16)))
        zero((Omega148.scalarmul(field_element(frequency))-E148)*u148-s148)
        reduced = evaluate(result['reduced_with_stabilizer'], k)
        u139 = DM.vstack(z0, actual_y, actual_A0.extract(range(9,12),[0]))
        Omega139 = dm(s.diag(-canonical_J(66),s.zeros(7)))
        zero((Omega139.scalarmul(field_element(frequency))-reduced)*u139-s139)
        yy = evaluate(result['Hyy'], k); yz = evaluate(result['Hyz'], k)
        y_graph = evaluate(result['y_z'], k)
        temporal_source = s139.extract(range(132,136), [0])
        particular_y = -y_graph*contact_z-yy.inv()*temporal_source
        zero(actual_y-y_graph*actual_z-particular_y)
        H = evaluate(result['Schur'], k); Omega = dm(-canonical_J(66))
        effective_source = s139.extract(range(132), [0])-adjoint(yz)*yy.inv()*temporal_source
        native_descriptor = Omega.scalarmul(field_element(frequency))-H
        gauss = evaluate(result['Gauss'], k)
        stable_A0 = actual_A0.extract(range(9,12),[0])
        zero(native_descriptor*z0-adjoint(gauss)*stable_A0-effective_source)
        fiber = load_common_fiber(sign)
        active = carrier['active_reader']*dm(fiber['X']).extract(range(1214),range(126))
        affine_z = carrier['active_reader']*affine
        zero(active*response+affine_z-actual_z)
        projected_source = adjoint(active)*(effective_source-native_descriptor*(affine_z-contact_z))
        physical_Omega = dm(fiber['Omega_split']).extract(range(126),range(126))
        zero(projected_source-physical_Omega*force)
        zero((physical_Omega.scalarmul(field_element(frequency))-adjoint(active)*H*active)*response-projected_source)
        # Re-evaluate the unaltered original full12 Gauss consumer. Its source
        # need not vanish and its broken normal momentum is not discarded.
        whole = phase.to_Matrix(); actual_field = field.to_Matrix()
        phi = clean(m.split.J*actual_field[:m.split.J.cols,:])
        A0native = actual_field[A0_rows,:]
        actual_Piphi = clean(-(frequency*phi+m.split.orbit*A0native)/m.split.N)
        predicted_Piphi = m.model.broken_scalar_momentum(k,whole)
        normal_source = clean(actual_Piphi-predicted_Piphi)
        full_Gauss = clean(m.model.full_Gauss(k,whole)+m.split.orbit.T*normal_source)
        expected_Gauss = j.to_Matrix()[A0_rows,:]
        zero(full_Gauss-expected_Gauss); assert full_Gauss.todok()
        print('PASS actual onshell current through both Schur covectors, original source time graph and full12 Gauss',
              sign, frequency, flush=True)
        return {'momentum':list(map(str,k)), 'frequency':str(frequency), 'physical_source_factor':str(source_factor),
            'source_time_covector':encode(temporal_source.to_Matrix()),
            'original_auxiliary_canonical_offset':encode(contact_z.to_Matrix()),
            'generated_affine_time_response':encode(particular_y.to_Matrix()),
            'actual_full_time_response':encode(actual_y.to_Matrix()),
            'full132_dynamic_equations_and_all4_time_equations':True,
            'original126_forcing_from_Schur_covector':encode(projected_source.to_Matrix()),
            'full12_original_Gauss_equals_actual_A0_current':encode(full_Gauss),
            'normal_scalar_source_preserved':encode(normal_source),
            'Contact_added_once_before_canonical_readback':True}


def main():
    started = time.monotonic()
    paid = (
        'retained_matter_action', 'independent_retained_matter_action',
        'retained_hamiltonian_reduction', 'independent_retained_hamiltonian_reduction',
        'source_temporal_dirac_reduction', 'independent_source_temporal_dirac_reduction',
        'source_spatial_phase_tangent', 'independent_source_spatial_phase_tangent',
        'source_physical_phase_splice', 'independent_source_physical_phase_splice',
        'source_spatial_active_phase_splice', 'independent_source_spatial_active_phase_splice',
        'source_full_linear_split', 'independent_source_full_linear_split',
        'source_common_phase_time', 'independent_source_common_phase_time',
        'source_onshell_phase_forcing', 'independent_source_onshell_phase_forcing',
        'source_nonzero_frequency_onshell_response', 'independent_source_onshell_time_response',
        'source_forced_hamiltonian_reduction')
    records = {name:read_bound(name+'.json') for name in paid}
    model = SourceCanonicalTemporalHessian()
    result = model.all_momenta()
    zero(evaluate(result['Hyy'],(0,0,0))+dm(decode(records['source_temporal_dirac_reduction']['source_J'])))
    for name in ('H', 'Hyy', 'Hyz', 'Hzz', 'y_z', 'Schur', 'Gauss'):
        value = result[name].to_Matrix()
        zero(pdm(value.subs(dict(zip(K,[-v for v in K])),simultaneous=True))-pdm(value.conjugate()))
    carrier = model.complete_canonical_carrier()
    fibers = [model.response_consumer(result,carrier,sign)[0] for sign in (1,-1)]
    sources = [model.onshell_consumer(result,carrier,sign,shifted)
               for shifted in (False,True) for sign in (1,-1)]
    paths = [HERE/(name+'.json') for name in paid]+[HERE/name for name in (
        'source_canonical_temporal_hessian.py', 'source_spatial_active_phase_splice.py',
        'source_full_linear_split.py', 'source_coframe_live_ordering.py',
        'source_stabilizer_phase_reduction.py', 'source_common_retarded_phase.py',
        'source_forced_hamiltonian_reduction.py', 'source_quantum_temporal_symbol.py')]
    paths += [BASE/name for name in ('active-gauge/receipt.json', 'matter-vertices/receipt.json',
                                   'occupied-response/receipt.json')]
    public = ('canonical_embedding','canonical_with_A0_energy','A0_basis','scalar_embedding',
              'broken_A0_block','H','Hyy','Hyz','Hzz','y_z','Schur','Gauss','source_shear')
    matrices = {name:encode(result[name].to_Matrix()) for name in public}
    out = {'root':ROOT_ID,
        'scope':'ALL_SPATIAL_MOMENTA_ORIGINAL_CANONICAL_TIME_SCHUR_HESSIAN_AND_ACTUAL_FULL_PHASE_SOURCE_RESPONSE',
        'source_sha256':model.source.split.vertices['source_sha256'],
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'carrier':{'retained_fields':121,'original_velocity_quotient':172,
            'fixed_scalar9_velocity9_and_Lorentz6':24,
            'unreduced_canonical132_time4_A0native12':148,
            'broken_A0_directions':9,'residual_Gauss_multipliers':3,
            'original_canonical_pairs_before_residual_Gauss':607,
            'active_phase_before_residual_Gauss':132,'tail':1082,
            'physical_phase_after_residual_Gauss':1208,
            'active_coordinates':'q=(coframe6, gauge36, occupied_primal_real24); P=(original Pi_e6, Pi_A36, occupied independent-dual real24). The full original tail supplies scalar61 pairs and both matter complements.',
            'scalar_compressed13_used_as_canonical_coordinates':False},
        'all_k_construction':{'variables':list(map(str,K)),
            'original_velocity_radical_annihilated_by_full_phase_and_energy':True,
            'original_field_reader132_by289':encode(model.canonical_field_reader()),
            'source_coordinate_shear_square_zero':True,
            'inverse_formula':'C(k)=C(0)*(I+S(k)), S(k)^2=0; C(k)^-1=(I-S(k))*C(0)^-1. The only inverse is generated from the actual original C(0), not an assumed chart normalizer.',
            'original_phase_identity':'B(-k)^T Omega172(k) B(k)=diag(-J66,0_16)',
            'same_original_BF_boundary_and_delta_chi_E_plus_chi_deltaE':True,
            'opposite_k_conjugacy_and_Hermitian_phase_energy_checked':True},
        'all_k_matrices':matrices,
        'temporal_derivative':{'original_constraint':'F=-partial_y H, at fixed original canonical coordinates and the same broken-Gauss graph.',
            'source_Jacobian':'F_y=-Hyy=J0; Hyy=diag(sqrt30,2sqrt30/3,2sqrt30/3,2sqrt30/3) for all real k.',
            'branch_derivative':'y_z=-Hyy^-1 Hyz, and Hyy*y_z+Hyz=0 in every one of the4x132 entries.',
            'reduced_Hessian':'Hred_zz=Hzz-Hzy Hyy^-1 Hyz, with Hzy(k)=Hyz(-k)^T.',
            'generic_Hyz_nonzero_entries':result['Hyz'].nnz(),
            'generic_Schur_nonzero_entries':result['Schur'].nnz(),
            'actual_canonical_graph_not_single_epsilon_curve':True},
        'whole_canonical_carrier':{
            'active_embedding1214':encode(carrier['active_embedding'].to_Matrix()),
            'active_reader132':encode(carrier['active_reader'].to_Matrix()),
            'tail_embedding1214':encode(carrier['tail_embedding'].to_Matrix()),
            'tail_reader1082':encode(carrier['tail_reader'].to_Matrix()),
            'both1214_inverses_and_full_phase_identity':True,
            'original_time_vertex_coefficients_checked':carrier['source_time_vertex_coefficients'],
            'tail_decoupling':'All4 time-coframe original vertices have zero occupied/complement transitions for each constant and four momentum coefficients. All70 source scalar bilinears vanish and every background covariant scalar derivative vanishes. These actual sparse identities give H_y_tail=0; no dimension-based zero block is installed.',
            'complete_Hessian_formula':'On all1214 canonical fields, Hzz_full=Ractive^* Hzz Ractive+Rtail^* Htail_original Rtail; Hyz_full=Hyz Ractive. The original tail keeps its complete scalar-dual cross and co-rotating source phase energy. Applying the same temporal Schur replaces only Hzz by Schur.',
            'source_linearization_frame':'The original full1310 Jacobi action along the literal Cauchy source is co-rotated before this tangent calculation. Its original two-endpoint phase and independent-dual momentum map remain those of source_common_phase_time; no stationary spectrum or new source clock is inferred.'},
        'signed_nonzero_physical_consumers':fibers,
        'actual_onshell_consumers':sources,
        'source_covector_elimination':[
            'Start with the unchanged original289 current and its original retained-source readback. Pull its descriptor covector through the actual canonical embedding and native A0 basis.',
            'The broken9 graph pulls that covector through the same source Schur embedding; no completed response determines this forcing.',
            'Subtract only the original auxiliary Contact contribution when using homogeneous Legendre coordinates, then restore it. The affine y term is -y_z*z_Contact-Hyy^-1*s_time.',
            'The complete132 dynamic and4 temporal equations, then the original126 physical forcing, consume the same covector. All12 original Gauss rows equal the actual A0 current and retain the induced normal scalar momentum.'],
        'response_scope':'The canonical phase and Schur Hessian identities are polynomial in all three real spatial momenta. Equality with the previously generated complete1208 physical response and true on-shell current consumers is checked at the two signed nonaxial fibers, including zero and original nonzero transfer frequency.',
        'nonlinear_neighborhood_Hessian_or_quantum_Weyl_spectrum_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_canonical_temporal_hessian.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS source canonical temporal Hessian',out['elapsed_seconds'],'seconds',flush=True)


if __name__ == '__main__': main()
