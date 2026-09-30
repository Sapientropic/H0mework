#!/usr/bin/env python3
"""Exact elimination of the original nonlinear Lorentz auxiliary connection.

The BF and simplicity polynomials below are the untruncated original density.
The old active-gauge quadratic receipt is only a background consumer.  Gravity
uses the oriented top form; the independent-dual matter density uses |det e|.
This produces a reduced action, before the remaining bosonic Legendre map.
"""
from __future__ import annotations

import hashlib
import json
import sys
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode

sys.path.insert(0, str(BASE / 'nonlinear-contact'))
from slice_checks import PAIRS, ETA, J, W as WEDGE, PAIR_SIGN, GAMMA, source_matrices, wedge_matrix


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    residual = clean(left-right)
    assert not residual.todok(), list(residual.todok().items())[:3]


def encode(matrix):
    return {'shape': list(matrix.shape), 'entries': [
        [int(i), int(j), str(v)] for (i, j), v in sorted(clean(matrix).todok().items())]}


def bilinear(left, right):
    return sum(PAIR_SIGN[a]*(left.row(a)*WEDGE*right.row(a).T)[0] for a in range(6))


def gravity_density(e, B, multiplier, curvature):
    """The once-raised BF pairing, original B-star-B, and simplicity term."""
    X = wedge_matrix(e)
    mixed = sum((B.row(a)*WEDGE*curvature.row(a).T)[0] for a in range(6))
    return mixed-bilinear(B, J*B)/2+bilinear(multiplier, B-J*X)


class SourceLorentzContact:
    def __init__(self):
        source_matrices(ROOT)
        self.basis = []
        for a, b in PAIRS:
            matrix = s.zeros(4)
            matrix[a, b], matrix[b, a] = ETA[a, a], -ETA[b, b]
            self.basis.append(matrix)
        self.structure = {}
        for b in range(6):
            for c in range(6):
                bracket = self.basis[b]*self.basis[c]-self.basis[c]*self.basis[b]
                for a, (i, j) in enumerate(PAIRS):
                    value = ETA[i, i]*bracket[i, j]
                    if value:
                        self.structure[a, b, c] = value
        self.spin = [GAMMA[a]*GAMMA[b]/2 for a, b in PAIRS]
        self.flat = self.hessian(s.eye(4))
        self.flat_inverse = clean(self.flat.inv())

    def simplicity(self, e, curvature):
        B = J*wedge_matrix(e)
        multiplier = J*B-s.diag(*PAIR_SIGN)*curvature
        return clean(B), clean(multiplier)

    def curvature_quadratic(self, connection):
        curvature = s.MutableSparseMatrix(6, 6, {})
        for p, (mu, nu) in enumerate(PAIRS):
            for (a, b, c), value in self.structure.items():
                curvature[a, p] += value*connection[6*mu+b]*connection[6*nu+c]
        return clean(curvature)

    def curvature_coefficient(self, e):
        return clean(J*wedge_matrix(e)*WEDGE)

    def hessian(self, e):
        C = self.curvature_coefficient(e)
        matrix = s.MutableSparseMatrix(24, 24, {})
        for p, (mu, nu) in enumerate(PAIRS):
            for (a, b, c), value in self.structure.items():
                coefficient = C[a, p]*value
                matrix[6*mu+b, 6*nu+c] += coefficient
                matrix[6*nu+c, 6*mu+b] += coefficient
        return clean(matrix)

    def inverse_numerator(self, e):
        return clean(s.kronecker_product(e.T, s.eye(6))*self.flat_inverse*
                     s.kronecker_product(e, s.eye(6)))

    def inverse(self, e):
        """Domain: det(e) != 0; no positive-definiteness assumption."""
        return clean(self.inverse_numerator(e)/e.det())

    def geometry_maps(self, e):
        """de index=(rho, internal a, coordinate lambda), in that order."""
        # Differentiate a fresh generic coframe so this API also accepts a
        # numerical or constrained coframe without differentiating constants.
        variables = s.Matrix(4, 4, s.symbols('coframe0:16', real=True))
        C = self.curvature_coefficient(variables)
        change = dict(zip(variables, e))
        G = s.MutableSparseMatrix(24, 64, {})
        for p, (mu, nu) in enumerate(PAIRS):
            for a in range(6):
                for b in range(4):
                    for lam in range(4):
                        value = s.diff(C[a, p], variables[b, lam]).xreplace(change)
                        G[6*nu+a, 16*mu+4*b+lam] -= value
                        G[6*mu+a, 16*nu+4*b+lam] += value
        torsion = s.MutableSparseMatrix(24, 24, {})
        curl = s.MutableSparseMatrix(24, 64, {})
        for b in range(4):
            for p, (mu, nu) in enumerate(PAIRS):
                row = 6*b+p
                curl[row, 16*mu+4*b+nu] += 1
                curl[row, 16*nu+4*b+mu] -= 1
                for a in range(6):
                    torsion[row, 6*mu+a] += (self.basis[a]*e[:, nu])[b]
                    torsion[row, 6*nu+a] -= (self.basis[a]*e[:, mu])[b]
        return clean(G), clean(torsion), clean(curl)

    def raw_matter_ports(self, e):
        """Original density E,V on every invertible e, including null slices."""
        assert e.det() != 0, 'the original coframe must be invertible'
        adj = e.adjugate()
        signed = [clean(sum((adj[mu, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4)))
                  for mu in range(4)]
        orientation = s.sign(e.det())
        E = orientation*signed[0]
        norm = s.expand((signed[0]*signed[0])[0, 0])
        V = [clean(orientation*signed[mu]*spin) for mu in range(4) for spin in self.spin]
        return {'E': clean(E), 'V': V, 'temporal_norm': norm,
                'internal_multiplicity': 63, 'orientation': orientation,
                'oriented_principals': signed}

    def matter_ports(self, e):
        """Canonical W=-i E^-1 V, requiring a noncharacteristic time slice."""
        data = self.raw_matter_ports(e)
        norm, signed = data['temporal_norm'], data['oriented_principals']
        assert norm != 0, 'the original temporal principal is characteristic'
        canonical = [clean(-s.I*signed[0]*signed[mu]*spin/norm)
                     for mu in range(4) for spin in self.spin]
        return {**data, 'W': canonical}

    def matter_current(self, e, primal, dual):
        """The independent-dual real action current on the full 252 carrier."""
        assert primal.shape == (252, 1) and dual.shape == (1, 252)
        ports = self.raw_matter_ports(e)
        return s.Matrix([s.simplify(s.re((dual*s.kronecker_product(V, s.eye(63))*primal)[0]))
                         for V in ports['V']])

    def eliminate(self, e, de, primal, dual):
        assert de.shape == (64, 1)
        geometry = self.geometry_maps(e)[0]*de
        matter = self.matter_current(e, primal, dual)
        inverse = self.inverse(e)
        return {'connection': clean(-inverse*(geometry+matter)),
                'geometry_source': geometry, 'matter_source': matter,
                'geometry_action': s.expand(-(geometry.T*inverse*geometry)[0]/2),
                'cross_action': s.expand(-(geometry.T*inverse*matter)[0]),
                'contact_action': s.expand(-(matter.T*inverse*matter)[0]/2)}

    def canonical_contact_coefficients(self, e):
        """Complete Re branches and CAR ordering coefficients, before a QFT domain.

        Physical indices are (branch, spin, color); the spin8 matrices tensor
        identity63.  The ordered product symbol has a one-body CAR contraction
        in addition to the normal-ordered quartic symbol.  Both are returned;
        neither an ordering prescription nor a continuum regulator is chosen.
        """
        ports = self.matter_ports(e)
        matrices = [clean(s.diag(matrix, -s.conjugate(matrix))) for matrix in ports['W']]
        inverse = self.inverse(e)
        tensor = s.MutableSparseMatrix(64, 64, {})
        contraction = s.MutableSparseMatrix(8, 8, {})
        for (a, b), value in inverse.todok().items():
            tensor += value*s.kronecker_product(matrices[a], matrices[b])/2
            contraction += value*matrices[a]*matrices[b]/2
        return matrices, clean(tensor), clean(contraction)


def certify_untruncated_density(model, e):
    B = s.Matrix(6, 6, s.symbols('B0:36', real=True))
    multiplier = s.Matrix(6, 6, s.symbols('M0:36', real=True))
    curvature = s.Matrix(6, 6, s.symbols('R0:36', real=True))
    density = s.expand(gravity_density(e, B, multiplier, curvature))
    S = s.diag(*PAIR_SIGN)
    gradient_B = (curvature-S*J*B+S*multiplier)*WEDGE
    gradient_multiplier = S*(B-J*wedge_matrix(e))*WEDGE
    equal(s.Matrix(6, 6, [s.diff(density, value) for value in B]), gradient_B)
    equal(s.Matrix(6, 6, [s.diff(density, value) for value in multiplier]), gradient_multiplier)
    Bs, Ms = model.simplicity(e, curvature)
    substitution = dict(zip(B, Bs)) | dict(zip(multiplier, Ms))
    equal(gradient_B.xreplace(substitution), s.zeros(6))
    equal(gradient_multiplier.xreplace(substitution), s.zeros(6))
    reduced = s.expand(density.xreplace(substitution))
    original_BF = sum((Bs.row(a)*WEDGE*curvature.row(a).T)[0] for a in range(6))
    assert s.expand(reduced-original_BF+3*e.det()) == 0
    for value in e:
        assert s.expand(s.diff(reduced, value)-s.diff(density, value).xreplace(substitution)) == 0

    omega = s.Matrix(s.symbols('omega0:24', real=True))
    R2 = model.curvature_quadratic(omega)
    quadratic = s.expand(sum((Bs.row(a)*WEDGE*R2.row(a).T)[0] for a in range(6)))
    H = model.hessian(e)
    assert s.expand(quadratic-(omega.T*H*omega)[0]/2) == 0
    equal(s.hessian(quadratic, omega), H)
    return {'all_72_original_auxiliary_Euler_coordinates': '0',
            'all_16_coframe_responses_after_simplicity': 'unchanged',
            'simplicity': 'B=J wedge^2(e), multiplier=J B-S curvature',
            'reduced_gravity_potential': '-3 det(e)',
            'Lorentz_dependence': 'exactly quadratic in all24; not a Taylor approximation',
            'IBP_boundary_flux': 'F^mu += C[a,(mu,nu)] Omega_(nu,a); F^nu -= C[a,(mu,nu)] Omega_(mu,a), summed over PAIRS and a',
            'IBP_identity': 'C*dOmega = divergence(F) + Omega^T G(e) de'}


def certify_generic_geometry(model, e):
    determinant = s.expand(e.det())
    H, K = model.hessian(e), model.inverse_numerator(e)
    G, torsion, curl = model.geometry_maps(e)
    T = s.kronecker_product(e, s.eye(6))
    equal(T*H*T.T, determinant*model.flat)
    equal(H*K, determinant*s.eye(24))
    equal(K*H, determinant*s.eye(24))
    equal(torsion*K*G, determinant*curl)
    equal(H, H.T)
    equal(K, K.T)
    assert model.flat.rank() == 24 and model.flat.det() == 256

    # Clear the only geometric denominator. This checks every coefficient of
    # the actual completion of the square for independent whole24 currents.
    # The Omega*j coefficients are H*K=det*I above; the j*j coefficients
    # below finish the square identity without expanding its dummy currents.
    equal(K*H*K, determinant*K)
    return {'generic_independent_coframe_variables': 16,
            'generic_independent_coframe_derivative_variables': 64,
            'flat_Hessian': encode(model.flat), 'flat_inverse': encode(model.flat_inverse),
            'Hessian': encode(H), 'inverse_numerator': encode(K),
            'geometry_source_map': encode(G), 'Cartan_torsion_map': encode(torsion),
            'coframe_exterior_derivative_map': encode(curl),
            'flat_rank': 24, 'flat_determinant': '256',
            'nonlinear_determinant': '256 det(e)^12',
            'covariance': '(e tensor I6) H(e) (e^T tensor I6)=det(e) H(I)',
            'inverse': 'H(e)^-1=(e^T tensor I6) H(I)^-1 (e tensor I6)/det(e)',
            'exact_Cartan_identity': 'Tor(e) K(e) G(e)=det(e) d_coframe',
            'connection': 'Omega*=-H(e)^-1 [G(e)de+j_matter]',
            'Cartan_equation_after_elimination': 'd_e+Tor(e)Omega*=-Tor(e)H(e)^-1 j_matter',
            'complete_square': 'L_Lorentz=1/2 (Omega-Omega*)^T H(e)(Omega-Omega*)-1/2 J_total^T H(e)^-1 J_total',
            'density_split': ['-1/2 J_geom^T H^-1 J_geom', '-J_geom^T H^-1 j_matter',
                              '-1/2 j_matter^T H^-1 j_matter'],
            'domain': 'real invertible e, both orientations; compact variations or the displayed boundary flux retained'}


def certify_matter(model, active, vertices, occupied, exchange):
    # Independent adjugate rows prove the temporal identity for every coframe
    # before specializing or lifting the exact identity through identity63.
    rows = s.Matrix(4, 4, s.symbols('adj0:16', real=True))
    C = [sum((rows[mu, a]*s.I*GAMMA[a] for a in range(4)), s.zeros(4)) for mu in range(4)]
    norm = s.expand((C[0]*C[0])[0, 0])
    equal(C[0]*C[0], norm*s.eye(4))
    eps = s.Symbol('orientation', real=True)
    for mu in range(4):
        for spin in model.spin:
            V = eps*C[mu]*spin
            numerator = -s.I*C[0]*C[mu]*spin
            equal((-s.I*eps*C[0])*numerator, -norm*V)

    e0 = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    N = s.sympify(vertices['source_lapse'])
    assert e0 == s.diag(N, 1, 1, 1) and N == 3*s.sqrt(30)/25
    ports = model.matter_ports(e0)
    primitive = {(item['group'], tuple(item['coordinate'])): decode(item['operator'])
                 for item in vertices['primitive_vertices']}
    all_vertices = {item['field']: decode(item['operator'])
                    for item in vertices['active_289_bosonic_source_operators']}
    for mu in range(4):
        for a in range(6):
            vertex = s.kronecker_product(ports['V'][6*mu+a], s.eye(63))
            equal(vertex, primitive['Lorentz', (mu, a)])
            equal(vertex, all_vertices[121+6*mu+a])
            equal(-s.I*ports['E']*ports['W'][6*mu+a], -ports['V'][6*mu+a])

    G0 = model.geometry_maps(e0)[0]
    H0 = model.hessian(e0)
    inverse = model.inverse(e0)
    old = active['algebraic_Schur_steps'][-1]
    assert old['eliminated_groups'] == ['Lorentz'] and old['eliminated_fields'] == list(range(121, 145))
    old_inverse = s.SparseMatrix(24, 24, {(i-121, j-121): s.sympify(v)
                    for i, j, v in old['algebraic_block_inverse']})
    equal(inverse, old_inverse)
    lorentz_contact = next(item for item in exchange['source_contact_terms'] if item['groups'] == ['Lorentz'])
    source_map = decode(lorentz_contact['source_map'])
    order = exchange['source_field_indices']
    expected = s.SparseMatrix(24, 97, {(a, order.index(121+a)): 1 for a in range(24)})
    equal(source_map, expected)
    equal(source_map.T*inverse*source_map, decode(lorentz_contact['kernel']))

    frame = decode(occupied['occupied_frame'])
    seed = s.Matrix(active['actual_background']['primal_H']).applyfunc(s.sympify)
    primal = frame*seed
    dual = s.sqrt(2)*primal.T
    result = model.eliminate(e0, s.zeros(64, 1), primal, dual)
    original_connection = s.Matrix(active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
    equal(result['connection'], original_connection)
    equal(H0*original_connection+result['matter_source'], s.zeros(24, 1))
    assert result['contact_action'] == -18*s.sqrt(30)/25

    gamma5 = s.diag(-1, -1, 1, 1)
    swap = GAMMA[0]*gamma5
    axial = [s.sqrt(2)*swap*gamma*gamma5 for gamma in GAMMA]
    axial_basis = s.Matrix.hstack(*[value.reshape(16, 1) for value in axial])
    axial_left = (axial_basis.T*axial_basis).inv()*axial_basis.T
    axial_map = s.zeros(24, 4)
    for a, V in enumerate(ports['V']):
        prepared_real = clean(s.sqrt(2)*(swap*V+V.H*swap)/2)
        coefficients = clean(axial_left*prepared_real.reshape(16, 1))
        equal(axial_basis*coefficients, prepared_real.reshape(16, 1))
        axial_map[a, :] = coefficients.T
    equal(axial_map, decode(exchange['canonical_spin_source_axial_map']))
    equal(axial_map.T*inverse*axial_map, 3*N/8*s.diag(1, -1, -1, -1))
    ranks = [s.Matrix.hstack(*[s.Matrix.vstack(matrix.applyfunc(s.re).reshape(16, 1),
                matrix.applyfunc(s.im).reshape(16, 1)) for matrix in ports[name]]).rank()
             for name in ('V', 'W')]
    assert ranks == [8, 8] and axial_map.rank() == 4
    # A negative orientation remains a true raw current identity. Gravity's
    # inverse changes with oriented det; the matter measure stays positive.
    reverse = s.diag(-N, 1, 1, 1)
    negative = model.matter_ports(reverse)
    assert negative['orientation'] == -1
    equal(negative['E'], ports['E']*-1)
    for V, matrix in zip(negative['V'], negative['W']):
        equal(-s.I*negative['E']*matrix, -V)
    assert model.hessian(reverse) != H0
    null_slice = s.Matrix([[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    null_raw = model.raw_matter_ports(null_slice)
    assert null_slice.det() == -2 and null_raw['temporal_norm'] == 0
    null_result = model.eliminate(null_slice, s.zeros(64, 1), primal, dual)
    equal(model.hessian(null_slice)*null_result['connection']+null_result['matter_source'], s.zeros(24, 1))
    try:
        model.matter_ports(null_slice)
    except AssertionError as error:
        assert str(error) == 'the original temporal principal is characteristic'
    else:
        raise AssertionError('canonical W must not invert a null temporal principal')
    return {'full_internal_dimension': 252, 'all_Lorentz_currents': 24,
            'raw_independent_dual_source': 'j_(mu,a)=Re chi [|det e| sum_b (e^-1)_(mu,b) i Gamma_b Spin_a tensor I63] psi',
            'normalized_momentum': 'p=-i chi E; E=|det e| sum_b (e^-1)_(0,b) i Gamma_b tensor I63',
            'canonical_vertex': 'W_(mu,a)=-i E^-1 V_(mu,a)',
            'original_Legendre_identity': 'p W psi=-chi V psi; j=-Re(p W psi)',
            'generic_temporal_principal_square': str(norm),
            'canonical_domain': 'det(e)!=0 and temporal_norm!=0; no positive-adjoint graph imposed',
            'density_source_real_rank_at_actual_background': ranks[0],
            'canonical_vertex_real_rank_at_actual_background': ranks[1],
            'prepared_axial_subreadout_rank': 4,
            'background_V_spin4': list(map(encode, ports['V'])),
            'background_W_spin4': list(map(encode, ports['W'])),
            'background_geometry_source_map': encode(G0),
            'background_Hessian': encode(H0), 'background_inverse': encode(inverse),
            'actual_background_matter_source': encode(result['matter_source']),
            'actual_original_connection_regenerated': encode(result['connection']),
            'actual_background_contact_action': str(result['contact_action']),
            'existing_exchange_consumer': 'all24 Lorentz auxiliary inverse and its exact97-source embedded Contact term; the additional scalar-Ward Contact is a separate term',
            'prepared_axial_action': '3N/16*(-axial0^2+axial1^2+axial2^2+axial3^2)',
            'negative_orientation_current_identity_checked': True,
            'null_temporal_but_invertible_coframe_eliminates_all24': True,
            'noncharacteristic_required_only_for_canonical_W': True,
            'canonical_vertices_equal_density_vertices': False}


def certify_CAR_coefficients(model, e):
    matrices, tensor, contraction = model.canonical_contact_coefficients(e)
    N = e[0, 0]
    equal(contraction, -3*N/4*s.eye(8))
    # Complete +/- branch combinations survive in the coefficient producer.
    branch_counts = {}
    for (row, column), value in tensor.todok().items():
        i, k = divmod(row, 8)
        j, l = divmod(column, 8)
        assert i//4 == j//4 and k//4 == l//4
        key = str(i//4)+str(k//4)
        branch_counts[key] = branch_counts.get(key, 0)+1
    assert set(branch_counts) == {'00', '01', '10', '11'}
    # Exact CAR contraction is a readout of the same full quartic coefficient,
    # not a separately supplied one-body term or a selected vertex.
    traced = s.Matrix(8, 8, lambda i, l: sum(tensor[8*i+j, 8*j+l] for j in range(8)))
    equal(traced, contraction)
    z, w = s.symbols('z w', complex=True)
    assert s.expand_complex((z*w+s.conjugate(z*w))/2-s.re(z*w)) == 0
    assert s.sqrt(2)**2/2 == 1
    return {'branches': 'M_a=diag(W_a,-conjugate(W_a)); complete matrix M_a tensor I63 on504 modes',
            'original_Re_weights': '1/2 with raw primal sqrt(2)c and momenta (+sqrt(2)c^dagger,-sqrt(2)c^dagger); no residual arbitrary Z',
            'fixed_coframe_contact_Hamiltonian_symbol': '+1/2 sum_ab H(e)^-1_ab rho_a rho_b, rho_a=Re(p W_a psi)=-j_a',
            'normal_ordered_quartic_coefficient_spin8': encode(tensor),
            'tensor_index_order': '(i,k),(j,l); coefficient of c^dagger_i c^dagger_k c_l c_j, with delta_color(i,j) delta_color(k,l)',
            'all_real_branch_coefficient_counts': branch_counts,
            'ordered_CAR_product_contraction_spin8': encode(contraction),
            'ordered_product_minus_normal_product': '-3N/4 dGamma(I504)=-9sqrt(30)/100 dGamma(I504) at actual coframe',
            'generic_CAR_identity': 'dGamma(A)dGamma(B)=dGamma(AB)+normalProduct(A,B)',
            'quantum_ordering_prescription_selected': False,
            'continuum_coincident_product_or_physical_vacuum_constructed': False,
            'Lorentz_auxiliary_CCR_added': False}


def main():
    began = time.monotonic()
    model = SourceLorentzContact()
    active = json.loads((BASE/'active-gauge/receipt.json').read_text())
    vertices = json.loads((BASE/'matter-vertices/receipt.json').read_text())
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    exchange = json.loads((BASE/'matter-vertices/exchange.json').read_text())
    for name, expected in vertices['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected
    e = s.Matrix(4, 4, s.symbols('e0:16', real=True))
    density = certify_untruncated_density(model, e)
    print('PASS untruncated original BF/simplicity:72 Euler,16 coframe,whole24 quadratic polynomial', flush=True)
    geometry = certify_generic_geometry(model, e)
    print('PASS generic16 coframe covariance/inverse,64 derivative Cartan identity and exact square', flush=True)
    matter = certify_matter(model, active, vertices, occupied, exchange)
    print('PASS whole252 independent-dual currents,all24 source connection and original Lorentz Contact', flush=True)
    e0 = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    car = certify_CAR_coefficients(model, e0)
    print('PASS original Re504 branches,whole quartic tensor and exact CAR ordering contraction', flush=True)
    core = ROOT/'Lean/SaturationMonoid/PhysicsCore'
    paths = [core/name for name in (
        'DiracCliffordRepresentation.lean','StageNineFormNativeMotherAction.lean',
        'StageNineDiracDualFormNativeMotherAction.lean',
        'StageNineDiracDualFormNativeLorentzConnectionVariation.lean',
        'StageNineTopologicalGravityCurvatureVariancePairing.lean',
        'LowEnergy/FullQuantum/Source.lean','LowEnergy/Fermion/NormalOrder.lean')]
    paths += [BASE/name for name in ('nonlinear-contact/slice_checks.py','active-gauge/compute.py',
        'active-gauge/receipt.json','matter-vertices/receipt.json','matter-vertices/exchange.py',
        'matter-vertices/exchange.json','occupied-response/receipt.json')]
    paths += [HERE/name for name in ('source_lorentz_contact.py','RealScalarFock.lean')]
    bindings = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
    output = {'root': ROOT_ID, 'source_sha256': vertices['source_sha256'], 'input_sha256': bindings,
        'scope': 'ORIGINAL_NONLINEAR_BF_SIMPLICITY_AND_LORENTZ_AUXILIARY_ELIMINATION_WITH_FULL252_REAL_MATTER_CURRENT',
        'untruncated_original_density': density, 'generic_geometry': geometry,
        'whole_matter_current_and_existing_Contact': matter, 'canonical_real_CAR_coefficients': car,
        'public_producer': 'SourceLorentzContact.{simplicity,hessian,geometry_maps,inverse,raw_matter_ports,matter_ports,matter_current,eliminate,canonical_contact_coefficients}',
        'remaining_bosonic_Legendre_responsibility': 'J_geom contains coframe derivatives; recompute their reduced momenta before calling the complete geom/cross action a Hamiltonian',
        'auxiliary_elimination_count': 'Bg+multiplier then originalLorentz24, once each; independent-dual24 retained dynamics is a different block',
        'Taylor_truncation_or_occupied12_used_as_nonlinear_producer': False,
        'new_source_occurrence_or_coupling': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_lorentz_contact.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original nonlinear Lorentz/Contact producer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
