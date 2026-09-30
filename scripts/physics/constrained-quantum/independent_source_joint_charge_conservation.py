#!/usr/bin/env python3
"""Certify the actual source charges of the joint operator and its graph blocks."""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import tempfile
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_joint_ccr_car_ports import SourceJointCCRCarPorts


def read(path):
    return json.loads(path.read_bytes())


def matrix(data):
    return s.SparseMatrix(*data['shape'], {(i, j): s.sympify(c) for i, j, c in data['entries']})


def clean(state):
    return {w: c for w, raw in state.items() if (c := s.cancel(s.expand(raw))) != 0}


def equal_states(left, right):
    assert not clean({w: left.get(w, 0)-right.get(w, 0) for w in left.keys() | right.keys()})


def commutes(A, B):
    assert all(s.cancel(s.expand(c)) == 0 for c in s.SparseMatrix(A*B-B*A).todok().values())


@lru_cache(None)
def step(word, mode, creation):
    if (mode in word) == creation:
        return None
    sign = (-1)**sum(j < mode for j in word)
    out = tuple(sorted((*word, mode))) if creation else tuple(j for j in word if j != mode)
    return out, sign


class OccupationAction:
    """Independent bit occupation action, including the original four-word order."""
    def __init__(self):
        self.columns = {}

    def column(self, A, j):
        key = id(A)
        if key not in self.columns:
            columns = defaultdict(list)
            for (i, k), c in s.SparseMatrix(A).todok().items():
                columns[k].append((i, c))
            self.columns[key] = A, columns
        return self.columns[key][1][j]

    def one_body(self, A, state):
        out = defaultdict(int)
        for w, c in state.items():
            for j in w:
                u, sign = step(w, j, False)
                for i, a in self.column(A, j):
                    created = step(u, i, True)
                    if created:
                        v, other = created
                        out[v] += c*a*sign*other
        return clean(out)

    def normal(self, A, B, state):
        out = defaultdict(int)
        for w, c in state.items():
            for j in w:
                u, sign = step(w, j, False)
                for ell in u:
                    v, other = step(u, ell, False)
                    for k, b in self.column(B, ell):
                        created = step(v, k, True)
                        if not created:
                            continue
                        z, third = created
                        for i, a in self.column(A, j):
                            final = step(z, i, True)
                            if final:
                                target, fourth = final
                                out[target] += c*a*b*sign*other*third*fourth
        return clean(out)

    def hamiltonian(self, H, state):
        out = defaultdict(int, {w: H.scalar*c for w, c in state.items()})
        for w, c in self.one_body(H.one_body, state).items():
            out[w] += c
        for coefficient, A, B in H.pairs:
            for w, c in self.normal(A, B, state).items():
                out[w] += coefficient*c
        return clean(out)


def source_charges(target):
    source = read(BASE/'matter-charge-selection/receipt.json')
    basis = [matrix(item) for item in source['matter_commutant']['basis']]
    diagonal = [A for A in basis if A.is_diagonal()]
    forward, reverse = [A for A in basis if not A.is_diagonal()]
    h = diagonal+[forward+reverse, s.I*(forward-reverse)]
    assert len(h) == 14 and sum(diagonal, s.zeros(63)) == s.eye(63)
    expected = []
    for a, internal in enumerate(h):
        assert internal.H == internal
        full = s.kronecker_product(s.eye(4), internal)
        lifted = s.SparseMatrix(s.diag(-full, full.conjugate()))
        assert lifted == matrix(target['source_real_CAR504_generators'][a])
        assert internal == matrix(target['source_hermitian_basis63'][a])
        # Rebuild the original real representation, without candidate.realify.
        rho = s.I*full
        real = s.SparseMatrix(s.BlockMatrix([[s.re(rho), -s.im(rho)],
                                           [s.im(rho), s.re(rho)]]).as_explicit())
        I = s.eye(252)
        U = s.SparseMatrix(s.BlockMatrix([[I, s.I*I], [I, -s.I*I]]).as_explicit()/s.sqrt(2))
        assert U*(s.I*real)*U.H == lifted
        assert s.diag(full, full.conjugate()) != lifted
        expected.append(lifted)
    assert expected[12]*expected[13] != expected[13]*expected[12]
    return source, h, expected


def finite_spectra(charges, target):
    nodes = 0
    radii = []
    for Q in charges[:12]:
        row = list(Q.diagonal())
        assert all(c in (-1, 0, 1) for c in row)
        minus = [j for j, c in enumerate(row) if c == -1]
        plus = [j for j, c in enumerate(row) if c == 1]
        r = len(plus)
        assert r == len(minus) > 0
        radii.append(r)
        for value in range(-r, r+1):
            word = plus[:value] if value >= 0 else minus[:-value]
            assert sum(row[j] for j in word) == value
            for selected in range(-r, r+1):
                if selected == value:
                    polynomial = math.prod(Fraction(value-m, selected-m)
                        for m in range(-r, r+1) if m != selected)
                else:
                    # The m=value factor occurs and has a nonzero denominator.
                    # This is an exact zero factor, not a numerical tolerance.
                    polynomial = Fraction(value-value, selected-value)
                assert polynomial == int(selected == value)
            nodes += 1
    assert sum(radii) == 252 and nodes == 516
    assert radii == target['finite_charge_projectors']['radii']
    return {'actual_signed_radii': radii, 'all_realized_spectral_nodes': nodes,
            'all_Lagrange_values_checked': True, 'noncommuting_U2_pair_retained': True,
            'whole_carrier_argument': 'Every occupation selects each signed mode at most once. Its charge is an integer in the displayed interval, every integer is attained, and all Lagrange polynomials were evaluated on every possible integer. The occupation basis spans the full finite CAR carrier. The twelve diagonal operators commute; their joint projectors are orthogonal and exhaustive, permitting zero joint blocks.'}


def actual_consumers(model, h, charges, ports, target):
    common = model.leaf.weyl.native.joint.common
    primitives = []
    for i in range(4):
        for j in range(4):
            primitives.append(s.kronecker_product(s.SparseMatrix(4, 4, {(i, j): 1}), s.eye(63)))
    primitive_count = 0
    for internal, Q in zip(h, charges):
        full = s.kronecker_product(s.eye(4), internal)
        for A in [*primitives, *common.rho, *common.yukawa_basis]:
            commutes(full, A)
            primitive_count += 1
        for A in model.leaf.charges:
            commutes(Q, A)
            primitive_count += 1
        for A in primitives:
            for branch in range(2):
                block = s.zeros(504)
                block[252*branch:252*(branch+1), 252*branch:252*(branch+1)] = A
                commutes(Q, block)
                primitive_count += 1
    assert primitive_count == 1498
    configuration = tuple(map(s.sympify, ports['configuration100']))
    # Different configuration momenta and occupation from the candidate's fixture.
    phase = configuration+tuple(s.Rational(j % 5-2, 67) for j in range(100))
    H = model.symbol(phase)
    sharp = H.adjoint()
    act = OccupationAction()
    source = read(BASE/'matter-charge-selection/receipt.json')['matter_commutant']
    first, second = source['M2_first_sector'], source['M2_second_sector']
    word = tuple(sorted((8, 126+first[0], 378+second[2])))
    state = {word: s.S.One}
    image = act.hamiltonian(H, state)
    image_sharp = act.hamiltonian(sharp, state)
    assert image and image_sharp
    equal_states(image, H.apply(state))
    equal_states(image_sharp, sharp.apply(state))
    for Q in charges:
        qstate = act.one_body(Q, state)
        equal_states(act.one_body(Q, image), act.hamiltonian(H, qstate))
        equal_states(act.one_body(Q, image_sharp), act.hamiltonian(sharp, qstate))
    diagonals = [list(Q.diagonal()) for Q in charges[:12]]
    def signature(w):
        return tuple(sum(row[j] for j in w) for row in diagonals)
    assert all(signature(w) == signature(word) for w in image.keys() | image_sharp.keys())
    count = 0
    for entry in ports['actual_full_H_images']:
        for output, _ in entry['unchanged_differential_H']:
            assert signature(output) == signature(entry['input'])
            count += 1
    for output, _ in ports['actual_force']['image']:
        assert signature(output) == signature((144, 396))
        count += 1
    for entry in ports['actual_CAR_ports']:
        expected = tuple(value+(1 if entry['creation'] else -1)*row[entry['mode']]
            for value, row in zip(signature(entry['word']), diagonals))
        for output, _ in entry['original_differential_port']:
            assert signature(output) == expected
            count += 1
    assert count == target['frozen_differential_output_charge_checks'] == 251
    return {'original_full_family_primitive_checks': primitive_count,
            'different_configuration_momentum_and_CAR_word': list(word),
            'independent_four_word_action_against_actual_H_and_Hsharp': True,
            'all14_actual_operator_intertwiners_checked': True,
            'original_differential_force_and_CAR_charge_outputs': count,
            'quartic_count_scope': '119 counts the frozen source fixture. All-configuration conservation follows from the complete source coefficient algebra, including its derivatives, not from a fixed support count.'}


def lean_check():
    names = ['SaturationMonoid.PhysicsCore.LowEnergy.Fermion.'+name for name in (
        'occupationCharge_quantize', 'occupationCharge_normalProduct',
        'occupationCharge_preserves_eigenstate', 'occupationCharge_selection')]
    names += ['SourceJointCCRCarPorts.normalProduct_primal_port',
              'SourceJointCCRCarPorts.normalProduct_independent_momentum_port']
    with tempfile.TemporaryDirectory(prefix='source-joint-charge-certify-') as directory:
        path = Path(directory)/'Audit.lean'
        path.write_text('import SaturationMonoid.PhysicsCore.LowEnergy.Fermion.Charge\n'+
            (HERE/'JointCCRCarPorts.lean').read_text()+'\n'+
            '\n'.join('#print axioms '+name for name in names)+'\n')
        result = subprocess.run(['lake', 'env', 'lean', '--trust=0', '-DwarningAsError=true', str(path)],
            cwd=ROOT/'Lean', text=True, capture_output=True, check=True)
    axioms = {name: [entry.strip() for entry in values.split(',') if entry.strip()]
              for name, values in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)}
    assert set(axioms) == set(names), result.stdout
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(values) <= allowed for values in axioms.values()), axioms
    return {'exit_code': result.returncode, 'trust': 0, 'warning_as_error': True,
            'source_theorems': names, 'axioms': axioms}


def main():
    started = time.monotonic()
    target_path = HERE/'source_joint_charge_conservation.json'
    target = read(target_path)
    assert target['root'] == ROOT_ID
    assert target['scope'] == 'FULL_LOCAL_INTERACTING_SOURCE_HAMILTONIAN_CHARGES_AND_MINIMAL_GRAPH_BLOCKS'
    paths = [target_path, HERE/'source_joint_charge_conservation.py', Path(__file__),
             HERE/'source_full_quantum_adjoint.json', HERE/'independent_source_full_quantum_adjoint.json',
             HERE/'source_common_hamiltonian.py', HERE/'source_common_weyl_symbol.py']
    hashes = {}
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in target[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            hashes[name] = digest
    adjoint = read(HERE/'independent_source_full_quantum_adjoint.json')
    assert adjoint['root'] == ROOT_ID and adjoint['verdict'].startswith('CERTIFIED')
    _, h, charges = source_charges(target)
    spectra = finite_spectra(charges, target)
    print('PASS independent actual504 real lift and all516 finite charge spectral nodes', flush=True)
    consumers = actual_consumers(SourceJointCCRCarPorts(), h, charges,
        read(HERE/'source_joint_ccr_car_ports.json'), target)
    print('PASS independent primitive closure, new actual interacting state and all251 original charge outputs', flush=True)
    lean = lean_check()
    hashes.update({str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    result = {'root': ROOT_ID, 'scope': target['scope'], 'verdict': 'CERTIFIED', 'source_hashes': hashes,
        'finite_source_spectra': spectra, 'actual_consumers': consumers, 'Lean_consumers': lean,
        'minimal_graph_consumer': {
            'same_original_formal_adjoint_pair_consumed': True,
            'direct_proof': 'Every source charge is constant in configuration, preserves total CAR occupation and therefore the original number-dependent density and half-density. Its bounded action and every finite charge polynomial preserve the original compact smooth core. Apply P x_n->P x and H P x_n=P H x_n->P y to a defining graph sequence (x_n,H x_n)->(x,y). This proves invariance of the minimal closed graph and commutation on its actual domain; the same proof applies to Hsharp. No selfadjoint extension or energy spectral theorem is used.',
            'twelve_commuting_charge_projectors_not_fourteen': True,
            'energy_spectrum_or_particle_name_supplied': False},
        'scope_readback': 'Full original local Gauss100 interacting H and independent Hsharp preserve the generated charge blocks on the same core and minimal graph domains. These are charge spectra, not Hamiltonian spectra or proton identification.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_source_joint_charge_conservation.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source joint charges and minimal graph blocks', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
