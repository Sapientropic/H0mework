#!/usr/bin/env python3
"""Recheck the literal H0 behind the common-carrier unitary and CAR consumers."""
from pathlib import Path
import hashlib
import json
import time
from dynamic import HERE, ROOT, ROOT_ID
from source_live_differential_hamiltonian import SourceLiveDifferentialHamiltonian
from source_joint_form_hamiltonian import read_bound
from source_diagonal_grade import run


def main(raw=None):
    began = time.monotonic()
    raw = SourceLiveDifferentialHamiltonian() if raw is None else raw
    for name in ('source_diagonal_grade', 'source_diagonal_core_history',
                 'source_live_differential_hamiltonian'):
        read_bound(name)
    records = run(raw)
    lean = ('GaussAdjointHistory', 'GaussFockLift', 'GaussCARHistory',
            'SourceFamilyHilbert', 'SourceFamilyOperator', 'GaussUnitaryHistory',
            'GaussUnitaryCore', 'FiniteCoreEvolution', 'WeakCoreEvolution',
            'GaussDiagonalHistory', 'GaussHalfDensity', 'GaussCoreHilbert',
            'SourceQuantumCARBound')
    paths = [Path(__file__), HERE/'source_diagonal_grade.py']
    paths += [HERE/(name+'.lean') for name in lean]
    paths += [HERE/(name+'.json') for name in
              ('source_diagonal_grade', 'source_diagonal_core_history',
               'source_live_differential_hamiltonian')]
    report = {
        'root': ROOT_ID,
        'scope': 'ACTUAL_H0_COMMON_CARRIER_UNITARY_CAR_AND_TWO_TIME_CORE_RESPONSE',
        'source_sha256': raw.full.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                         for p in paths},
        'original_H0_state_actions': records,
        'original_Y_retained_nonzero_grade': 1,
        'lean_consumers': ['GaussUnitaryHistory.time_add', 'GaussUnitaryHistory.time_norm',
                           'GaussUnitaryHistory.weak_readback', 'GaussUnitaryHistory.car_all_time',
                           'GaussUnitaryCore.core_derivative', 'GaussUnitaryCore.core_smooth',
                           'GaussUnitaryCore.source_continuous',
                           'GaussUnitaryCore.response_left', 'GaussUnitaryCore.response_right'],
        'carrier': 'Completion of bounded original-Hilbert families with the original shared cofinal-filter inner product; the constant-family inclusion is isometric.',
        'readback': 'The common time group returns the original unpinched GaussDiagonalHistory.history through the constant inclusion.',
        'reader': 'Original half-density normalized full-Fock CAR; products are retained on the common carrier.',
        'scope_boundary': 'Unitary group on the common carrier; strong continuity on every embedded original-state orbit and smoothness on the original core. Whole-carrier Number/G commutation, physical unbounded readers and original Y remain separate obligations.',
        'controller': 'Original source/root/current and whole ledger unchanged; subordinate producer.',
        'seconds': round(time.monotonic()-began, 3),
    }
    (HERE/'source_unitary_core_history.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    print('PASS original H0 source return for unitary/CAR core consumers', report['seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
