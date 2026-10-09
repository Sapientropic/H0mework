"""Consume the completed current inlet through its original constructors."""
from pathlib import Path
import hashlib
import json

import reissued_source_intake_rha0027 as paid
import prepared_retarded_gaussian_inlet as inlet

HERE, ROOT = paid.HERE, paid.ROOT
FIRST = HERE/'retarded-inlet-first-rha0027.json'
FREEZE = 'e7c9ad745ebda5666f2035e24aaeb7a82d25e310'


def _artifact(binding, directory):
    relative = Path(binding['path'])
    paid.require(not relative.is_absolute() and '..' not in relative.parts, 'inlet artifact outside its workspace')
    path = ROOT/relative if directory is None else Path(directory)/relative.name
    paid.require(path.stat().st_size == binding['bytes'], 'completed inlet snapshot byte count changed')
    with path.open('rb') as handle:
        paid.require(hashlib.file_digest(handle, 'sha256').hexdigest() == binding['sha256'],
                     'completed inlet snapshot SHA changed')
    with path.open() as handle:
        return json.load(handle)


def consume(*, artifacts_directory=None):
    receipt = json.loads(paid.frozen(FIRST))
    paid.require(receipt['schema'] == 'stage10-completed-current-retarded-inlet-evidence/rha0027' and
        receipt['scientific_freeze_commit'] == FREEZE and receipt['complete_local_residual_count'] == 10 and
        receipt['scope']['ten_complete_local_residuals_checked'] is True and
        receipt['scope']['current_PreparedRetardedGaussianInlet_issued'] is True and
        receipt['scope']['generation1_asserted'] is False and
        receipt['scope']['actual_hardware_member_asserted'] is False,
        'completed current inlet evidence scope changed')
    for relative, expected in receipt['source_bindings'].items():
        paid.require(hashlib.sha256(paid.frozen(ROOT/relative, FREEZE)).hexdigest() == expected,
                     'completed inlet execution no longer matches its checked evidence')
    summary = _artifact(receipt['completed_producer_summary'], artifacts_directory)
    paid.require(summary['schema'] == 'stage10-paid-current-source-retarded-inlet/rha0027' and
        all(summary[key] == receipt[key] for key in summary if key != 'schema'),
        'completed inlet producer summary changed')
    payload = _artifact(receipt['fresh_inlet'], artifacts_directory)
    raw, banks = payload['source_record'], payload['density_witnesses']
    paid.require(raw['source_bindings'] == inlet._bindings() and len(banks) == 2 and
        sum(map(len, banks)) == 10 and raw['whole_retarded_gate_input_error'] == receipt['whole_retarded_gate_input_error'] and
        raw['actual_retarded_local_cuts_seconds'] == receipt['source_retarded_local_cuts_seconds'],
        'completed inlet source, complete inventory, input error or clock changed')
    for bank in banks:
        for item in bank:
            report = item['complete_density_certificate']
            paid.require(report['schema'] == inlet.density.SCHEMA+'/checked-curve' and
                report['source_record']['source_bindings'] == inlet.density._bindings(),
                'completed local curve execution changed')
    return receipt, payload


def restore(*, artifacts_directory=None):
    receipt, payload = consume(artifacts_directory=artifacts_directory)
    source = paid.restore_prepared()
    paid.require(source.record() == payload['source_record']['source_issued_two_pump_source'],
                 'the completed inlet must consume the same paid pump parent')
    for bank in payload['density_witnesses']:
        for item in bank:
            report = item['complete_density_certificate']
            inlet.density._CHECKED[inlet.density._digest(report)] = inlet.density._copy(report)
    law = inlet.retarded.RetardedGaussianBSMSource(source._field)
    current = inlet.PreparedRetardedGaussianInlet(source, law, payload['density_witnesses'],
                                                 bits=payload['source_record']['scalar_bits'])
    paid.require(current.record() == payload['source_record'],
                 'original constructors must reproduce the complete paid current inlet')
    return current
