"""Restore the existing checked generation-zero source, without rechecking pumps.

This consumes one frozen completed producer receipt.  It is an evidence
readout, not a new numerical certificate or a source of free endpoints.
All original constructors and predecessor/source-frame checks still run.
"""
from pathlib import Path
from types import ModuleType
import hashlib
import json
import subprocess

import source_reissue_rha0025 as producer

HERE, ROOT = producer.HERE, producer.ROOT
FIRST = HERE/'source-reissue-pumps-first-rha0025.json'
FREEZE = 'd8097db5cc09c0cab95b1623f46ea45e8a97832b'


def require(value, reason):
    if not value:
        raise ValueError(reason)


def frozen(path, commit='HEAD'):
    path = Path(path); data = path.read_bytes(); relative = path.relative_to(ROOT).as_posix()
    saved = subprocess.check_output(['git', '-C', str(ROOT), 'show', commit+':'+relative])
    require(data == saved, 'unregistered reissued-source evidence: '+relative)
    return data


def prefix_modules():
    seen = {}; pending = [producer.reference, producer.local, producer.programme, producer.prepared]
    while pending:
        module = pending.pop(); path = Path(getattr(module, '__file__', '')).resolve()
        if path.parent != HERE or path in seen:
            continue
        seen[path] = module
        pending.extend(value for value in vars(module).values() if isinstance(value, ModuleType))
    return set(seen)


def report_inventory(prepared, certificates):
    parent = prepared['reference_local_parent']; programme = prepared['programme_source_record']
    require(type(certificates) is list and len(certificates) == 2, 'both complete checked pump banks required')
    reports = []
    for side, bank in enumerate(certificates):
        expected = parent['local_factor_inventory'][side]
        require([row['factor_id'] for row in bank] == [row['factor_id'] for row in expected], 'checked source factor coverage')
        for row, initial in zip(bank, expected):
            previous = []; value = initial['initial_local_matrix']; old = '0'
            phase_reports = row['complete_phase_certificates']
            require(len(phase_reports) == 2, 'both complete checked predecessor phases required')
            for index, report in enumerate(phase_reports):
                raw = report['source_record']
                require(report['schema'] == producer.programme.PHASE_SCHEMA+'/coimage' and
                    raw['programme_source_digest'] == producer.programme._digest(programme) and
                    raw['side'] == side and raw['factor_id'] == row['factor_id'] and raw['phase_index'] == index and
                    raw['source_phase'] == parent['source_generated_local_plans'][side][index]['source_phase'] and
                    raw['complete_initial_local_factor'] == value and raw['factor_upstream_error'] == old and
                    raw['verified_preceding_phase_certificate_digests'] == previous,
                    'cached report belongs to another source, phase, initial factor or predecessor')
                previous.append(producer.programme._digest(report)); value = report['full_local_poststate']
                old = report['trace_norm_error']; reports.append(report)
    require(len(reports) == 20, 'the original ten factors and both pumps must be complete')
    return reports


def consume(*, artifacts_directory=None):
    receipt = json.loads(frozen(FIRST))
    require(receipt['schema'] == 'stage10-completed-source-reissued-pump-evidence/rha0025' and
        receipt['scientific_freeze_commit'] == FREEZE and receipt['complete_pump_certificate_count'] == 20 and
        receipt['original_source_payload_sha256'] == producer.original.INPUT_SHA and
        receipt['original_pump_witness_sha256'] == producer.WITNESS_SHA and
        receipt['scope']['complete_two_pump_prefix_rechecked'] is True and
        receipt['scope']['current_PreparedGaussianFieldSource_issued'] is True and
        receipt['scope']['actual_hardware_member_asserted'] is False and
        receipt['scope']['actual_hardware_uniquely_identified'] is False and
        receipt['scope']['controller_advance'] is False, 'the completed original source scope is missing')
    corridor = receipt['checked_prefix_execution_dependencies']
    require({(ROOT/path).resolve() for path in corridor} == prefix_modules(), 'the paid source execution scope changed')
    for relative, expected in corridor.items():
        require(hashlib.sha256(frozen(ROOT/relative, FREEZE)).hexdigest() == expected,
                'the checked prefix code no longer matches its completed evidence')
    values = {}
    for role, binding in receipt['source_artifacts'].items():
        relative = Path(binding['path'])
        require(not relative.is_absolute() and '..' not in relative.parts, 'source snapshot outside the declared workspace')
        path = ROOT/relative if artifacts_directory is None else Path(artifacts_directory)/relative.name
        require(path.stat().st_size == binding['bytes'], 'source snapshot byte count changed: '+role)
        with path.open('rb') as handle:
            require(hashlib.file_digest(handle, 'sha256').hexdigest() == binding['sha256'], 'source snapshot SHA changed: '+role)
        with path.open() as handle: values[role] = json.load(handle)
    summary = values['summary']
    require(summary['scientific_freeze_commit'] == FREEZE and summary['complete_two_pump_prefix_rechecked'] is True and
            summary['source_payload_sha256'] == producer.original.INPUT_SHA and summary['solver_executed'] is False,
            'the completed producer summary changed')
    reports = report_inventory(values['prepared'], values['pumps'])
    require(values['prepared']['reference_local_parent']['reference_first_poll_ready'] == values['ready'],
            'the same primitive-generated Ready must remain the pump parent')
    return receipt, values, reports


def restore_prepared(*, artifacts_directory=None):
    receipt, values, reports = consume(artifacts_directory=artifacts_directory)
    with producer.WITNESS.open('rb') as handle:
        require(hashlib.file_digest(handle, 'sha256').hexdigest() == receipt['original_pump_witness_sha256'],
                'the original shared source templates changed')
    with producer.WITNESS.open() as handle: witness = json.load(handle)
    # This memo contains exactly the reports already checked by the completed
    # frozen producer.  verify still matches every full source frame before
    # accepting a cache entry; no caller-supplied endpoint is admitted here.
    for report in reports:
        producer.programme._CHECKED[producer.programme._digest(report)] = producer.programme._copy(report)
    record = values['prepared']
    parent = producer.local.ReferenceLocalPhaseSource.from_record(record['reference_local_parent'])
    programme = producer.programme.FourierReferenceLocalProgrammeSource(parent)
    field = record['Gaussian_field_source']
    pulses = tuple(producer.prepared.driven.gaussian.GaussianAtomicPulseSource(parent, side,
        **{name: field['Gaussian_source_legs'][side][name] for name in
           ('sigma_squared_seconds', 'centre_seconds', 'duration_seconds', 'phase_radians')}) for side in (0, 1))
    photon = producer.prepared.driven.DrivenGaussianFieldSource(*pulses,
        flight_seconds=field['flight_seconds'], emission_origins_seconds=field['emission_origins_seconds'],
        gate_seconds=field['gate_seconds'])
    restored = producer.prepared.PreparedGaussianFieldSource(programme, values['pumps'],
        witness['shared_phase_templates'], photon, bits=record['scalar_bits'])
    require(restored.record() == record, 'the shared-parent restore must preserve the complete original source')
    return restored


def completed_density_reports():
    """Reuse only the first local check actually completed before the writer failure."""
    import gaussian_local_density_source as density
    receipt = json.loads(frozen(HERE/'retarded-local-density-first-rha0027.1.json'))
    require(receipt['schema'] == 'stage10-completed-retarded-local-density-evidence/rha0027.1' and
        receipt['scientific_freeze_commit'] == '654428649706d972c361c9d2be1716ff7221b965' and
        receipt['scope']['complete_local_residual_checked'] is True and
        receipt['scope']['whole_retarded_inlet_checked'] is False,
        'completed local density evidence scope changed')
    reports = {}
    for entry in receipt['source_artifacts']:
        path = ROOT/entry['path']
        require(path.stat().st_size == entry['bytes'], 'completed local density byte count changed')
        with path.open('rb') as handle:
            require(hashlib.file_digest(handle, 'sha256').hexdigest() == entry['sha256'], 'completed local density SHA changed')
        with path.open() as handle: report = json.load(handle)
        require(report['schema'] == density.SCHEMA+'/checked-curve' and
            report['source_record']['source_bindings'] == density._bindings() and
            report['untrusted_trial']['source_record'] == report['source_record'] and
            report['source_interval_seconds'] == receipt['source_interval_seconds'],
            'completed local density source, executable or clock changed')
        key = entry['side'], entry['factor_id']
        require(key not in reports, 'duplicate completed local density')
        density._CHECKED[density._digest(report)] = density._copy(report); reports[key] = report
    require(len(reports) == receipt['completed_local_certificate_count'] == 1, 'completed local density inventory changed')
    return reports
