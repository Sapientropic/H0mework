"""Stream a complete Chebyshev curve through its original closed density source."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import json
import time

import chebyshev_density_rha0032 as core
import chebyshev_basis_independent_rha0032 as independent
import chebyshev_density_integer_rha0032_1 as integer

density = core.density


def certify(source, initial, start, stop, path, output, *, coefficient_bits=192, envelope_order=20, progress=None, strategy="integer"):
    core.require(strategy in ("integer", "rational"), "registered explicit residual arithmetic required")
    density._CHECK(); core.require(type(source) is density.GaussianLocalDensitySource,
                                 'the complete original closed density source is required')
    raw = source.record(); source_sha = core.digest(raw)
    start, stop = map(Q, (start, stop)); path, output = Path(path), Path(output)
    core.require(start < stop and type(envelope_order) is int and 0 <= envelope_order <= 32,
                 'positive source interval and registered Gaussian order required')
    output.mkdir(parents=True, exist_ok=False)
    basis = independent.check(core.derivative_weights, core.product_weights, 2*envelope_order, 64)
    with path.open('rb') as handle: witness_sha = hashlib.file_digest(handle, 'sha256').hexdigest()
    started = time.monotonic(); records = []; elapsed = start
    with gzip.open(path, 'rt') as handle:
        header = json.loads(next(handle)); mode_bits = header['mode_bits']
        core.require(header['schema'] == core.SCHEMA+'/untrusted-stream' and header['writer_correctness_assumed'] is False and
            header['source_record_sha256'] == source_sha and
            header['initial_matrix_sha256'] == core.digest(density.channel._input_record(initial)) and
            header['source_interval_seconds'] == list(map(str, (start, stop))) and
            type(header['piece_count']) is int and header['piece_count'] > 0 and header['curve_degree'] <= 64,
            'untrusted Chebyshev source, factor, interval or complete inventory changed')
        original, current, error = density._rotating_initial(raw['Gaussian_source'], initial, start, mode_bits)
        norm = density.fourier.bsm._entry_norm(original, bits=coefficient_bits)
        columns = density._Columns(raw['Gaussian_source'], coefficient_bits)
        for index, line in enumerate(handle):
            core.require(index < header['piece_count'], 'extra free-flow piece')
            width, current, price, record = (integer.piece if strategy == "integer" else core.piece)(columns, raw['Gaussian_source'], json.loads(line), current,
                                                      elapsed, mode_bits, envelope_order)
            elapsed += width; error += price; core.require(elapsed <= stop, 'curve exceeded its exact retarded source endpoint')
            records.append(record)
            checkpoint = {'piece': index+1, 'original_source_sha256': source_sha, 'witness_sha256': witness_sha,
                'checked_through_seconds': str(elapsed), 'rotating_endpoint': [[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(current.items())],
                'cumulative_new_curve_error': str(density.field._price_upper(error, coefficient_bits)), 'piece_record': record}
            with (output/f'piece-{index+1:04d}.json').open('x') as saved: json.dump(checkpoint, saved, sort_keys=True); saved.write('\n')
            if progress is not None:
                progress({'piece': index+1, 'pieces': header['piece_count'], 'new_curve_error_upper': float(error),
                          'seconds': time.monotonic()-started})
        core.require(len(records) == header['piece_count'] and elapsed == stop, 'the complete source interval was not checked')
    physical, phase = density._frame(raw['Gaussian_source'], current, stop, coefficient_bits)
    source_raw = raw['Gaussian_source']; gamma = Q(source_raw['reference_clock']['Gamma_numerical_centre'])
    lo, hi = map(Q, source_raw['reference_clock']['angular_Gamma_enclosure_per_second'])
    gamma_price = norm*(2*density.gaussian.GaussianAtomicPulseSource.Gamma_math_price(source._pulse, start, stop, bits=coefficient_bits)+
        max(abs(gamma-lo), abs(hi-gamma))/gamma*(stop-start)*density.gaussian._norm(
            density.gaussian._matrix(source_raw['complete_natural_R_per_second']), coefficient_bits))
    total = error+phase+gamma_price
    report = {'schema': core.SCHEMA+'/checked-stream/rha0032.1', 'original_density_source': raw,
        'untrusted_stream': {'bytes': path.stat().st_size, 'sha256': witness_sha}, 'stream_header': header,
        'independent_finite_basis_check': basis, 'source_interval_seconds': list(map(str, (start, stop))),
        'complete_physical_endpoint': density.channel._input_record({key: density.dipole.ComplexRadical(*v) for key, v in physical.items()}),
        'piece_count': len(records), 'source_curve_residual_error': str(density.field._price_upper(error, coefficient_bits)),
        'physical_frame_price': str(density.field._price_upper(phase, coefficient_bits)),
        'mathematical_Gamma_price': str(density.field._price_upper(gamma_price, coefficient_bits)),
        'whole_new_trace_norm_error': str(density.field._price_upper(total, coefficient_bits)),
        'initial_entry_norm_upper': str(norm), 'registered_relative_accuracy': '1/100000000',
        'registered_relative_accuracy_passed': total <= norm*Q(1, 100000000),
        'old_inlet_error_reapplied_per_factor': False, 'Hermitian_CPTP_contraction_used': True,
        'full_atomic_coordinates_and_natural_recycling_kept': True, 'source_column_count': len(columns.cache),
        'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False,
        'residual_arithmetic': strategy, 'controller_advance': False, 'seconds': time.monotonic()-started}
    with (output/'checked-curve.json').open('x') as handle: json.dump(report, handle, sort_keys=True); handle.write('\n')
    return report
