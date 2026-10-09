"""The original two-pump factors reach the fixed retarded gate cut.

Each complete local density certificate consumes its actual issued factor.
The product of the two independent CPTP flows transports the old joint error
once.  The original time, pump field and rolling queue mother is retained.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import prepared_gaussian_field_source as prepared
import retarded_gaussian_bsm_source as retarded
import gaussian_local_density_source as density

field, dipole, full, channel, joint, bsm = (retarded.field, retarded.dipole, retarded.full,
                                          retarded.channel, retarded.joint, retarded.bsm)
SCHEMA = 'stage10-source-issued-retarded-Gaussian-gate-inlet/v1'
_ISSUED = {}
_PREPARED_CHECK, _RETARDED_CHECK, _DENSITY_CHECK = prepared._CHECK, retarded._CHECK, density._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (prepared, retarded, density, prepared.programme.factors,
                                                     field, dipole, full, channel, joint, bsm)))}


def _freeze(terms):
    return tuple((tuple(sorted(a.items())), tuple(sorted(b.items()))) for a,b in terms)


def _tensor_price(a, b, ea, eb, bits):
    return prepared.programme.factors._tensor_price(a, b, ea, eb, bits)


class PreparedRetardedGaussianInlet:
    def __init__(self, source, law, local_density_certificates, *, bits=192):
        _CHECK(); field._closed(source); field._closed(law)
        _require(type(source) is prepared.PreparedGaussianFieldSource and
                 type(law) is retarded.RetardedGaussianBSMSource and law._field is source._field,
                 'original source-issued pumps and the very same driven field detector law required')
        density.gaussian._precision(bits)
        raw = prepared.PreparedGaussianFieldSource.record(source)
        gate = retarded.RetardedGaussianBSMSource.record(law)
        tensors = prepared.PreparedGaussianFieldSource.source_tensors(source)
        g0 = Q(gate['gate_seconds'][0]); cuts = retarded.RetardedGaussianBSMSource.local_times(law, g0)
        _require(all(t >= 0 for t in cuts), 'both actual retarded gate cuts must follow their source pump prefixes')
        _require(type(local_density_certificates) in (tuple,list) and len(local_density_certificates) == 2,
                 'both complete source-factor density inventories required')
        endpoints = [{}, {}]; checked_records = []; local_sources = []
        for side, rows in enumerate(local_density_certificates):
            original = raw['source_issued_two_pump_factor_inlets'][side]
            _require(type(rows) in (tuple,list) and [r.get('factor_id') for r in rows] == [r['factor_id'] for r in original],
                     'every original source factor must reach its own exact retarded cut')
            local = density.GaussianLocalDensitySource(source._field._pulses[side]); local_sources.append(local)
            records = []
            for item, parent in zip(rows, original):
                _require(type(item) is dict and set(item) == {'factor_id','complete_density_certificate'},
                         'original factor identity and full density witness required')
                certificate = item['complete_density_certificate']
                _require(type(certificate) is dict and certificate.get('schema') == density.SCHEMA+'/checked-curve',
                         'complete source density certificate required; an endpoint is not a witness')
                trial = certificate['untrusted_trial']; old = parent['source_issued_next_phase']
                _require(trial['complete_initial_matrix'] == old['complete_initial_local_factor'] and
                         Q(trial['start_seconds']) == 0 and Q(trial['stop_seconds']) == cuts[side] and
                         Q(certificate['input_trace_norm_error']) == 0,
                         'density flow must consume the actual pump factor and cut; whole prefix error is paid once')
                verified = density.GaussianLocalDensitySource.verify(local, certificate)
                matrix = channel._read_input(verified['complete_physical_endpoint'], full.DIMENSION)
                endpoints[side][item['factor_id']] = matrix, Q(verified['whole_trace_norm_error'])
                records.append({'factor_id':item['factor_id'], 'density_certificate_digest':_digest(certificate),
                    'complete_retarded_local_endpoint':verified['complete_physical_endpoint'],
                    'new_local_trace_norm_error':verified['whole_trace_norm_error']})
            checked_records.append(records)
        terms = []; payments = []; new_error = Q(0)
        for left, right in raw['source_tensor_factor_ids']:
            a, ea = endpoints[0][left]; b, eb = endpoints[1][right]
            price, na, nb = _tensor_price(a, b, ea, eb, bits)
            new_error += price; terms.append((a,b))
            payments.append({'source_factor_ids':[left,right], 'new_local_errors':list(map(str,(ea,eb))),
                'complete_endpoint_norms':list(map(str,(na,nb))), 'new_tensor_price':str(field._price_upper(price,bits))})
        old_error = Q(tensors['whole_upstream_trace_norm_error']); error = old_error+new_error
        self._prepared, self._law, self._sources = source, law, tuple(local_sources)
        self._terms = _freeze(terms)
        self._witnesses = channel._canonical(local_density_certificates)
        self._value = {'schema':SCHEMA, 'source_issued_two_pump_source':raw, 'retarded_detector_law':gate,
            'fixed_detector_gate_start_seconds':str(g0), 'actual_retarded_local_cuts_seconds':list(map(str,cuts)),
            'retarded_atom_physical_cuts_seconds':[str(g0-Q(f)) for f in gate['complete_driven_field_source']['flight_seconds']],
            'source_factor_ids':raw['source_tensor_factor_ids'], 'checked_local_density_inventories':checked_records,
            'whole_prefix_trace_norm_error_once':str(old_error),
            'new_complete_tensor_trace_norm_error':str(field._price_upper(new_error,bits)),
            'whole_retarded_gate_input_error':str(field._price_upper(error,bits)), 'source_tensor_payments':payments,
            'source_positive_mass_upper':tensors['source_record']['source_positive_mass_upper'],
            'source_centre_trace_norm_upper':str(field._price_upper(Q(tensors['source_positive_mass_upper'])+error,bits)),
            'retained_pump_field_and_queue_mother':_copy(tensors['time_state_mother']),
            'native_pending_poststate':raw['native_pending_poststate'],
            'density_certificate_inventory_sha256':_digest(local_density_certificates),
            'retarded_coimage_is_actual_detector_time_atom':False,
            'source_scope':'two-pump atomic marginal transported to both retarded cuts; original open-loop BSM inlet',
            'pre_gate_nonzero_evolution_replaced_by_I':False, 'old_prefix_error_paid_per_factor':False,
            'rolling_APD_queue_reset':False, 'controller_advance':False, 'scalar_bits':bits,
            'source_bindings':_bindings()}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, self._terms, self._witnesses, self._sources

    def record(self):
        _CHECK(); field._closed(self)
        owned = _ISSUED.get(id(self))
        _require(type(self) is PreparedRetardedGaussianInlet and set(vars(self)) ==
            {'_prepared','_law','_sources','_terms','_witnesses','_value','_seal'} and owned is not None and
            self._seal == owned[0] and self._terms is owned[1] and self._witnesses is owned[2] and self._sources is owned[3] and
            self._value['source_bindings'] == _bindings() and _digest(self._value) == self._seal and
            prepared.PreparedGaussianFieldSource.record(self._prepared) == self._value['source_issued_two_pump_source'] and
            retarded.RetardedGaussianBSMSource.record(self._law) == self._value['retarded_detector_law'] and
            all(density.GaussianLocalDensitySource.record(s)['Gaussian_source'] == raw for s,raw in
                zip(self._sources,self._value['retarded_detector_law']['complete_driven_field_source']['Gaussian_source_legs'])),
            'original pumps, complete retarded cuts, density witnesses or retained time mother changed')
        return _copy(self._value)

    def source_tensors(self):
        raw = PreparedRetardedGaussianInlet.record(self)
        return {'source_record':raw, 'tensor_terms':tuple((dict(a),dict(b)) for a,b in self._terms),
            'whole_upstream_trace_norm_error':Q(raw['whole_retarded_gate_input_error']),
            'retained_time_state_mother':raw['retained_pump_field_and_queue_mother'],
            'actual_retarded_local_cuts_seconds':tuple(map(Q,raw['actual_retarded_local_cuts_seconds']))}

    def complete_pending_initial(self):
        raw = PreparedRetardedGaussianInlet.record(self); result = {}
        for a,b in PreparedRetardedGaussianInlet.source_tensors(self)['tensor_terms']:
            field._add(result, prepared.tensor._tensor(a,b))
        return {'source_record':raw, 'complete_pending_state':{(bsm.INITIAL,i,j):v for (i,j),v in result.items()},
            'whole_upstream_trace_norm_error':Q(raw['whole_retarded_gate_input_error']),
            'retained_time_state_mother':raw['retained_pump_field_and_queue_mother']}


def _function(value):
    value = getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers = (_require,_copy,_digest,_bindings,_freeze,_tensor_price,_function,_signature,_check,
        prepared.PreparedGaussianFieldSource.record,prepared.PreparedGaussianFieldSource.source_tensors,
        retarded.RetardedGaussianBSMSource.record,retarded.RetardedGaussianBSMSource.local_times,
        density.GaussianLocalDensitySource.record,density.GaussianLocalDensitySource.verify,
        prepared.programme.factors._tensor_price,prepared.tensor._tensor,
        field._closed,field._price_upper,field._add,channel._read_input)
    methods = tuple(_function(v) for v in vars(PreparedRetardedGaussianInlet).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA,bsm.INITIAL


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        prepared._CHECK is _PREPARED_CHECK and retarded._CHECK is _RETARDED_CHECK and density._CHECK is _DENSITY_CHECK,
        'source-issued retarded Gaussian inlet execution changed')
    _PREPARED_CHECK(); _RETARDED_CHECK(); _DENSITY_CHECK()


_CHECK,_SIGNATURE = _check,_signature
_EXPECTED = _signature()
