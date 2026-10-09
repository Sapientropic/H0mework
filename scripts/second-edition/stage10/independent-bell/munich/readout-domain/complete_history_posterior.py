"""Original full observation -> whole-history CEM posterior, including its tail.

The finite CP event and unknown positive continuation share one event
normalizer.  The centre is a numerical coimage; the complete mother retains
every ready/receipt/time component and every unresolved continuation.
"""
from fractions import Fraction as Q
import hashlib
import importlib
import importlib.util

import all_ready_history_law as all_ready
import conditioned_window_history as old
import fluorescence_channel as channel
import joint_clock_observation as original
import joint_reload_source as reload
import projected_history_law as component
import projected_window_cem as projected
import stopped_history_law as stopped
import window_cem_source as window


SCHEMA = 'stage10-complete-history-observed-posterior/v1'


def _source_types():
    types=(all_ready.AllReadyHistoryLaw,stopped.StoppedHistoryLaw)
    if importlib.util.find_spec('recurrent_history_law') is not None:
        module=importlib.import_module('recurrent_history_law')
        named=getattr(module,'RecurrentHistoryLaw',None)
        if named is not None:
            types += (named,)
    return types


def reject_shadowed_source_methods(source):
    names={name for kind in type(source).__mro__ for name,member in vars(kind).items()
           if callable(getattr(member,'__func__',member)) or isinstance(member,property)}
    channel._require(not names.intersection(vars(source)), 'closed source methods cannot be replaced by instance callbacks')


def _observer_record(first,second,admitted):
    return {'histories':[{'run':h.run,'role':h.role,'observations':[list(row) for row in h.observations],
                         'paired_rows':sorted(h.paired_rows)} for h in (first,second)],
            'admitted':{'run':admitted.run,'trials':[[t.row,str(t.time_ms),t.h,t.a,t.b,t.x,t.y,t.row_a,t.row_b]
                        for t in admitted.trials], 'token_dictionaries':projected._copy(admitted.token_dictionaries),
                        'audit':projected._copy(admitted.audit)}}


def normalization_price(center_mass, center_norm, finite_error, positive_tail_upper):
    """Positive finite F plus positive unknown U, with Tr(U) <= T.

    Normalize F with its certified lower mass, then price the convex mixture
    with U.  Its mixing trace distance is at most 2T/(lo+T), including U=0.
    The numerical centre is not assumed positive.
    """
    mass, norm, error, tail = map(Q, (center_mass, center_norm, finite_error, positive_tail_upper))
    channel._require(error >= 0 and tail >= 0 and norm >= 0 and mass-error > 0,
                     'positive complete-event normalizer requires certified finite mass')
    lower = mass-error
    finite = error/lower+norm*error/(lower*mass)
    mixing = 2*tail/(lower+tail)
    return {'center':str(mass),'lower':str(lower),'upper':str(mass+error+tail),
            'finite_normalization_error':str(finite),'positive_tail_mixing_error':str(mixing),
            'posterior_trace_norm_error':str(finite+mixing)}


def _observer_signature(first, second, admitted):
    # The full observation and trial tuples contain only frozen rows/fields.
    # Their identity detects replacement without serializing the entire public
    # archive at each following source consumer; mutable dictionaries are read.
    return ((first.run,first.role,id(first.observations),first.paired_rows),
            (second.run,second.role,id(second.observations),second.paired_rows),
            (admitted.run,id(admitted.trials),channel._canonical(admitted.token_dictionaries),
             channel._canonical(admitted.audit)))


def _observation(first, second, admitted, pair_row, encoding):
    return old.decode_observation(first, second, admitted, pair_row, encoding)


def _norm(matrix):
    return projected.bsm._entry_norm(matrix)


class CompleteHistoryPosterior:
    def __init__(self, source, forecast, first, second, admitted, pair_row, *, encoding=old.Encoding()):
        channel._require(type(source) in _source_types(),
                         'closed whole-history source constructor required')
        channel._require(type(forecast) is dict, 'complete source-generated forecast required')
        reject_shadowed_source_methods(source)
        type(source).verify(source,forecast)
        rows,origin,settings,herald,clicks=_observation(first,second,admitted,pair_row,encoding)
        self.source=source
        self._first,self._second,self._admitted=first,second,admitted
        self._observer_seal=_observer_signature(first,second,admitted)
        self._source_seal=channel._canonical(source.record())
        self._hardware_seal=channel._canonical(source.hardware_record())
        self._code_seal=stopped._verification_code(source)
        self._source_operations=tuple(id(getattr(getattr(source,name),'__func__',getattr(source,name)))
                                      for name in ('verify','record','hardware_record'))
        self._forecast_reference=forecast
        self._forecast_seal=channel._canonical(forecast)
        self._forecast=projected._copy(forecast)
        self._forecast_sha256=hashlib.sha256(self._forecast_seal.encode()).hexdigest()
        selected_report=self._forecast['setting_reports'][component.SETTINGS.index(settings)]
        channel._require(tuple(selected_report['settings']) == settings and
                        selected_report['raw_window_source'] == source._window_source(settings).record(),
                        'observed settings must retain the same source-generated applied waveform')
        selected=component._selected(selected_report,herald,clicks)
        mass,rounding=projected._trace(selected)
        error=(Q(self._forecast['whole_receipt_measure']['global_trace_norm_error'])+
               Q(selected_report['window_local_error'])+
               Q(self._forecast['command_substitution_payments'][component.SETTINGS.index(settings)]))
        error += rounding
        tail_upper=Q(self._forecast['complete_pending_tail']['future_receipt_mass_upper'])
        price=normalization_price(mass,_norm(selected),error,tail_upper)
        self._normalized={key:value*(1/mass) for key,value in selected.items()}
        channel._require(all((projected.occupancy(i) == projected.occupancy(j)) for i,j in self._normalized),
                         'terminal CEM coimage must preserve neutral/Empty block algebra')
        raw_window=selected_report['raw_window_source']
        response_end=Q(raw_window['interval_start'])+Q(raw_window['duration'])
        finite_branches=[]
        for packet in selected_report['packets']:
            if packet['physical_herald'] != herald:
                continue
            marked={key:value for key,value in window._read_marked(packet['complete_marked_matrix']).items()
                    if key[0].clicks == clicks}
            finite_branches.append({'pattern_index':packet['pattern_index'],
                    'entering_occupancy':packet['entering_occupancy'],
                    'complete_selected_marked_matrix':window._marked_record(window._initial_marked(marked))})
        self._value={'schema':SCHEMA,'whole_source_record':projected._copy(source.record()),
            'hardware_record':projected._copy(source.hardware_record()),
            'source_forecast':self._forecast,'forecast_sha256':self._forecast_sha256,
            'raw_encoding':encoding.record(),'original_pair':list(origin),
            'original_observer_record':_observer_record(first,second,admitted),
            'original_rows':[list(row) for row in rows],'physical_settings':list(settings),
            'physical_herald':herald,'physical_clicks':list(clicks),
            'finite_selected_matrix':channel._input_record(selected),
            'normalized_center':channel._input_record(self._normalized),
            'finite_event_trace_norm_error':str(error),'unknown_positive_selected_tail_upper':str(tail_upper),
            'normalizer':price,'finite_selected_branches':finite_branches,
            'time_state_mother_record':{
                'whole_source_record':projected._copy(source.record()),'forecast_sha256':self._forecast_sha256,
                'finite_component_addresses':self._forecast['whole_receipt_measure']['component_addresses'],
                'complete_pending_tail':self._forecast['complete_pending_tail'],
                'common_response_end_shift':str(response_end),
                'selected_raw_response_source':raw_window,
                'source_relative_start_is_actual_clock':False,
                'time_law': 'original full source spectra followed by common receipt-relative CP response; tail remains unresolved',
                'normalization': 'one whole observed-event normalizer; finite subintervals are not re-normalized'},
            'whole_event_normalizer_generated_from_source':True,
            'all_native_ready_components_consumed':bool(self._forecast.get('all_native_ready_components_consumed')),
            'all_original_receipt_components_consumed':True,
            'unknown_positive_tail_conditioning_retained':True,
            'numerical_center_PSD_certified':False,'literal_cohort_reconstructed':False,
            'complete_record_clock_square_certified':False,'actual_hardware_uniquely_identified':False,
            'controller_advance':False}
        self._record_seal=channel._canonical(self._value)
        self._matrix_seal=channel._canonical(channel._input_record(self._normalized))

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA,
                         'original complete conditioned source record required')
        raw_source=record['whole_source_record']
        source_class=next((kind for kind in _source_types()
                           if raw_source.get('schema') == importlib.import_module(kind.__module__).SCHEMA),None)
        channel._require(source_class is not None,'closed named posterior source required')
        source=source_class.from_record(raw_source)
        observers=record['original_observer_record']
        first,second=tuple(original.history.RecordHistory(h['run'],h['role'],tuple(tuple(row) for row in h['observations']),
                                frozenset(h['paired_rows'])) for h in observers['histories'])
        raw=observers['admitted']
        trials=tuple(original.history.schema.Trial(t[0],Q(t[1]),*t[2:]) for t in raw['trials'])
        admitted=original.history.schema.AdmittedRun(raw['run'],trials,raw['token_dictionaries'],raw['audit'])
        encoding=record['raw_encoding']
        decoded=old.Encoding(tuple(encoding['click_tokens']),tuple(encoding['setting_zero_tokens']),tuple(encoding['herald_labels']))
        result=cls(source,record['source_forecast'],first,second,admitted,record['original_pair'][1],encoding=decoded)
        channel._require(result.record() == record,'whole posterior mother, observation or normalizer changed')
        return result

    @property
    def original_pair(self):
        return tuple(self._value['original_pair'])

    @property
    def original_rows(self):
        return tuple(tuple(row) for row in self._value['original_rows'])

    @property
    def physical_settings(self):
        return tuple(self._value['physical_settings'])

    @property
    def physical_herald(self):
        return self._value['physical_herald']

    @property
    def physical_clicks(self):
        return tuple(self._value['physical_clicks'])

    @property
    def normalized_poststate(self):
        self.verify()
        return dict(self._normalized)

    @property
    def trace_norm_error(self):
        self.verify()
        return Q(self._value['normalizer']['posterior_trace_norm_error'])

    def verify(self):
        channel._require(type(self.source) in _source_types(),
                         'same closed whole-history source required')
        reject_shadowed_source_methods(self.source)
        channel._require(channel._canonical(self.source.record()) == self._source_seal and
                        channel._canonical(self.source.hardware_record()) == self._hardware_seal,
                        'whole source or shared hardware changed after posterior construction')
        operations=tuple(id(getattr(getattr(self.source,name),'__func__',getattr(self.source,name)))
                         for name in ('verify','record','hardware_record'))
        channel._require(stopped._verification_code(self.source) == self._code_seal and operations == self._source_operations,
                         'source checker or source operations changed')
        channel._require(channel._canonical(self._forecast_reference) == self._forecast_seal and
                        channel._canonical(self._forecast) == self._forecast_seal,
                        'whole forecast alias or mother spectrum changed')
        channel._require(_observer_signature(self._first,self._second,self._admitted) == self._observer_seal,
                         'original full observer or admitted dictionary changed')
        channel._require(channel._canonical(self._value) == self._record_seal and
                        channel._canonical(channel._input_record(self._normalized)) == self._matrix_seal,
                        'generated posterior, normalizer or complete centre changed')
        return True

    def record(self):
        self.verify()
        return projected._copy(self._value)

    def next_reload_input(self, source):
        self.verify()
        channel._require(type(source) is reload.JointReloadSource, 'closed original joint reload source required')
        source=reload.JointReloadSource.from_record(source.record())
        raw_parent=self._value['hardware_record']['raw_reload']['raw_source']
        channel._require(source.record() == raw_parent, 'next reload must use the same mother raw hardware')
        state={(0,0,i,j):value for (i,j),value in self._normalized.items()}
        source._projected_blocks(state)
        return {'state':state,'upstream_trace_norm_error':Q(self._value['normalizer']['posterior_trace_norm_error']),
                'source_posterior':self,'original_pair':self.original_pair,'original_rows':self.original_rows,
                'time_state_mother_record':projected._copy(self._value['time_state_mother_record']),
                'source_relative_start':Q(self._value['time_state_mother_record']['common_response_end_shift']),
                'window_end_relative_to_receipt':Q(self._value['time_state_mother_record']['common_response_end_shift']),
                'seconds_per_source_unit':Q(self._value['time_state_mother_record']['selected_raw_response_source']['seconds_per_unit']),
                'raw_reload_source':source.record(),'whole_event_normalizer':projected._copy(self._value['normalizer']),
                'unknown_positive_tail_conditioning_retained':True,'complete_poststate_consumed':True,
                'literal_cohort_reconstructed':False,'source_relative_start_is_actual_clock':False,
                'complete_record_clock_square_certified':False,'actual_hardware_uniquely_identified':False}
