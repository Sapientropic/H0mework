"""Source operation invariants generate exact matter and outcome coimages.

Accepted ion birth and background OR have different matter actions.  The
complete native vacancy source with zero capture remains on its discovered
ray through every control/history branch, including the unexpanded tail.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import complete_history_posterior as complete
import fluorescence_channel as channel
import projected_window_cem as projected
import window_cem_source as window


SCHEMA='stage10-source-window-posterior-support/v1'
EMPTY_PAIR=33*dipole.ION+dipole.ION


def whole_source_ray_certificate(source):
    """Recover the initial ray, then check every source-owned operation."""
    channel._require(type(source) in complete._source_types(),'closed whole instrument source required')
    complete.reject_shadowed_source_methods(source)
    mother=source.component.mother
    parent=mother.parent_report
    raw_reload=projected.reload.JointReloadSource.from_record(mother.parent_programme_record['raw_source'])
    native=raw_reload.intake(projected.reload_programme._read_coarsened(parent['original_coarsened_input']))
    coordinates={(i,j) for (_,_,i,j),value in native.items() if value}
    if len(coordinates) != 1 or next(iter(coordinates))[0] != next(iter(coordinates))[1]:
        return {'generated':False,'obstruction':'original source input is not a single diagonal ray'}
    index=next(iter(coordinates))[0]
    if index != EMPTY_PAIR or any(any(h.occupied for h in history.traps) for history,_,_,_ in native):
        return {'generated':False,'obstruction':'original source ray is not two source-vacant traps'}
    for capture in raw_reload.captures:
        if capture.first_birth_rate or any(capture.birth_operators.values()):
            return {'generated':False,'obstruction':'raw capture regenerates matter from the original vacancy'}
    ray={(index,index):dipole.ComplexRadical(1)}
    reload_checks=[]
    for stage in range(projected.reload.READY):
        generator=raw_reload._window(stage)
        for atom in generator.sources:
            if atom.atomic_action({(dipole.ION,dipole.ION):dipole.ComplexRadical(1)}):
                return {'generated':False,'obstruction':'raw reload atom bath moves the source vacancy ray'}
        for counter in range(generator.threshold+1):
            action=raw_reload.window_action({(counter,index,index):dipole.ComplexRadical(1)},stage)
            if any((i,j) != (index,index) for _,i,j in action):
                return {'generated':False,'obstruction':'raw stage/count action changes the source ray'}
        reload_checks.append({'stage':stage,'counter_columns_checked':generator.threshold+1,
                              'raw_window':generator.record(),'capture_enabled':list(projected.reload.CAPTURE_AT[stage])})
    components=getattr(source,'components',(source,))
    bsm_checks=[]
    for item in components:
        ingress=getattr(item,'ingress',None)
        if ingress is None:
            # A recurrent source keeps all earlier occurrences in its parent;
            # its local burst records must satisfy the same source invariant.
            ingresses=getattr(item,'ingresses',())
        else:
            ingresses=(ingress,)
        if not ingresses:
            return {'generated':False,'obstruction':'complete source-owned burst inventory unavailable'}
        for ingress in ingresses:
            burst=projected._burst(ingress['raw_burst'],ingress['multitone_bits'])
            invariant=projected.bsm_occupancy_certificate(burst.gate)
            phases=burst.preparation+burst.excitation+burst.arrival_delay+burst.return_phases+burst.recooling
            for phase in phases:
                for atom in (projected.joint._source(phase.first),projected.joint._source(phase.second)):
                    if atom.atomic_action({(dipole.ION,dipole.ION):dipole.ComplexRadical(1)}):
                        return {'generated':False,'obstruction':'raw complete burst phase changes the recovered ray'}
            for port in range(4):
                expected={key:value*burst.gate.background_rates[port] for key,value in ray.items()
                          if burst.gate.background_rates[port]}
                if burst.gate.port_action(ray,port) != expected:
                    return {'generated':False,'obstruction':'raw physical APD changes matter on the source ray'}
            bsm_checks.append({'raw_burst':burst.record(),'occupancy_certificate':invariant,
                               'raw_phase_pairs_checked':len(phases),'physical_APD_ports_checked':4,
                               'background_quantum_action':'identity on the discovered source ray'})
    windows=[]
    for settings in complete.component.SETTINGS:
        window_source=source._window_source(settings)
        proof=source_support_certificate(window_source)
        for phase in window_source.phases():
            for side in (0,1):
                if phase.ion_birth_action(ray,side):
                    return {'generated':False,'obstruction':'raw response creates an ion birth from the source ray'}
            for mark in window.MARKS:
                if phase.action({(mark,index,index):dipole.ComplexRadical(1)}):
                    return {'generated':False,'obstruction':'raw response phase moves the discovered source ray'}
        for mark in window.MARKS:
            OR=window_source.background_action({(mark,index,index):dipole.ComplexRadical(1)})
            if any((i,j) != (index,index) for _,i,j in OR):
                return {'generated':False,'obstruction':'raw CEM background OR moves matter'}
        expected={}
        for clicks in window.REGISTRATION_ORDER:
            weight=Q(1)
            for bit,background in zip(clicks,window_source.backgrounds):
                weight *= background if bit else 1-background
            if weight:
                expected[window.Mark(clicks),index,index]=dipole.ComplexRadical(weight)
        if window_source.background_action({(window.INITIAL,index,index):dipole.ComplexRadical(1)}) != expected:
            return {'generated':False,'obstruction':'raw unmarked background OR is not its source Bernoulli product'}
        windows.append({'settings':list(settings),'raw_window_support':proof,
                        'all_original_Mark_columns_preserve_discovered_ray':True,
                        'all_source_ion_birth_fluxes_zero_on_discovered_ray':True,
                        'initial_Mark_before_background_OR':list(window.INITIAL.clicks),
                        'raw_backgrounds':list(map(str,window_source.backgrounds)),
                        'raw_background_OR_product_checked':True})
    return {'generated':True,'initial_native_source_groups':parent['original_coarsened_input'],
            'discovered_ray_basis_index':index,'raw_reload_source':raw_reload.record(),
            'source_capture_birth_operators_all_zero':True,'reload_stage_inventory':reload_checks,
            'complete_BSM_inventory':bsm_checks,'all_nominal_window_sources':windows,
            'closure':'every raw source operation preserves the same ray; observations restrict scalar mass only',
            'whole_unknown_future_tail_in_same_ray':True,'target_ray_supplied':False,
            'literal_cohort_reconstructed':False,'actual_hardware_point_member_certified':False}


def source_support_certificate(source):
    channel._require(type(source) is window.WindowCEMSource,'closed raw window-CEM source required')
    source=window.WindowCEMSource.from_record(source.record())
    phases=[]
    for phase in source.phases():
        sides=[]
        for side,atom in enumerate(phase.sources):
            h_count=projected._commutes_empty(atom.hamiltonian)
            jumps=sum(projected._commutes_empty(jump.matrix) for jump in atom.jumps)
            channel._require(atom.outgoing[dipole.ION] == 0 and
                            atom.atomic_action({(dipole.ION,dipole.ION):dipole.ComplexRadical(1)}) == {},
                            'original terminal ION axis must be absorbing')
            rates=phase.ion_rates[side]
            channel._require(all(index != dipole.ION and rate >= 0 for index,rate in rates.items()),
                             'original ion-birth source cannot start at ION')
            channel._require(Q(0) <= phase.kappas[side] <= Q(1), 'raw registration must generate a legal birth split')
            checked=0
            # The original birth source is a local rank-one jump tensored with
            # the identity on the other atom.  Check every local matrix unit;
            # both the tensor address and the other atom are retained.
            for i in range(33):
                for j in range(33):
                    row,column=(33*i+1,33*j+2) if side == 0 else (33+i,66+j)
                    actual=phase.ion_birth_action({(row,column):dipole.ComplexRadical(1)},side)
                    rate=rates.get(i,Q(0)) if i == j else Q(0)
                    target=(33*dipole.ION+1,33*dipole.ION+2) if side == 0 else (33+dipole.ION,66+dipole.ION)
                    expected={target:dipole.ComplexRadical(rate)} if rate else {}
                    channel._require(actual == expected,'original full local ion-birth column changed')
                    checked += 1
            mark_count=0
            for mark in window.MARKS:
                target=mark.with_click(side)
                channel._require(target.clicks[side] == 1 and target.clicks[1-side] == mark.clicks[1-side],
                                 'source ion birth must set only its own retained seen bit')
                mark_count += 1
            sides.append({'side':side,'Hamiltonian_entries_checked':h_count,
                          'natural_jump_entries_checked':jumps,'natural_jump_operators_checked':len(atom.jumps),
                          'local_birth_matrix_units_checked':checked,'original_Mark_targets_checked':mark_count,
                          'kappa':str(phase.kappas[side]),'ION_axis_absorbing':True})
        phases.append({'raw_phase':phase.record(),'sides':sides})
    # OR is the only remaining seen-bit producer.  Reconstruct every branch
    # from the raw Bernoulli fields rather than assuming a no-background flag.
    OR_checks=[]
    for side,background in enumerate(source.backgrounds):
        checked=0
        for mark in window.MARKS:
            for noise in window.REGISTRATION_ORDER:
                weight=Q(1)
                for bit,p in zip(noise,source.backgrounds):
                    weight *= p if bit else 1-p
                target=window.Mark(tuple(int(bool(a or b)) for a,b in zip(mark.clicks,noise)))
                if background == 0 and weight:
                    channel._require(not (not mark.clicks[side] and target.clicks[side]),
                                     'zero-background OR cannot create an observed click')
                checked += 1
        OR_checks.append({'side':side,'raw_background':str(background),'OR_branches_checked':checked,
                          'observed_click_implies_terminal_ION':background == 0})
    return {'schema':SCHEMA,'raw_window_source':source.record(),'phase_inventory':phases,'background_OR':OR_checks,
            'initial_mark':list(window.INITIAL.clicks),
            'source_generated_invariant':'seen_s=1 implies both quantum addresses on original ION_s',
            'full_marked_block_algebra':'initial unmarked full33 pair; birth flux into ION; retained Mark; absorbing source',
            'target_support_supplied':False,'actual_hardware_slice_identified':False,
            'literal_cohort_reconstructed':False,'controller_advance':False}


def verify_source_support_certificate(report,source):
    channel._require(type(report) is dict and report == source_support_certificate(source),
                     'same original window source support certificate required')
    return True


class SupportedHistoryPosterior:
    def __init__(self,posterior):
        channel._require(type(posterior) is complete.CompleteHistoryPosterior,
                         'original closed complete-history posterior required')
        complete.CompleteHistoryPosterior.verify(posterior)
        self.posterior,self.source=posterior,posterior.source
        self._parent_record=complete.CompleteHistoryPosterior.record(posterior)
        settings=posterior.physical_settings
        raw=self.source._window_source(settings)
        self._proof=source_support_certificate(raw)
        self._whole_proof=whole_source_ray_certificate(self.source)
        clicks=posterior.physical_clicks
        forced=tuple(clicks[side] == 1 and raw.backgrounds[side] == 0 for side in (0,1))
        self._exact=all(forced) or self._whole_proof['generated']
        # Normalizer positivity remains the original whole-event obligation;
        # support narrowing cannot turn a zero-probability condition into one.
        channel._require(Q(self._parent_record['normalizer']['lower']) > 0,
                         'original observed-event normalizer must remain certified positive')
        self._state=({(EMPTY_PAIR,EMPTY_PAIR):dipole.ComplexRadical(1)} if self._exact else
                     complete.CompleteHistoryPosterior.normalized_poststate.fget(posterior))
        self._error=Q(0) if self._exact else complete.CompleteHistoryPosterior.trace_norm_error.fget(posterior)
        self._value={'schema':SCHEMA,'complete_parent_posterior':self._parent_record,'source_support_proof':self._proof,
                    'whole_source_ray_proof':self._whole_proof,
                    'forced_terminal_ION_sides':list(forced),'normalized_coimage':channel._input_record(self._state),
                    'trace_norm_error':str(self._error),'exact_rank_one_coimage_generated':self._exact,
                    'unknown_positive_tail_covered_by_same_window_source_invariant':self._exact,
                    'unresolved_time_state_mother':self._parent_record['time_state_mother_record'],
                    'parent_unknown_tail_and_price_retained':True,'source_normalizer_replaced':False,
                    'literal_cohort_reconstructed':False,'actual_hardware_slice_identified':False,
                    'actual_hardware_uniquely_identified':False,'controller_advance':False}
        self._seal=channel._canonical(self._value)
        self._matrix_seal=channel._canonical(channel._input_record(self._state))

    @property
    def normalized_poststate(self):
        self.verify()
        return dict(self._state)

    @property
    def trace_norm_error(self):
        self.verify()
        return self._error

    def verify(self):
        channel._require(self._whole_proof == self._value['whole_source_ray_proof'] and
                        self._proof == self._value['source_support_proof'],
                        'source support proof attributes must match the sealed source fields')
        complete.CompleteHistoryPosterior.verify(self.posterior)
        channel._require(complete.CompleteHistoryPosterior.record(self.posterior) == self._parent_record and
                        self.source is self.posterior.source,'same observed parent and source required')
        raw=self.source._window_source(self.posterior.physical_settings)
        channel._require(raw.record() == self._proof['raw_window_source'], 'raw support-generating hardware changed')
        channel._require(channel._canonical(self._value) == self._seal and
                        channel._canonical(channel._input_record(self._state)) == self._matrix_seal,
                        'source-generated coimage or support certificate changed')
        channel._require(self._error == Q(self._value['trace_norm_error']) and
                        self._exact == self._value['exact_rank_one_coimage_generated'],
                        'source-supported error or exactness changed')
        return True

    def record(self):
        self.verify()
        return projected._copy(self._value)

    def exact_outcome_law(self):
        """All source times -> exact conditional q before an outcome is chosen."""
        SupportedHistoryPosterior.verify(self)
        channel._require(self._whole_proof['generated'],
                         'complete source-operation ray invariant required for an exact future outcome law')
        normalizers=self._parent_record['source_forecast']['finite_herald_normalizers']
        channel._require(len(normalizers) == len(complete.component.HERALDS),
                         'both original source herald normalizers required')
        positive=[]
        for herald,item in zip(complete.component.HERALDS,normalizers):
            center,error=Q(item['center']),Q(item['error'])
            channel._require(error >= 0 and center-error > 0,
                             'original source herald normalizer must remain certified positive')
            positive.append({'physical_herald':herald,'finite_center':str(center),
                             'source_error':str(error),'strict_lower':str(center-error)})
        rows=[]
        for proof in self._whole_proof['all_nominal_window_sources']:
            settings=proof['settings']
            backgrounds=tuple(map(Q,proof['raw_backgrounds']))
            channel._require(proof['all_source_ion_birth_fluxes_zero_on_discovered_ray'] and
                             proof['raw_background_OR_product_checked'] and
                             proof['initial_Mark_before_background_OR'] == [0,0],
                             'unmarked raw response must preserve the complete source ray until background OR')
            for h in range(len(complete.component.HERALDS)):
                for clicks in window.REGISTRATION_ORDER:
                    probability=Q(1)
                    for bit,background in zip(clicks,backgrounds):
                        probability *= background if bit else 1-background
                    rows.append({'h':h,'a':settings[0],'b':settings[1],
                                 'x':clicks[0],'y':clicks[1],
                                 'probability_interval':[str(probability),str(probability)]})
        rows.sort(key=lambda row:tuple(row[k] for k in ('h','a','b','x','y')))
        table=complete.component.ProjectedHistoryLaw._table(rows)
        channel._require(len(rows) == 32 and len(table) == 8,
                         'complete physical herald/setting/outcome inventory required')
        return {'schema':'stage10-source-ray-exact-outcome-law/v1',
                'whole_source_record':projected._copy(self._parent_record['whole_source_record']),
                'raw_hardware_model':projected._copy(self._parent_record['hardware_record']),
                'source_forecast_sha256':self._parent_record['forecast_sha256'],
                'whole_source_ray_proof':projected._copy(self._whole_proof),
                'source_positive_herald_normalizers':positive,
                'source_probability_enclosures':rows,'complete_contexts':len(table),
                'all_current_outcomes_generated_before_selection':True,
                'whole_unknown_future_tail_covered_by_same_source_invariant':True,
                'finite_receipt_mass_or_tail_bound_used_to_determine_q':False,
                'source_normalizer_replaced':False,'physical_encoding':True,
                'quantum_time_measure_preserved_by_mother':True,
                'literal_cohort_reconstructed':False,'actual_hardware_slice_identified':False,
                'actual_hardware_uniquely_identified':False,'controller_advance':False}

    def exact_probability_table(self):
        report=SupportedHistoryPosterior.exact_outcome_law(self)
        return complete.component.ProjectedHistoryLaw._table(report['source_probability_enclosures'])

    @classmethod
    def from_record(cls,record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA,
                         'original source-supported posterior required')
        parent=complete.CompleteHistoryPosterior.from_record(record['complete_parent_posterior'])
        result=cls(parent)
        channel._require(result.record() == record,'source invariant, actual event or normalized coimage changed')
        return result

    def next_reload_input(self,source):
        self.verify()
        inlet=complete.CompleteHistoryPosterior.next_reload_input(self.posterior,source)
        inlet.update(state={(0,0,i,j):v for (i,j),v in self._state.items()},
                     upstream_trace_norm_error=self._error,source_posterior=self,
                     parent_complete_posterior=self.posterior,source_support_proof=projected._copy(self._proof),
                     whole_source_ray_proof=projected._copy(self._whole_proof),
                     exact_rank_one_coimage_generated=self._exact,
                     parent_unknown_tail_and_price_retained=True,literal_cohort_reconstructed=False)
        return inlet
