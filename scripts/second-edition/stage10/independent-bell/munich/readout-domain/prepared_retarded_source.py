"""Full33 source-born preparation feeds a retained one-emission field.

Every original resolved radiation group is retained.  A reduced preparation
endpoint can feed this field only after its earlier emitted photons are proved
outside the fixed BSM gate.  Their native APD time history stays in the mother.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import atom_photon_source as photons
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import joint_record_continuation as continuation
import munich_atomic_programme as atomic
import common_optical_readout as optical
import persistent_ready_mother as ready_mother
import retarded_photon_source as retarded
import native_tone_frame as native_frame
import exact_local_phase_source as exact_local


SCHEMA='stage10-full33-field-off-retarded-photon-kernel/v1'
PREPARED_SCHEMA='stage10-source-born-prepared-retarded-photon-source/v1'
INSTRUMENT_SCHEMA='stage10-full33-retarded-first-receipt-instrument/v1'
C=dipole.ComplexRadical
ZERO=C()


def _copy(value):
    return json.loads(channel._canonical(value))


def _bindings(*,exact=False,factorized=False):
    modules=(dipole,full,modes,photons,bsm,channel,joint,continuation,atomic,retarded,optical,ready_mother,native_frame)
    if exact:
        modules+=(exact_local,)
    if factorized:
        import factorized_local_phase_source as factors
        modules+=(exact_local,factors)
    paths={Path(__file__).resolve(),Path(__file__).resolve().with_name('retarded_receipt_source.py'),
           *(Path(m.__file__).resolve() for m in modules)}
    return {path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)}


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None)),repr(getattr(value,'__defaults__',None)),repr(getattr(value,'__kwdefaults__',None))


def _execution():
    helpers=(_copy,_bindings,_function,_execution,_guard,_tensor,_sandwich,_tensor_sandwich,_factorized_endpoint,_complex_product,_phase,
        _group_sources,_source_operations,_operation_record,_same_native_base,_scale_segment,_local_cell,_local_certificate,
        _local_counter_price,_local_endpoints,_exact_local_endpoints,_pair_endpoints,_native_inlet,_full_receipt_mother,
        _positive_packet_mass_lower,
        channel._read_input,channel._input_record,channel.poststate,channel._complex_record,
        channel._source,channel.SourceKernel.__init__,channel.SourceKernel.column,channel.SourceKernel.action,
        channel.SourceKernel.coefficient_error,channel._piece,channel._observations,channel._bindings,
        joint.JointCounterGenerator.record,joint.JointCounterGenerator.action,joint._source,
        joint.local.CounterGenerator.record,joint.local.CounterGenerator.action,joint.local.CounterGenerator.atomic_action,
        atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.atomic_base,
        atomic.MunichAtomicProgramme.certify_pair_cell,atomic.MunichAtomicProgramme.verify_pair_certificate,
        atomic.MunichAtomicProgramme.pair_phases,atomic.AtomicPhase.record,atomic.AtomicPhase.compile_grid,
        atomic._read_phase,atomic._counter_price,
        continuation.JointRecordContinuation.record,continuation.JointRecordContinuation.verify,
        continuation.JointRecordContinuation.hardware_record,joint._source,
        ready_mother.PersistentReadyMother.record,ready_mother.PersistentReadyMother.verify,
        ready_mother.PersistentReadyMother.from_record,optical.CommonOpticalReadout.record,
        optical.CommonOpticalReadout.verify_persistent,optical.CommonOpticalReadout.from_record,
        native_frame.NativeToneFrame.record,native_frame.NativeToneFrame.from_record,native_frame.NativeToneFrame.verify_first_poll,
        joint.local.natural_channels,dipole.matrix_product,dipole.matrix_adjoint,
        photons.collection_matrix,photons.beam_splitter_matrix,bsm.optical_transfer,bsm._rates,bsm._entry_norm,
        retarded._cdf,retarded._difference,retarded._product,retarded._exp_negative,retarded._closed,
        modes.complex_exponential)
    classes=(FieldOffPhotonKernel,PreparedRetardedSource,_LocalTensorKernel)
    methods=tuple(_function(member) for cls in classes for member in vars(cls).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return (tuple(map(_function,helpers)),methods,tuple(dipole.STATES),tuple(bsm.PATTERNS),tuple(bsm.PORTS),
            tuple(dipole.Q_COMPONENTS),joint.DIMENSION,bsm.GATE_SECONDS,SCHEMA,PREPARED_SCHEMA,INSTRUMENT_SCHEMA)


def _tensor(first,second):
    return {(joint.atom_pair_index(a,b),joint.atom_pair_index(c,d)):x*y
            for (a,c),x in first.items() for (b,d),y in second.items() if x and y}


def _sandwich(first,matrix,second):
    return dipole.matrix_product(dipole.matrix_product(first,matrix),dipole.matrix_adjoint(second))


def _tensor_sandwich(first_a,first_b,second_a,second_b,terms):
    result={}
    for a,b in terms:
        left=_sandwich(first_a,a,second_a);right=_sandwich(first_b,b,second_b)
        retarded._add(result,_tensor(left,right))
    return result


def _factorized_endpoint(source,report,native_record,native_result,owner,initial,old):
    import factorized_local_phase_source as factors
    channel._require(factors._check is factors._CHECK and factors._check.__code__ is factors._CHECK_CODE,
                     'factorized local source execution changed')
    factors._CHECK()
    channel._require(type(source) is factors.FactorizedLocalPhaseSource,
                     'closed source-issued factorized local evolution required')
    raw=factors.FactorizedLocalPhaseSource.record(source)
    channel._require(raw['native_source_record']==native_record and raw['native_ready_report']==native_result and
                     raw['common_atomic_owner']==atomic.MunichAtomicProgramme.record(owner) and
                     raw['complete_initial_ready']==channel._input_record(initial) and
                     Q(raw['upstream_trace_norm_error'])==old,
                     'factorized local actions must start at this same complete source Ready')
    factors.FactorizedLocalPhaseSource.verify(source,report)
    matrix=channel._read_input(report['full_pair_endpoint'],joint.DIMENSION)
    error=full.nonnegative(report['trace_norm_error'])
    endpoints=tuple(map(full.nonnegative,report['source_local_emission_origins_seconds']))
    terms=tuple((channel._read_input(item['left']['local_poststate'],full.DIMENSION),
                 channel._read_input(item['right']['local_poststate'],full.DIMENSION))
                for item in report['tensor_terms'])
    return matrix,error,endpoints,[{'kind':'same-source exact local Hermitian tensor evolution',
                                   'complete_factorized_local_certificate':_copy(report)}],raw,terms


def _complex_product(first,second,bits):
    a,e=first;b,f=second
    return a*b,e*bsm._entry_norm({(0,0):b},bits=bits)+f*bsm._entry_norm({(0,0):a},bits=bits)+e*f


def _phase(angle,bits):
    if not angle:
        return C(1),Q(0)
    value,error=modes.complex_exponential(0,angle,bits=bits)
    return C(*value),error


def _group_sources(owner):
    retarded._closed(owner)
    parent=atomic.MunichAtomicProgramme.record(owner)
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    channel._require(all(Q(x)==0 for x in parent['atomic_base']['magnetic_fields']),
                     'the complete field-off source currently requires B=0')
    unit=Q(parent['atomic_base']['seconds_per_unit'])
    atoms=tuple(joint._source(base.segment(side,1)) for side in (0,1))
    groups={}
    for side,atom in enumerate(atoms):
        channel._require(not any(i!=j for i,j in atom.hamiltonian) and not any(atom.program.ion_rates.values()),
                         'the field-off source must have diagonal Hamiltonian and no ion birth')
        channel._require(all(atom.outgoing[i]==0 for i,s in enumerate(dipole.STATES) if s.family in ('ground','ion')),
                         'emitted ground and dark ion sectors must remain absorbing')
        local={}
        for jump in atom.jumps:
            group=jump.label[:3]
            entries=local.setdefault(group,{})
            for (target,origin),value in jump.matrix.items():
                if not value:
                    continue
                source_state,target_state=dipole.STATES[origin],dipole.STATES[target]
                channel._require(source_state.family in ('D1','D2') and target_state.family=='ground' and
                                 source_state.f==group[1] and target_state.f==group[2],
                                 'one original resolved radiation group per field mode required')
                gamma=atom.outgoing[origin]
                ground_energy=atom.hamiltonian.get((target,target),ZERO).real.as_rational()/unit
                frequency=(atom.hamiltonian.get((origin,origin),ZERO)-atom.hamiltonian.get((target,target),ZERO)).real.as_rational()
                info=groups.setdefault(group,{'gamma':gamma/unit,'frequency':frequency/unit,
                                             'ground_energy':ground_energy,'operators':None})
                channel._require(gamma>0 and info['gamma']==gamma/unit and info['frequency']==frequency/unit and
                                 info['ground_energy']==ground_energy,
                                 'B0 radiation group must have one common source-generated width and frequency')
                factor=C(dipole.sqrt_rational(atom.program.gammas[group[:2]]/gamma))
                joint.local._add(entries,(jump.label[3],target,origin),value*factor)
        if side==0:
            for group,entries in local.items():
                groups[group]['operators']=entries
        else:
            channel._require(set(local)==set(groups) and all(local[group]==groups[group]['operators'] for group in groups),
                             'both full33 legs must use the same original natural bath')
    return parent,atoms,groups


def _source_operations(groups,collections,splitter,efficiencies):
    transfer=bsm.optical_transfer(*collections,splitter,efficiencies)
    operations={}
    for group,info in groups.items():
        for side in (0,1):
            for port in range(4):
                operator={}
                for (q,target,origin),value in info['operators'].items():
                    joint.local._add(operator,(target,origin),value*transfer[port][3*side+dipole.Q_COMPONENTS.index(q)])
                operations[group,side,port]=operator
    return operations


def _operation_record(operations):
    return [{'group':list(group),'side':side,'port':port,'full33_operator':channel._input_record(matrix)}
            for (group,side,port),matrix in sorted(operations.items())]


def _same_native_base(source,owner):
    unit=Q(source.record()['source_inlet']['seconds_per_source_unit'])
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    channel._require(unit==Q(base.record()['seconds_per_unit']),
                     'native mother and common atomic source must have the same physical unit')
    for window in source._reload.windows:
        for side,atom in enumerate(window.sources):
            common=base.segment(side,1)
            channel._require(atom.program.gammas==common.gammas and
                             atom.program.radiation_regime==common.radiation_regime,
                             'native mother and full prepared field must share the original natural bath')
            keys=list(dipole.STATES);anchor=keys[0]
            def detuning(program,state):
                return program.detunings[state] if state in program.detunings else program.detunings[state.family,state.f]
            channel._require(all(detuning(atom.program,k)-detuning(atom.program,anchor)==
                                 detuning(common,k)-detuning(common,anchor) for k in keys),
                             'native mother and preparation must share the original full hyperfine spectrum')


def _scale_segment(program,scale):
    return full.Segment(1,program.fields_r,program.fields_c,program.r*scale,program.c*scale,
        {key:value*scale for key,value in program.detunings.items()},
        {key:value*scale for key,value in program.gammas.items()},
        {key:value*scale for key,value in program.ion_rates.items()},
        radiation_regime=program.radiation_regime,field_convention=program.field_convention,ion_regime=program.ion_regime)


def _local_cell(owner,phase,cuts,cell_index,bits):
    parent=atomic.MunichAtomicProgramme.record(owner)
    raw=atomic.AtomicPhase.record(phase)
    channel._require(type(phase) is atomic.AtomicPhase and raw['parent']==parent,'same common-owner local phase required')
    compiled=atomic.AtomicPhase.compile_grid(phase,cuts,bits=bits)
    channel._require(type(cell_index) is int and 0<=cell_index<len(compiled['cells']),'original local phase cell required')
    cell=compiled['cells'][cell_index]
    physical=full.Segment.from_record(cell['original_cell']['raw_segment'])
    duration=physical.duration;scaled=_scale_segment(physical,duration)
    identity=full.Segment(1,dict.fromkeys(dipole.Q_COMPONENTS,0),dict.fromkeys(dipole.Q_COMPONENTS,0),0,0,
        dict.fromkeys(dipole.MANIFOLDS,0),dict.fromkeys(full.WIDTHS,0),dict.fromkeys(full.EXCITED,0),
        radiation_regime=physical.radiation_regime,field_convention=physical.field_convention)
    side=raw['side'];segments=(scaled,identity) if side==0 else (identity,scaled)
    auxiliary=joint.JointCounterGenerator(*segments,threshold=1,background_rate=0,collection=((0,)*6,))
    atom=joint._source(physical);rescaled=auxiliary.sources[side];fixed=auxiliary.sources[1-side]
    channel._require(rescaled.hamiltonian=={k:v*duration for k,v in atom.hamiltonian.items() if v*duration} and
                     rescaled.recycling=={k:v*duration for k,v in atom.recycling.items() if v*duration} and
                     rescaled.outgoing==[v*duration for v in atom.outgoing] and
                     not fixed.hamiltonian and not fixed.recycling and not any(fixed.outgoing),
                     'auxiliary unit-time generator must be exactly d*G_side tensor identity')
    model={'multitone':cell['original_cell']['cptp_duhamel_trace_norm_error'],
           'Zeeman':cell['Zeeman_trace_norm_error'],'total':cell['total_trace_norm_error']}
    return auxiliary,{'common_atomic_programme':parent,'physical_local_phase':raw,
        'physical_compilation':compiled,'physical_cell_index':cell_index,'physical_source_cell':cell,
        'physical_duration_source_units':str(duration),'per_unit_model_delta':model,
        'auxiliary_original_counter_source':auxiliary.record(),
        'generator_identity':'G_aux = duration*G_side tensor identity_other_side',
        'identity_other_side_generated_from_zero_H_jump_ion':True,
        'auxiliary_unit_interval_is_not_physical_common_clock':True}


class _LocalTensorKernel(channel.SourceKernel):
    """Original local columns act on every untouched spectator coordinate."""
    def __init__(self,generator,side,coefficient_bits=160):
        _guard();retarded._closed(generator)
        channel._require(type(generator) is joint.JointCounterGenerator and type(side) is int and side in (0,1),
                         'original generated local tensor source required')
        channel.SourceKernel.__init__(self,generator,coefficient_bits)
        fixed=self.source.sources[1-side]
        channel._require(not fixed.hamiltonian and not fixed.recycling and not any(fixed.outgoing) and
                         not self.source.background_rate and
                         all(not a and not b for _,(a,b) in self.source.detected_operators),
                         'local tensor pullback requires an identity spectator and no observed counter jump')
        self.side=side
        self.local=channel.SourceKernel(self.source.sources[side],coefficient_bits)

    def column(self,key):
        channel._key(key,self.dimension,self.threshold)
        if key not in self.columns:
            counter,row,column=key
            a,b=divmod(row,full.DIMENSION);c,d=divmod(column,full.DIMENSION)
            local_key=(counter,a,c) if self.side==0 else (counter,b,d)
            self.local.column(local_key)
            def address(target):
                count,i,j=target
                return ((count,joint.atom_pair_index(i,b),joint.atom_pair_index(j,d)) if self.side==0 else
                        (count,joint.atom_pair_index(a,i),joint.atom_pair_index(c,j)))
            self.columns[key]={address(target):value for target,value in self.local.columns[local_key].items()}
            self.exact_columns[key]={address(target):value for target,value in self.local.exact_columns[local_key].items()}
            self.errors[key]=self.local.errors[local_key]
        return self.columns[key]


def _local_certificate(kernel,initial,pieces,*,upstream_error,mode_bits,coefficient_bits,exponential_bits):
    _guard()
    # Only column compilation differs from the original certificate: the
    # same full-pair curve and original residual/rounding checker are used.
    channel._require(type(kernel) is _LocalTensorKernel and type(mode_bits) is int and 32<=mode_bits<=256 and
                     type(exponential_bits) is int and 64<=exponential_bits<=1024 and type(pieces) is list,
                     'complete original curve and registered precision required')
    source=kernel.source;duration=channel._duration(source)
    initial=channel._initial(initial,kernel.dimension);old=full.nonnegative(upstream_error)
    centre={};rounding=Q(0)
    for (i,j),value in initial.items():
        a,da=full.radical_midpoint(value.real,coefficient_bits)
        b,db=full.radical_midpoint(value.imag,coefficient_bits)
        channel._add(centre,(0,i,j),a,b);rounding+=da+db
    error=old+rounding;elapsed=Q(0);records=[]
    for item in pieces:
        width,begin,end,errors,diagnostics=channel._piece(kernel,item,mode_bits,exponential_bits)
        gap=channel._difference(begin,centre);error+=gap+sum(errors.values(),Q(0));elapsed+=width
        channel._require(elapsed<=duration,'trial pieces extend beyond raw programme duration')
        records.append({'duration':str(width),'initial_join_error':str(gap),
                        **{name:str(value) for name,value in errors.items()},'modes':diagnostics})
        centre=end
    channel._require(elapsed==duration,'trial pieces must cover the whole raw programme duration')
    raw_source=source.record();raw_initial=channel._input_record(initial)
    return {'schema':channel.SCHEMA,'certified':True,'physical_dimension':kernel.dimension,
        'counter_levels':kernel.threshold+1,'duration':str(duration),
        'counter_complex_coordinates':(kernel.threshold+1)*kernel.dimension**2,
        'raw_source':raw_source,'raw_source_sha256':channel._digest(raw_source),
        'initial_state':raw_initial,'initial_state_sha256':channel._digest(raw_initial),
        'initial_counter':0,'upstream_trace_norm_error':str(old),'initial_radical_error':str(rounding),
        'trial_pieces':_copy(pieces),'piece_error_records':records,'mode_bits':mode_bits,
        'coefficient_bits':coefficient_bits,'exponential_bits':exponential_bits,
        'source_columns_checked':len(kernel.columns),'trace_norm_error_bound':str(error),
        'counter_poststate_center':[[c,i,j,str(a),str(b)] for (c,i,j),(a,b) in sorted(centre.items())],
        **channel._observations(centre,error,kernel.threshold),'source_bindings':channel._bindings(source),
        'error_transport':'CPTP trace-norm contraction on Hermitian trial curves',
        'local_coordinate':'u=t/Delta; polynomial derivative divided by Delta',
        'source_time_coverage_complete':True,'source_counter_trace_preservation_checked':True,
        'complete_poststate_enclosure':True,'omitted_entries_covered_by_global_error':True,
        'counter_saturation_stops_atomic_dynamics':False,'solver_reexecuted_by_checker':False,
        'eigenvector_correctness_assumed':False,'physical_probability_interpretation_requires_positive_input':True,
        'input_positivity_certified_here':False,'actual_presence_programme_identified':False,
        'actual_clock_encoder_identified':False,'actual_hardware_identity_asserted':False,
        'controller_advance':False,'propagation_performed':True}


def _local_counter_price(source,side,initial,pieces,delta,old_error,precision):
    _guard()
    initial=channel._initial(initial,joint.DIMENSION);old=full.nonnegative(old_error)
    norm=bsm._entry_norm(initial,bits=precision['coefficient_bits'])
    optical_price=Q(delta['multitone'])*norm;zeeman_price=Q(delta['Zeeman'])*norm
    payment=optical_price+zeeman_price
    kernel=_LocalTensorKernel(source,side,precision['coefficient_bits'])
    raw=_local_certificate(kernel,initial,pieces,upstream_error=old+payment,**precision)
    local=Q(raw['trace_norm_error_bound'])-old-payment
    channel._require(local>=0,'original residual checker dropped a source price')
    return {'before_model_trace_norm_error':str(old),'input_trace_norm_upper':str(norm),
        'per_unit_model_delta':delta,'multitone_payment':str(optical_price),'Zeeman_payment':str(zeeman_price),
        'source_model_payment':str(payment),'source_checker_local_error':str(local),
        'global_trace_norm_error':raw['trace_norm_error_bound'],'source_certificate':raw,
        'price_transport':'true CP contracts the old Hermitian error once; true-minus-compiled acts on the complete centre',
        'input_positivity_certified_here':False,'physical_probability_requires_positive_source_input':True,
        'source_column_pullback':{'side':side,'local_columns_compiled':len(kernel.local.columns),
            'complete_pair_columns_checked':len(kernel.columns),'spectator_coordinates_retained':True,
            'identity':'G_side tensor identity on the entire original pair; no partial trace or state projection'}}


def _local_endpoints(owner,matrix,error,plans,bits):
    channel._require(type(plans) in (tuple,list) and len(plans)==2,'two complete source-owned local control plans required')
    matrix=channel._initial(matrix,joint.DIMENSION);error=full.nonnegative(error)
    certificates=[];endpoints=[]
    for side,plan in enumerate(plans):
        channel._require(type(plan) in (tuple,list) and len(plan)>=3,'alternating preparation then excitation is required on each leg')
        elapsed=Q(0);previous=None
        for index,item in enumerate(plan):
            channel._require(type(item) is dict and set(item)=={'phase','cuts','trial_pieces'},
                             'source phase/cuts and one untrusted complete curve per cell required')
            phase=atomic._read_phase(item['phase']);record=atomic.AtomicPhase.record(phase)
            kind='excitation' if index==len(plan)-1 else 'preparation'
            channel._require(record['side']==side and record['kind']==kind,'each local source plan ends in its own excitation')
            if kind=='preparation':
                pump=next(d for d in record['drives'] if d['role']=='pump2to1')
                address=pump['beam'],pump['polarization']
                channel._require(previous is None or all(a!=b for a,b in zip(previous,address)),
                                 'local pump direction and polarization must alternate')
                previous=address
            compiled=atomic.AtomicPhase.compile_grid(phase,item['cuts'],bits=bits)
            channel._require(len(item['trial_pieces'])==len(compiled['cells']),'every generated local cell needs its complete witness')
            for cell,pieces in enumerate(item['trial_pieces']):
                source,model=_local_cell(owner,phase,item['cuts'],cell,bits)
                priced=_local_counter_price(source,side,matrix,pieces,model['per_unit_model_delta'],error,
                    dict(mode_bits=60,coefficient_bits=bits,exponential_bits=bits))
                certificate={'schema':PREPARED_SCHEMA+'/local-source-TP-cell','owned_local_cell':model,**priced}
                matrix,error=channel.poststate(priced['source_certificate'],'unconditional')
                certificates.append(certificate)
            elapsed+=Q(record['duration_seconds'])
        endpoints.append(elapsed)
    return matrix,error,tuple(endpoints),certificates


def _exact_local_endpoints(owner,matrix,error,plans,bits):
    _guard()
    channel._require(exact_local._guard is exact_local._GUARD and exact_local._guard.__code__ is exact_local._GUARD_CODE,
                     'exact local source execution changed')
    exact_local._GUARD()
    channel._require(type(plans) in (tuple,list) and len(plans)==2,'two complete exact source-local plans required')
    parent=atomic.MunichAtomicProgramme.record(owner)
    matrix=channel._initial(matrix,joint.DIMENSION);error=full.nonnegative(error)
    certificates=[];endpoints=[]
    for side,plan in enumerate(plans):
        channel._require(type(plan) in (tuple,list) and len(plan)>=3,'alternating preparation then excitation is required on each leg')
        elapsed=Q(0);previous=None
        for index,item in enumerate(plan):
            channel._require(type(item) is dict and set(item) in ({'phase','cuts','trial_pieces'},
                {'phase','cuts','trial_pieces','precision'}),'raw exact local phase, cuts and complete untrusted witnesses required')
            phase=atomic._read_phase(item['phase']);raw=atomic.AtomicPhase.record(phase)
            kind='excitation' if index==len(plan)-1 else 'preparation'
            channel._require(raw['parent']==parent and raw['side']==side and raw['kind']==kind,
                             'each source-local plan keeps its common owner, side and final excitation')
            if kind=='preparation':
                pump=next(d for d in raw['drives'] if d['role']=='pump2to1');address=pump['beam'],pump['polarization']
                channel._require(previous is None or all(a!=b for a,b in zip(previous,address)),
                                 'exact source pump direction and polarization must alternate')
                previous=address
            programme=atomic.AtomicPhase.programme(phase);cuts=tuple(map(full.exact,item['cuts']))
            channel._require(len(cuts)>=2 and cuts[0]==0 and cuts[-1]==programme.base.duration and
                             all(a<b for a,b in zip(cuts,cuts[1:])) and
                             type(item['trial_pieces']) in (tuple,list) and len(item['trial_pieces'])==len(cuts)-1,
                             'exact local cuts and witnesses must cover the original physical phase')
            precision=item.get('precision',dict(phase_order=48,mode_bits=160,coefficient_bits=bits,exponential_bits=bits))
            channel._require(type(precision) is dict and set(precision)=={'phase_order','mode_bits','coefficient_bits','exponential_bits'},
                             'complete registered source residual precision required')
            for interval,pieces in zip(zip(cuts,cuts[1:]),item['trial_pieces']):
                source=exact_local.ExactLocalPhaseSource(phase,matrix,upstream_error=error,interval=interval)
                retarded._closed(source)
                report=exact_local.ExactLocalPhaseSource.certify(source,pieces,**precision)
                local_error=Q(report['trace_norm_error'])-error
                channel._require(report['old_error_once']==str(error) and report['source_model_payment']=='0' and local_error>=0,
                                 'exact source-local certificate must keep the old error once and pay every new residual')
                certificates.append({'schema':PREPARED_SCHEMA+'/exact-local-source-TP-cell',
                    'owned_exact_local_source':exact_local.ExactLocalPhaseSource.record(source),
                    'before_model_trace_norm_error':str(error),'source_model_payment':'0',
                    'source_checker_local_error':str(local_error),'global_trace_norm_error':report['trace_norm_error'],
                    'source_certificate':report})
                matrix=channel._read_input(report['full_pair_endpoint'],joint.DIMENSION)
                error=Q(report['trace_norm_error'])
            elapsed+=Q(raw['duration_seconds'])
        endpoints.append(elapsed)
    return matrix,error,tuple(endpoints),certificates


def _pair_endpoints(owner,matrix,error,phase_plan,bits):
    channel._require(type(phase_plan) in (tuple,list) and len(phase_plan)>=3,
                     'the full alternating preparation and excitation plan is required')
    clock=Q(0);certificates=[];previous=[None,None]
    for index,item in enumerate(phase_plan):
        channel._require(type(item) is dict and set(item)=={'first_phase','second_phase','cuts','trial_pieces'},
                         'only raw common pair phases, cuts and untrusted curve witnesses are inputs')
        first,second=(atomic._read_phase(item[key]) for key in ('first_phase','second_phase'))
        records=(atomic.AtomicPhase.record(first),atomic.AtomicPhase.record(second))
        kind='excitation' if index==len(phase_plan)-1 else 'preparation'
        channel._require(all(record['kind']==kind for record in records),'all preparation steps precede the final excitation')
        if kind=='preparation':
            for side,record in enumerate(records):
                drive=next(d for d in record['drives'] if d['role']=='pump2to1')
                address=drive['beam'],drive['polarization']
                channel._require(previous[side] is None or all(a!=b for a,b in zip(previous[side],address)),
                                 'source preparation alternates the raw pump direction and polarization')
                previous[side]=address
        phases,_=atomic.MunichAtomicProgramme.pair_phases(owner,first,second,item['cuts'],bits=bits)
        channel._require(type(item['trial_pieces']) in (tuple,list) and len(item['trial_pieces'])==len(phases),
                         'one untrusted complete curve per source-generated phase cell required')
        for cell,witness in enumerate(item['trial_pieces']):
            certificate=atomic.MunichAtomicProgramme.certify_pair_cell(owner,first,second,item['cuts'],cell,matrix,witness,
                upstream_error=error,coefficient_bits=bits,exponential_bits=bits,compilation_bits=bits)
            matrix,error=channel.poststate(certificate['source_certificate'],'unconditional')
            certificates.append(certificate)
        clock+=Q(records[0]['duration_seconds'])
    return matrix,error,(clock,clock),certificates


def _native_inlet(source,report,owner,shared,shared_report):
    retarded._closed(source);retarded._closed(owner)
    if type(source) is continuation.JointRecordContinuation:
        continuation.JointRecordContinuation.verify(source,report)
        _same_native_base(source,owner)
        channel._require(shared is None and shared_report is None,'legacy Ready derives its own original optical pack')
        gate=source._burst.gate
        matrix=channel._read_input(report['complete_future_ready_matrix'],joint.DIMENSION)
        error=Q(report['native_reload_resolvent']['ready_trace_norm_error'])
        geometry={'kind':'complete native resolvent Ready','time_mother':report['time_state_mother_record'],
                  'time_recipe':report['complete_relative_time_measure_recipe'],
                  'parameter_domain':report['parameter_domain'],'source_support_word':report['source_support_word']}
        optics={'collections':gate.collections,'splitter':gate.splitter,'efficiencies':gate.efficiencies,
                'backgrounds':gate.background_rates,'shared_record':gate.record()}
        source_record=continuation.JointRecordContinuation.record(source)
        bound=Q(1)
    else:
        channel._require(type(source) in (ready_mother.PersistentReadyMother,native_frame.NativeToneFrame) and
                         type(shared) is optical.CommonOpticalReadout,
                         'closed first-PC-ready mother and its common optical source required')
        retarded._closed(shared)
        exact_frame=type(source) is native_frame.NativeToneFrame
        if exact_frame:
            native_frame.NativeToneFrame.verify_first_poll(source,report)
            source_record=native_frame.NativeToneFrame.record(source)
            parent=source_record['original_PRM_source']
            channel._require(source_record['whole_native_time_and_queue_mother']==parent['whole_time_measure_recipe'] and
                             report['whole_native_time_and_queue_mother']==parent['whole_time_measure_recipe'],
                             'exact native frame must keep the original whole clock and arrival mother')
        else:
            ready_mother.PersistentReadyMother.verify(source,report)
            source_record=ready_mother.PersistentReadyMother.record(source);parent=source_record
        optical.CommonOpticalReadout.verify_persistent(shared,shared_report)
        raw=optical.CommonOpticalReadout.record(shared)
        channel._require(parent['persistent_source']==shared_report['raw_persistent_source'] and
                         parent['persistent_source']['atomic_owner']==atomic.MunichAtomicProgramme.record(owner)==
                         raw['common_atomic_owner'],'first-poll Ready, optics and preparation must have one exact atomic owner')
        matrix=channel._read_input(report['generated_first_ready_poststate'],joint.DIMENSION)
        error=Q(report['first_poll_joint_error'])
        geometry={'kind':('exact native-frame Ready at the original first poll' if exact_frame else
                         'first PC-ready at the original first poll'),'time_mother':parent['whole_time_measure_recipe'],
            'time_recipe':{'first_poll_geometry':parent['first_poll_geometry'],'count_faces':report['count_faces'],
                           'first_poll_pending_poststate':report['first_poll_pending_poststate'],
                           'whole_future_ready_mother':parent['whole_time_measure_recipe'],
                           'finite_first_ready_measure_not_all_later_ready':True},
            'parameter_domain':{'common_atomic_owner':raw['common_atomic_owner'],'common_optical_source':raw},
            'source_support_word':{'source_kind':'first-poll finite PC-ready event','normalization_or_occupancy_conditioned':False}}
        decode=lambda rows:tuple(tuple(channel._complex_record(v) for v in row) for row in rows)
        optics={'collections':(decode(raw['collection_a']),decode(raw['collection_b'])),'splitter':decode(raw['splitter']),
                'efficiencies':tuple(map(Q,raw['efficiencies'])),'backgrounds':tuple(map(Q,raw['background_rates'])),
                'shared_record':raw}
        bound=Q(parent['positive_source_input_mass_upper'])
    mass=joint._trace(matrix)
    channel._require(not mass.imag,'Hermitian source Ready mass required')
    centre,rounding=full.radical_midpoint(mass.real,160)
    bound=min(bound,max(Q(0),centre+rounding+error))
    return matrix,error,source_record,geometry,optics,bound


def _full_receipt_mother(shared,kernel):
    import retarded_receipt_source as receipt
    channel._require(receipt._guard is receipt._GUARD and receipt._guard.__code__ is receipt._GUARD_CODE,
                     'retarded receipt source execution changed')
    receipt._GUARD()
    return receipt.RetardedReceiptSource(shared,kernel)


def _positive_packet_mass_lower(states,error,survival,survival_error,bits):
    total=sum((value.real for state in states for (i,j),value in state.items() if i==j),dipole.Radical())
    centre,radical=full.radical_midpoint(total,bits)
    signal_lower=max(Q(0),centre-radical-full.nonnegative(error))
    probability_lower=max(Q(0),survival-survival_error)
    return {'signal_trace_centre':str(centre),'signal_trace_radical_error':str(radical),
        'signal_trace_norm_error':str(error),'signal_event_mass_lower':str(signal_lower),
        'no_BG_through_original_gate_probability_lower':str(probability_lower),
        'full_event_mass_lower':str(probability_lower*signal_lower),
        'positive_BG_remainder_subtracted_from_mass_lower':False,
        'law':'full receipt CP measure = p0*signal receipt CP measure + positive BG remainder'}


class FieldOffPhotonKernel:
    """Unconditional full33 photon instrument generated from the raw bath."""
    def __init__(self,owner,*,flight_seconds,emission_origin_seconds=(0,0),gate_start_seconds=0,
                 gate_seconds=None,collection_a=None,collection_b=None,splitter=None,efficiencies=(1,1,1,1)):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared retarded source execution changed')
        _guard()
        channel._require(type(self) is FieldOffPhotonKernel and type(owner) is atomic.MunichAtomicProgramme,
                         'closed common full33 field source required')
        parent,atoms,groups=_group_sources(owner)
        flights=tuple(map(full.nonnegative,flight_seconds));origins=tuple(map(full.nonnegative,emission_origin_seconds))
        channel._require(len(flights)==len(origins)==2,'two source emission origins and raw flight coordinates required')
        a=full.nonnegative(gate_start_seconds)
        gate=(a,a+bsm.GATE_SECONDS) if gate_seconds is None else tuple(map(full.nonnegative,gate_seconds))
        channel._require(len(gate)==2 and gate[0]<=gate[1],'fixed ordered physical BSM gate required')
        collections=tuple(map(photons.collection_matrix,(photons.ideal_collection() if collection_a is None else collection_a,
                              photons.ideal_collection() if collection_b is None else collection_b)))
        splitter=photons.beam_splitter_matrix(photons.balanced_beam_splitter() if splitter is None else splitter)
        efficiencies=bsm._rates(efficiencies,probabilities=True)
        self._owner,self._groups,self._operations=owner,groups,_source_operations(groups,collections,splitter,efficiencies)
        self._value={'schema':SCHEMA,'common_atomic_programme':parent,
            'source_atoms':[atom.program.record() for atom in atoms],
            'radiation_groups':[{'group':list(group),'source_decay_per_second':str(info['gamma']),
                'source_frequency_per_second':str(info['frequency']),
                'source_ground_energy_per_second':str(info['ground_energy']),
                'normalized_original_jump_columns':[[q,g,e,v.serialize()] for (q,g,e),v in sorted(info['operators'].items())]}
                for group,info in sorted(groups.items())],
            'local_source_born_detection_operators':_operation_record(self._operations),
            'raw_flight_seconds':list(map(str,flights)),'raw_emission_origin_seconds':list(map(str,origins)),
            'source_arrival_origins_seconds':list(map(str,(a+b for a,b in zip(origins,flights)))),
            'raw_gate_seconds':list(map(str,gate)),'default_public_120ns_gate':gate_seconds is None,
            'raw_collection':[[[v.serialize() for v in row] for row in matrix] for matrix in collections],
            'raw_splitter':[[v.serialize() for v in row] for row in splitter],'raw_efficiencies':list(map(str,efficiencies)),
            'complete_field_carrier':{'zero_photon':'all33 no-jump diagonal operator; ground and ion vacuum sectors retained',
                'one_photon':'original (line,Fexc,Fground,q) jump column tensor its causal L2 time leg',
                'two_photons':'tensor of both local fields, including both Bose assignments at each physical port',
                'loss':'the passive optical complement I-T*T; traced only by the receipt restriction',
                'normalization':'natural jump completeness gives a local TP field dilation; no excited occupancy renormalization',
                'emission_time_off_diagonals_retained':True,'prepared_F0_or_Bell_density_is_input':False},
            'field_off_single_emission_per_leg':True,'all_original33_input_coordinates_retained':True,
            'successful_preparation_or_excitation_conditioned':False,'physical_input_state_supplied':False,
            'full_retry_source_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False,
            'source_bindings':_bindings()}
        self._seal=channel._canonical(self._value)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared retarded source execution changed')
        _guard();retarded._closed(self);retarded._closed(self._owner)
        channel._require(type(self) is FieldOffPhotonKernel and channel._canonical(self._value)==self._seal and
                         self._value['source_bindings']==_bindings() and
                         atomic.MunichAtomicProgramme.record(self._owner)==self._value['common_atomic_programme'] and
                         _operation_record(self._operations)==self._value['local_source_born_detection_operators'] and
                         [{'group':list(g),'source_decay_per_second':str(v['gamma']),
                           'source_frequency_per_second':str(v['frequency']),
                           'source_ground_energy_per_second':str(v['ground_energy']),
                           'normalized_original_jump_columns':[[q,a,b,x.serialize()] for (q,a,b),x in sorted(v['operators'].items())]}
                          for g,v in sorted(self._groups.items())]==self._value['radiation_groups'],
                         'the full bath, photon operator, time origin or optical source changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        channel._require(cls is FieldOffPhotonKernel and type(record) is dict and record.get('schema')==SCHEMA,
                         'closed full33 photon kernel record required')
        decode=lambda matrix:tuple(tuple(channel._complex_record(x) for x in row) for row in matrix)
        result=cls(atomic.MunichAtomicProgramme.from_record(record['common_atomic_programme']),
            flight_seconds=record['raw_flight_seconds'],emission_origin_seconds=record['raw_emission_origin_seconds'],
            gate_start_seconds=record['raw_gate_seconds'][0],
            gate_seconds=None if record['default_public_120ns_gate'] else record['raw_gate_seconds'],
            collection_a=decode(record['raw_collection'][0]),collection_b=decode(record['raw_collection'][1]),
            splitter=decode(record['raw_splitter']),efficiencies=record['raw_efficiencies'])
        channel._require(result.record()==record,'full33 natural field or source scope differs')
        return result

    def _overlap(self,group,time,gate_origin,bits):
        info=self._groups[group];origins=tuple(map(Q,self._value['source_arrival_origins_seconds']))
        gamma,frequency=info['gamma'],info['frequency']
        excitation_origins=tuple(map(Q,self._value['raw_emission_origin_seconds']))
        mass=retarded._difference(retarded._cdf(gamma,max(origins),time,bits),
                                  retarded._cdf(gamma,max(origins),gate_origin,bits))
        visible=retarded._product(retarded._exp_negative(gamma*abs(origins[0]-origins[1])/2,bits),mass)
        # The two assignments end in the same total ground energy.  Unequal
        # local source origins nevertheless retain this relative matter phase.
        angle=frequency*(origins[0]-origins[1])+info['ground_energy']*(excitation_origins[0]-excitation_origins[1])
        return _complex_product((C(visible[0]),visible[1]),_phase(angle,bits),bits)

    def _cumulative(self,g,h,time,gate_origin,bits):
        origins=tuple(map(Q,self._value['source_arrival_origins_seconds']))
        if time is not None and time<=max(gate_origin,*origins):
            return (Q(0),Q(0)),(Q(0),Q(0)),(ZERO,Q(0))
        def mass(group,side):
            gamma=self._groups[group]['gamma']
            return retarded._difference(retarded._cdf(gamma,origins[side],time,bits),
                                        retarded._cdf(gamma,origins[side],gate_origin,bits))
        first=retarded._product(mass(g,0),mass(h,1));second=retarded._product(mass(h,0),mass(g,1))
        x=self._overlap(g,time,gate_origin,bits);y=self._overlap(h,time,gate_origin,bits)
        cross=_complex_product(x,(y[0].conjugate(),y[1]),bits)
        return first,second,cross

    def _instrument(self,matrix,left,right,gate_origin,gate_end,bits,upstream_error,*,tensor_terms=None):
        source_record=self.record();matrix=joint._matrix(matrix)
        channel._require(type(bits) is int and 64<=bits<=1024 and left>=gate_origin and
                         (right is None or (left<=right and (gate_end is None or right<=gate_end))),
                         'restriction must retain its original gate and registered scalar precision')
        result=tuple({} for _ in bsm.PATTERNS);local=Q(0);group_prices=[]
        for g in sorted(self._groups):
            for h in sorted(self._groups):
                lo=self._cumulative(g,h,left,gate_origin,bits);hi=self._cumulative(g,h,right,gate_origin,bits)
                w1,w2=(retarded._difference(b,a) for a,b in zip(lo[:2],hi[:2]))
                z=(hi[2][0]-lo[2][0],hi[2][1]+lo[2][1])
                if right==left:
                    w1=w2=(Q(0),Q(0));z=(ZERO,Q(0))
                group_error=Q(0)
                for index,(_,ports) in enumerate(bsm.PATTERNS):
                    d,e=ports
                    first_a,first_b=self._operations[g,0,d],self._operations[h,1,e]
                    second_a,second_b=self._operations[h,0,e],self._operations[g,1,d]
                    if tensor_terms is None:
                        first=_tensor(first_a,first_b);second=_tensor(second_a,second_b)
                        a=_sandwich(first,matrix,first);b=_sandwich(second,matrix,second)
                        c=_sandwich(first,matrix,second);f=_sandwich(second,matrix,first)
                    else:
                        a=_tensor_sandwich(first_a,first_b,first_a,first_b,tensor_terms)
                        b=_tensor_sandwich(second_a,second_b,second_a,second_b,tensor_terms)
                        c=_tensor_sandwich(first_a,first_b,second_a,second_b,tensor_terms)
                        f=_tensor_sandwich(second_a,second_b,first_a,first_b,tensor_terms)
                    retarded._add(result[index],a,w1[0]);retarded._add(result[index],b,w2[0])
                    retarded._add(result[index],c,z[0]);retarded._add(result[index],f,z[0].conjugate())
                    group_error+=w1[1]*bsm._entry_norm(a,bits=bits)+w2[1]*bsm._entry_norm(b,bits=bits)+\
                                 z[1]*(bsm._entry_norm(c,bits=bits)+bsm._entry_norm(f,bits=bits))
                local+=group_error
                if group_error:
                    group_prices.append({'first_group':list(g),'second_group':list(h),'whole_four_pattern_price':str(group_error)})
        old=full.nonnegative(upstream_error)
        if gate_end is None:
            contraction={'observation_scope':'ungated complete wavepacket',
                'whole_four_pattern_input_contraction_upper':'1',
                'effect_domination':'the complete passive photon receipt instrument is trace-nonincreasing',
                'finite_raw_gate_bound_used_for_infinite_measure':False}
        else:
            channel._require((gate_origin,gate_end)==tuple(map(Q,self._value['raw_gate_seconds'])),
                             'finite signal contraction belongs to the original source gate')
            contraction=FieldOffPhotonKernel.signal_input_contraction(self)
        old_payment=old*Q(contraction['whole_four_pattern_input_contraction_upper'])
        return _copy({'schema':INSTRUMENT_SCHEMA,'source_record':source_record,'scalar_bits':bits,
            'gate_origin_seconds':str(gate_origin),'gate_end_seconds':None if gate_end is None else str(gate_end),
            'restriction_seconds':[str(left),None if right is None else str(right)],
            'four_pattern_poststates':[channel._input_record(x) for x in result],
            'old_whole_input_error_paid_once':str(old),'signal_input_error_payment':str(old_payment),
            'source_signal_input_contraction':contraction,'whole_local_scalar_error':str(local),
            'global_trace_norm_error':str(old_payment+local),'resolved_group_prices':group_prices,
            'exact_CP_law':'each resolved two-photon environment is the Gram of both Bose time assignments on the same first-receipt domain',
            'source_domain':'every original33 coordinate; ground/ion/one-sided excitations and losses remain in the complete field mother',
            'excited_occupation_conditioned_or_renormalized':False,'first_click_before_restriction_left_retained':True,
            'gate_pre_click_latched':False,'numerical_centres_assumed_positive':False,
            'prepared_state_or_target_measure_supplied':False,'whole_input_error_summed_per_group':False,
            'full_retry_source_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False})

    def signal_input_contraction(self):
        """Two photons in the original gate bound this entire CP measure."""
        source=self.record();a,z=map(Q,source['raw_gate_seconds'])
        maximum=max(v['gamma'] for v in self._groups.values())
        width=z-a
        legs=[min(Q(1),maximum*width)]*2
        # The original natural loss identity gives an orthogonal excited
        # projector after every normalized radiation group is summed.
        gram={}
        for group in self._groups.values():
            for q in dipole.Q_COMPONENTS:
                operator={(g,e):v for (component,g,e),v in group['operators'].items() if component==q}
                retarded._add(gram,dipole.matrix_product(dipole.matrix_adjoint(operator),operator))
        expected={(i,i):C(1) for i,state in enumerate(dipole.STATES) if state.family in ('D1','D2')}
        channel._require(gram==expected,'all original radiation modes must give the full excited emission isometry')
        return {'original_gate_seconds':[str(a),str(z)],'original_gate_width_seconds':str(width),
            'maximum_source_decay_per_second':str(maximum),'leg_gate_emission_probability_uppers':list(map(str,legs)),
            'whole_four_pattern_input_contraction_upper':str(legs[0]*legs[1]),
            'source_natural_normalized_emission_gram':channel._input_record(gram),
            'effect_domination':'all signal patterns require both photons inside the original gate; effect <= P_A(G) tensor P_B(G) <= c_A*c_B*identity',
            'restricted_interval_does_not_reset_first_click_or_shorten_this_bound':True,
            'entangled_and_number_coherent_inputs_covered':True}

    def column(self,row,column,left=None,right=None,*,bits=160,whole_wavepacket=False):
        """Read a generated linear instrument column; no prepared state enters."""
        self.record()
        channel._require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and
                         0<=column<joint.DIMENSION and type(whole_wavepacket) is bool,'original full-pair matrix-unit column required')
        if whole_wavepacket:
            a=min(map(Q,self._value['source_arrival_origins_seconds']));z=None
        else:
            a,z=map(Q,self._value['raw_gate_seconds'])
        report=self._instrument({(row,column):C(1)},a if left is None else full.exact(left),
                                z if right is None else full.exact(right),a,z,bits,0)
        report['source_matrix_unit']=[row,column]
        report['linear_instrument_column_readout']=True
        report['ungated_column_readout']=whole_wavepacket
        return report

    def verify_column(self,report):
        self.record()
        channel._require(type(report) is dict and report.get('schema')==INSTRUMENT_SCHEMA and
                         report.get('source_record')==self.record() and report.get('linear_instrument_column_readout') is True,
                         'same source-generated full33 instrument column required')
        row,column=report['source_matrix_unit'];a,z=report['restriction_seconds']
        channel._require(FieldOffPhotonKernel.column(self,row,column,a,z,bits=report['scalar_bits'],
                         whole_wavepacket=report['ungated_column_readout'])==report,
                         'full33 column, field environment, gate or shared price changed')
        return True

    def no_emission_operator(self,side,physical_time,*,bits=160):
        source=self.record();time=full.exact(physical_time)
        channel._require(type(side) is int and side in (0,1) and type(bits) is int and 64<=bits<=1024,
                         'one original field leg and registered precision required')
        origin=Q(source['raw_emission_origin_seconds'][side]);age=time-origin
        channel._require(age>=0,'the field source has not reached this leg emission origin')
        atom=joint._source(full.Segment.from_record(source['source_atoms'][side]))
        unit=Q(source['common_atomic_programme']['atomic_base']['seconds_per_unit'])
        operator={};error=Q(0)
        for i in range(full.DIMENSION):
            energy=atom.hamiltonian.get((i,i),ZERO).real.as_rational()/unit
            if not age:
                value,radius=C(1),Q(0)
            else:
                scalar,radius=modes.complex_exponential(-atom.outgoing[i]*age/(2*unit),-energy*age,bits=bits)
                value=C(*scalar)
            joint.local._add(operator,(i,i),value);error=max(error,radius)
        return {'source_record':source,'side':side,'physical_time_seconds':str(time),
            'full33_vacuum_operator':channel._input_record(operator),'operator_norm_error_upper':str(error),
            'ground_and_ion_vacuum_coordinates_retained':True,'scalar_bits':bits}

    def emission_operator(self,side,group,q,arrival_time,physical_observation_time,*,bits=160):
        source=self.record();group=tuple(group)
        channel._require(type(side) is int and side in (0,1) and group in self._groups and
                         type(q) is int and q in dipole.Q_COMPONENTS and type(bits) is int and 64<=bits<=1024,
                         'one original resolved radiation mode and source leg required')
        time,observation=map(full.exact,(arrival_time,physical_observation_time))
        origin=Q(source['raw_emission_origin_seconds'][side]);flight=Q(source['raw_flight_seconds'][side])
        emission=time-flight;age=emission-origin
        channel._require(observation>=origin and emission<=observation,
                         'only already source-generated emission can be in the field at the observation clock')
        info=self._groups[group];operator={};error=Q(0)
        if age>=0:
            atom=joint._source(full.Segment.from_record(source['source_atoms'][side]))
            ground=next(a for (component,a,_),v in info['operators'].items() if v)
            unit=Q(source['common_atomic_programme']['atomic_base']['seconds_per_unit'])
            energy=atom.hamiltonian.get((ground,ground),ZERO).real.as_rational()/unit
            scalar,radius=modes.complex_exponential(-info['gamma']*age/2,
                          -info['frequency']*age-energy*(observation-origin),bits=bits)
            for (component,a,b),value in info['operators'].items():
                if component==q:
                    factor=value*C(dipole.sqrt_rational(info['gamma']))
                    joint.local._add(operator,(a,b),factor*C(*scalar))
                    error+=radius*bsm._entry_norm({(a,b):factor},bits=bits)
        return {'source_record':source,'side':side,'radiation_group':list(group),'q':q,
            'arrival_time_seconds':str(time),'source_emission_time_seconds':str(emission),
            'physical_observation_time_seconds':str(observation),
            'full33_one_photon_operator':channel._input_record(operator),'operator_norm_error_upper':str(error),
            'off_diagonal_time_coordinate_retained':True,'scalar_bits':bits}


class PreparedRetardedSource:
    """Native Ready → complete raw pair evolution → the same photon field."""
    def __init__(self,native_source,native_result,owner,phase_plan=None,*,flight_seconds,gate_start_seconds,
                 gate_seconds=None,collection_a=None,collection_b=None,splitter=None,efficiencies=None,bits=160,
                 local_clock_plan=None,exact_local_clock_plan=None,shared_optical_source=None,shared_persistent_report=None,
                 factorized_local_source=None,factorized_local_report=None):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared retarded source execution changed')
        _guard()
        channel._require(type(self) is PreparedRetardedSource and type(native_source) in
                         (continuation.JointRecordContinuation,ready_mother.PersistentReadyMother,native_frame.NativeToneFrame) and
                         type(owner) is atomic.MunichAtomicProgramme,'closed source-generated native Ready and common atomic owner required')
        matrix,error,native_record,geometry,pack,mass_upper=_native_inlet(native_source,native_result,owner,
                                         shared_optical_source,shared_persistent_report)
        collection_a=pack['collections'][0] if collection_a is None else photons.collection_matrix(collection_a)
        collection_b=pack['collections'][1] if collection_b is None else photons.collection_matrix(collection_b)
        splitter=pack['splitter'] if splitter is None else photons.beam_splitter_matrix(splitter)
        efficiencies=pack['efficiencies'] if efficiencies is None else bsm._rates(efficiencies,probabilities=True)
        channel._require((collection_a,collection_b)==pack['collections'] and splitter==pack['splitter'] and
                         efficiencies==pack['efficiencies'],'preparation field must use the original shared four-port optical source')
        plan_count=sum(plan is not None for plan in (phase_plan,local_clock_plan,exact_local_clock_plan))
        channel._require((factorized_local_source is None and factorized_local_report is None and plan_count==1) or
                         (factorized_local_source is not None and factorized_local_report is not None and plan_count==0),
                         'one complete source pair, local compiled, local exact or closed factorized plan is required')
        factor_record=None;tensor_terms=None
        if factorized_local_source is not None:
            matrix,error,endpoints,certificates,factor_record,tensor_terms=_factorized_endpoint(
                factorized_local_source,factorized_local_report,native_record,native_result,owner,matrix,error)
        else:
            if exact_local_clock_plan is not None:
                producer,plan=_exact_local_endpoints,exact_local_clock_plan
            else:
                producer=_pair_endpoints if local_clock_plan is None else _local_endpoints
                plan=phase_plan if local_clock_plan is None else local_clock_plan
            matrix,error,endpoints,certificates=producer(owner,matrix,error,plan,bits)
        flights=tuple(map(full.nonnegative,flight_seconds));g0=full.nonnegative(gate_start_seconds)
        if gate_seconds is not None:
            g0=full.nonnegative(gate_seconds[0])
        channel._require(len(flights)==2 and all(clock+flight<=g0 for clock,flight in zip(endpoints,flights)),
                         'a preparation photon can still reach this gate; its driven matter-field carrier is required')
        kernel=FieldOffPhotonKernel(owner,flight_seconds=flights,emission_origin_seconds=endpoints,
            gate_start_seconds=g0,gate_seconds=gate_seconds,collection_a=collection_a,collection_b=collection_b,
            splitter=splitter,efficiencies=efficiencies)
        self._native,self._native_result,self._owner=native_source,_copy(native_result),owner
        self._shared,self._shared_report=shared_optical_source,_copy(shared_persistent_report)
        self._kernel,self._matrix,self._error=kernel,matrix,error
        self._factorized,self._tensor_terms=factorized_local_source,tensor_terms
        receipt_common=shared_optical_source
        if receipt_common is None:
            receipt_common=optical.CommonOpticalReadout(owner,collection_a=collection_a,collection_b=collection_b,
                splitter=splitter,efficiencies=efficiencies,background_rates=pack['backgrounds'])
        self._receipt_source=_full_receipt_mother(receipt_common,kernel)
        self._value={'schema':PREPARED_SCHEMA,'native_source_record':native_record,
            'native_ready_result':_copy(native_result),'common_atomic_programme':atomic.MunichAtomicProgramme.record(owner),
            'native_inlet_kind':geometry['kind'],'shared_optical_source':pack['shared_record'],
            'common_optical_owner_record':None if shared_optical_source is None else optical.CommonOpticalReadout.record(shared_optical_source),
            'common_persistent_report':_copy(shared_persistent_report),'source_ready_positive_mass_upper':str(mass_upper),
            'raw_shared_four_port_background_rates':list(map(str,pack['backgrounds'])),
            'full_retarded_receipt_time_mother':type(self._receipt_source).record(self._receipt_source),
            'raw_full_pair_plan':_copy(phase_plan),'raw_two_local_clock_plan':_copy(local_clock_plan),
            'raw_exact_local_clock_plan':_copy(exact_local_clock_plan),
            'factorized_local_source_record':factor_record,
            'complete_pair_certificates':certificates,'compilation_bits':bits,
            'source_generated_full_pair_endpoint':channel._input_record(matrix),'upstream_trace_norm_error':str(error),
            'source_local_emission_origins_seconds':list(map(str,endpoints)),'field_kernel':kernel.record(),
            'early_field_gate_disjointness':{'each_side_latest_preparation_arrival_seconds':[str(clock+t) for clock,t in zip(endpoints,flights)],
                'fixed_gate_start_seconds':str(g0),'proved_by_source_control_and_raw_flight':True,
                'claim':'all earlier photons arrive before or at the initially empty half-open BSM gate',
                'native_APD_queue_or_time_mother_deleted':False},
            'native_time_state_mother':_copy(geometry['time_mother']),
            'native_ready_relative_time_recipe':_copy(geometry['time_recipe']),
            'parameter_domain':_copy(geometry['parameter_domain']),'source_support_word':_copy(geometry['source_support_word']),
            'successful_preparation_or_excitation_conditioned':False,'excited_occupation_renormalized':False,
            'native_rolling_APD_field_history_certified_here':False,
            'two_local_clock_endpoint_certified':local_clock_plan is not None or exact_local_clock_plan is not None or factor_record is not None,
            'exact_raw_local_time_action_certified':exact_local_clock_plan is not None or factor_record is not None,
            'same_source_Hermitian_tensor_evaluation':factor_record is not None,
            'joint_endpoint_clock_rule':'(Phi_A tensor Id)(Id tensor Phi_B) on the original complete Ready; each field starts at its own endpoint',
            'actual_scalar_clock_created':False,'full_retry_source_certified':False,
            'actual_hardware_uniquely_identified':False,'controller_advance':False,
            'source_bindings':_bindings(exact=exact_local_clock_plan is not None,factorized=factor_record is not None)}
        self._seal=channel._canonical(self._value)

    @classmethod
    def from_persistent_first_poll(cls,mother,report,common_optical_source,common_persistent_report,*,
                                   local_clock_plan=None,exact_local_clock_plan=None,flight_seconds,gate_start_seconds,gate_seconds=None,bits=160):
        channel._require(cls is PreparedRetardedSource and type(common_optical_source) is optical.CommonOpticalReadout,
                         'closed source-owned first-poll/native/optical producer required')
        retarded._closed(common_optical_source)
        owner=atomic.MunichAtomicProgramme.from_record(optical.CommonOpticalReadout.record(common_optical_source)['common_atomic_owner'])
        return cls(mother,report,owner,flight_seconds=flight_seconds,gate_start_seconds=gate_start_seconds,
            gate_seconds=gate_seconds,bits=bits,local_clock_plan=local_clock_plan,
            exact_local_clock_plan=exact_local_clock_plan,
            shared_optical_source=common_optical_source,shared_persistent_report=common_persistent_report)

    @classmethod
    def from_exact_native_frame(cls,frame,report,common_optical_source,common_persistent_report,*,
                                local_clock_plan=None,exact_local_clock_plan=None,flight_seconds,gate_start_seconds,gate_seconds=None,bits=160):
        channel._require(cls is PreparedRetardedSource and type(frame) is native_frame.NativeToneFrame and
                         type(common_optical_source) is optical.CommonOpticalReadout,
                         'closed exact native-frame first-poll source and original shared optics required')
        retarded._closed(frame);retarded._closed(common_optical_source)
        owner=atomic.MunichAtomicProgramme.from_record(optical.CommonOpticalReadout.record(common_optical_source)['common_atomic_owner'])
        return cls(frame,report,owner,flight_seconds=flight_seconds,gate_start_seconds=gate_start_seconds,
            gate_seconds=gate_seconds,bits=bits,local_clock_plan=local_clock_plan,
            exact_local_clock_plan=exact_local_clock_plan,
            shared_optical_source=common_optical_source,shared_persistent_report=common_persistent_report)

    @classmethod
    def from_factorized_local_source(cls,source,report,common_optical_source,common_persistent_report,*,
                                     flight_seconds,gate_start_seconds,gate_seconds=None,bits=160):
        import factorized_local_phase_source as factors
        channel._require(cls is PreparedRetardedSource and type(source) is factors.FactorizedLocalPhaseSource and
                         type(common_optical_source) is optical.CommonOpticalReadout,
                         'closed same-source factorized local action and original shared optics required')
        raw=factors.FactorizedLocalPhaseSource.record(source)
        frame=native_frame.NativeToneFrame.from_record(raw['native_source_record'])
        owner=atomic.MunichAtomicProgramme.from_record(raw['common_atomic_owner'])
        return cls(frame,raw['native_ready_report'],owner,flight_seconds=flight_seconds,gate_start_seconds=gate_start_seconds,
            gate_seconds=gate_seconds,bits=bits,shared_optical_source=common_optical_source,
            shared_persistent_report=common_persistent_report,factorized_local_source=source,factorized_local_report=report)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('prepared retarded source execution changed')
        _guard();retarded._closed(self);retarded._closed(self._native);retarded._closed(self._owner)
        channel._require(type(self) is PreparedRetardedSource and channel._canonical(self._value)==self._seal and
            self._value['source_bindings']==_bindings(exact=self._value['raw_exact_local_clock_plan'] is not None,
                factorized=self._value['factorized_local_source_record'] is not None) and
            type(self._native) in (continuation.JointRecordContinuation,ready_mother.PersistentReadyMother,native_frame.NativeToneFrame) and
            type(self._native).record(self._native)==self._value['native_source_record'] and
            self._native_result==self._value['native_ready_result'] and
            atomic.MunichAtomicProgramme.record(self._owner)==self._value['common_atomic_programme'] and
            FieldOffPhotonKernel.record(self._kernel)==self._value['field_kernel'] and
            channel._input_record(self._matrix)==self._value['source_generated_full_pair_endpoint'] and
            self._error==Q(self._value['upstream_trace_norm_error']),
            'native lineage, complete prepared endpoint, shared price or photon time mother changed')
        if self._factorized is not None:
            import factorized_local_phase_source as factors
            channel._require(type(self._factorized) is factors.FactorizedLocalPhaseSource and
                factors.FactorizedLocalPhaseSource.record(self._factorized)==self._value['factorized_local_source_record'],
                'same-source local factor mother changed')
            certificate=self._value['complete_pair_certificates'][0]['complete_factorized_local_certificate']
            terms=tuple((channel._read_input(item['left']['local_poststate'],full.DIMENSION),
                         channel._read_input(item['right']['local_poststate'],full.DIMENSION)) for item in certificate['tensor_terms'])
            channel._require(self._tensor_terms==terms,'source-issued tensor endpoint factors changed')
        else:
            channel._require(self._value['factorized_local_source_record'] is None and self._tensor_terms is None,
                             'source cannot discard its exact local factor mother')
        if self._shared is not None:
            retarded._closed(self._shared)
            channel._require(type(self._shared) is optical.CommonOpticalReadout and
                optical.CommonOpticalReadout.record(self._shared)==self._value['common_optical_owner_record'] and
                self._shared_report==self._value['common_persistent_report'],'shared optical or original persistent source changed')
        else:
            channel._require(self._value['common_optical_owner_record'] is None and self._shared_report is None,
                             'source cannot discard its common optical owner')
        import retarded_receipt_source as receipt
        channel._require(receipt._guard is receipt._GUARD and receipt._guard.__code__ is receipt._GUARD_CODE,
                         'retarded receipt source execution changed')
        receipt._GUARD()
        channel._require(type(self._receipt_source) is receipt.RetardedReceiptSource and
                         receipt.RetardedReceiptSource.record(self._receipt_source)==self._value['full_retarded_receipt_time_mother'],
                         'complete field/BG/Mark mother changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        channel._require(cls is PreparedRetardedSource and type(record) is dict and record.get('schema')==PREPARED_SCHEMA,
                         'closed source-born prepared photon record required')
        field=FieldOffPhotonKernel.from_record(record['field_kernel']);raw=field.record()
        decode=lambda matrix:tuple(tuple(channel._complex_record(x) for x in row) for row in matrix)
        factories={'complete native resolvent Ready':continuation.JointRecordContinuation,
                   'first PC-ready at the original first poll':ready_mother.PersistentReadyMother,
                   'exact native-frame Ready at the original first poll':native_frame.NativeToneFrame}
        channel._require(record['native_inlet_kind'] in factories,'named original native inlet required')
        factory=factories[record['native_inlet_kind']]
        factor_source=None;factor_report=None
        if record.get('factorized_local_source_record') is not None:
            import factorized_local_phase_source as factors
            factor_source=factors.FactorizedLocalPhaseSource.from_record(record['factorized_local_source_record'])
            factor_report=record['complete_pair_certificates'][0]['complete_factorized_local_certificate']
        result=cls(factory.from_record(record['native_source_record']),record['native_ready_result'],
            atomic.MunichAtomicProgramme.from_record(record['common_atomic_programme']),record['raw_full_pair_plan'],
            flight_seconds=raw['raw_flight_seconds'],gate_start_seconds=raw['raw_gate_seconds'][0],
            gate_seconds=None if raw['default_public_120ns_gate'] else raw['raw_gate_seconds'],
            collection_a=decode(raw['raw_collection'][0]),collection_b=decode(raw['raw_collection'][1]),
            splitter=decode(raw['raw_splitter']),efficiencies=raw['raw_efficiencies'],
            bits=record['compilation_bits'],local_clock_plan=record['raw_two_local_clock_plan'],
            exact_local_clock_plan=record.get('raw_exact_local_clock_plan'),
            factorized_local_source=factor_source,factorized_local_report=factor_report,
            shared_optical_source=None if record['common_optical_owner_record'] is None else
                                   optical.CommonOpticalReadout.from_record(record['common_optical_owner_record']),
            shared_persistent_report=record['common_persistent_report'])
        channel._require(result.record()==record,'native/preparation/field producer does not reconstruct the same source')
        return result

    def interval(self,left=None,right=None,*,bits=160):
        source_record=self.record();a,z=map(Q,self._kernel.record()['raw_gate_seconds'])
        report=FieldOffPhotonKernel._instrument(self._kernel,self._matrix,
            a if left is None else full.exact(left),z if right is None else full.exact(right),a,z,bits,self._error,
            tensor_terms=self._tensor_terms)
        # No BG in the entire gate is a source event, with no renormalization.
        # All other BG worlds are a positive packet of this one common source.
        rate=sum(map(Q,self._value['raw_shared_four_port_background_rates']),Q(0))
        survival,survival_error=retarded._exp_negative(rate*(z-a)/Q(self._value['common_atomic_programme']['atomic_base']['seconds_per_unit']),bits)
        matrices=tuple({(i,j):channel._complex_record(v) for i,j,v in row} for row in report['four_pattern_poststates'])
        signal_error=Q(report['global_trace_norm_error'])
        report['source_event_mass_lower']=_positive_packet_mass_lower(matrices,signal_error,survival,survival_error,bits)
        report['source_pattern_mass_lowers']=[{'pattern':index,**_positive_packet_mass_lower((matrix,),signal_error,survival,survival_error,bits)}
                                            for index,matrix in enumerate(matrices)]
        centre_norm=sum((bsm._entry_norm(matrix,bits=bits) for matrix in matrices),Q(0))
        background_tail=Q(self._value['source_ready_positive_mass_upper'])*min(Q(1),max(Q(0),1-survival+survival_error))
        report['four_pattern_poststates']=[channel._input_record({k:v*survival for k,v in matrix.items()}) for matrix in matrices]
        report['source_BG_free_gate_probability_center']=str(survival)
        report['source_BG_free_gate_probability_error']=str(survival_error)
        report['source_positive_BG_receipt_remainder_mass_upper']=str(background_tail)
        report['source_BG_scalar_error']=str(survival_error*centre_norm)
        report['global_trace_norm_error']=str(Q(report['global_trace_norm_error'])+survival_error*centre_norm+background_tail)
        report['full_shared_BG_first_receipt_enclosed']=True
        report['BG_worlds_not_deleted_or_conditionally_renormalized']=True
        report['exact_BG_remainder_state_time_mother']=_copy(self._value['full_retarded_receipt_time_mother'])
        report['source_preparation_record']=source_record
        report['parameter_domain']=_copy(self._value['parameter_domain'])
        report['source_support_word']=_copy(self._value['source_support_word'])
        report['complete_time_state_mother']=_copy(self._value['native_time_state_mother'])
        return report

    def verify(self,report):
        self.record()
        channel._require(type(report) is dict and report.get('schema')==INSTRUMENT_SCHEMA and
                         report.get('source_preparation_record')==self.record(),'same prepared photon source report required')
        a,z=report['restriction_seconds']
        channel._require(PreparedRetardedSource.interval(self,a,z,bits=report['scalar_bits'])==report,
                         'complete endpoint, receipt quantum measure, source domain or whole price changed')
        return True


def _guard():
    if _execution is not _EXECUTION_FUNCTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED_EXECUTION:
        raise ValueError('prepared retarded source execution changed')


_EXECUTION_FUNCTION=_execution
_EXECUTION_CODE=_execution.__code__
_GUARD_FUNCTION=_guard
_GUARD_CODE=_guard.__code__
_EXPECTED_EXECUTION=_execution()
