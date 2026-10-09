"""Canonical F0 emission retains photons through two raw flight clocks.

The fixed one-shot source emits a coherent atom/polarization/time leg from
the original natural jump columns.  A gate latches only its own two clicks;
restrictions of its first-receipt measure retain the earlier in-gate click.
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
import munich_atomic_programme as atomic


SCHEMA = 'stage10-canonical-retarded-F0-photon-source/v1'
MEASURE_SCHEMA = 'stage10-retarded-canonical-first-receipt-measure/v1'
C = dipole.ComplexRadical
ZERO = C()
C_LIGHT = Q(299792458)


def _copy(value):
    return json.loads(channel._canonical(value))


def _closed(value):
    for base in type(value).__mro__:
        for name, member in vars(base).items():
            if callable(member) or isinstance(member, (property, classmethod, staticmethod)):
                channel._require(name not in vars(value), 'source operations cannot be instance callbacks')


def _bindings():
    modules = (atomic, dipole, full, modes, photons, bsm, channel, joint)
    paths = {Path(__file__).resolve(), *(Path(module.__file__).resolve() for module in modules)}
    return {path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(paths)}


def _function(value):
    value = getattr(value, '__func__', value)
    return (id(value), id(getattr(value, '__code__', None)),
            repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None)))


def _execution():
    functions = (_copy, _closed, _bindings, _function, _execution, _guard, _norm, _outer, _add,
        _interval, _product, _square, _difference, _exp_negative, _cdf, _source_law, _path_vectors,
        atomic.MunichAtomicProgramme.record, atomic.MunichAtomicProgramme.atomic_base,
        atomic.AtomicBase.segment, atomic.AtomicBase.record, joint._source,
        joint.local.CounterGenerator.__init__, joint.local.CounterGenerator.atomic_action,
        joint.local.natural_channels, joint.JointCounterGenerator.__init__,
        atomic.MunichAtomicProgramme.bsm_gate, bsm.BSMSource.__init__, bsm._rates,
        joint.JointCounterGenerator.detected_action, bsm.BSMSource.port_action,
        photons.emission_amplitudes, photons.collected_amplitudes, photons.bsm_bras,
        photons.collection_matrix, photons.beam_splitter_matrix, photons.ideal_collection, photons.model_metadata,
        photons.balanced_beam_splitter, modes.complex_exponential, full.radical_midpoint)
    methods = tuple(_function(value) for value in vars(RetardedPhotonSource).values()
                    if callable(value) or isinstance(value, (classmethod, staticmethod)))
    return (tuple(map(_function,functions)), methods, tuple(bsm.PATTERNS), tuple(bsm.PORTS), bsm.GATE_SECONDS,
            tuple(photons.HERALD_PATTERNS), tuple(photons.POLARIZATIONS), tuple(photons.ATOM_BASIS),
            tuple(photons.PAIR_BASIS), C_LIGHT, SCHEMA, MEASURE_SCHEMA, joint.DIMENSION)


def _norm(matrix, bits=160):
    return bsm._entry_norm(matrix,bits=bits)


def _outer(first, second):
    return {(i,j):a*b.conjugate() for i,a in first.items() for j,b in second.items() if a and b}


def _add(target, matrix, factor=1):
    for key,value in matrix.items():
        joint.local._add(target,key,value*factor)


def _interval(center, error, *, lower=Q(0), upper=Q(1)):
    a,z=max(lower,center-error),min(upper,center+error)
    channel._require(a<=z,'outward scalar source enclosure is inconsistent')
    return (a+z)/2,(z-a)/2


def _product(first, second):
    a,e=first;b,f=second
    return ((a-e)*(b-f)+(a+e)*(b+f))/2,((a+e)*(b+f)-(a-e)*(b-f))/2


def _square(value):
    return _product(value,value)


def _difference(first, second):
    return _interval(first[0]-second[0],first[1]+second[1])


def _exp_negative(argument, bits):
    channel._require(argument>=0,'nonnegative source decay argument required')
    if not argument:
        return Q(1),Q(0)
    scalar,error=modes.complex_exponential(-argument,0,bits=bits)
    return _interval(scalar[0],error)


def _cdf(gamma, origin, time, bits):
    if time is None:
        return Q(1),Q(0)
    if time<=origin:
        return Q(0),Q(0)
    center,error=_exp_negative(gamma*(time-origin),bits)
    return 1-center,error


def _source_law(owner):
    channel._require(type(owner) is atomic.MunichAtomicProgramme,
                     'closed common atomic programme required; a prepared state or wavepacket is not input')
    _closed(owner)
    parent=atomic.MunichAtomicProgramme.record(owner)
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    channel._require(all(Q(x)==0 for x in base.record()['magnetic_fields']),
                     'this named single-emission source requires B=0')
    e=dipole.INDEX[dipole.State('D2',0,0)]
    g=dipole.INDEX[dipole.State('ground',1,0)]
    atoms=tuple(joint._source(base.segment(side,1)) for side in (0,1))
    gamma=atoms[0].outgoing[e]
    channel._require(gamma>0 and atoms[1].outgoing[e]==gamma and
                     all(atom.program.gammas['D2',0]==gamma for atom in atoms),
                     'one common positive F0 natural width required')
    emission=photons.emission_amplitudes()
    checks=[]
    for side,atom in enumerate(atoms):
        amplitudes={}
        for jump in atom.jumps:
            for (target,source),value in jump.matrix.items():
                if source==e and value:
                    channel._require(jump.label[:3]==('D2',0,1),
                                     'the canonical F0 source changed its original emission sector')
                    joint.local._add(amplitudes,(target,jump.label[3]),
                        value*dipole.sqrt_rational(atom.program.gammas[jump.label[:2]]))
        expected={key:value*dipole.sqrt_rational(gamma) for key,value in emission.items()}
        channel._require(amplitudes==expected,'time leg must use the original normalized natural jump columns')
        channel._require(not any(i!=j for i,j in atom.hamiltonian) and not any(atom.program.ion_rates.values()) and
                         all(atom.outgoing[i]==0 for i in photons.ATOM_BASIS),
                         'the single-emission field-off source must preserve its emitted ground sector')
        checks.append({'side':side,'raw_atom':atom.program.record(),
                       'natural_F0_columns':[[i,q,v.serialize()] for (i,q),v in sorted(amplitudes.items())]})
    unit=Q(parent['atomic_base']['seconds_per_unit'])
    frequency=(atoms[0].hamiltonian.get((e,e),ZERO)-atoms[0].hamiltonian.get((g,g),ZERO)).real.as_rational()/unit
    return parent,{'canonical_emission':photons.model_metadata(),'source_atoms':checks,
        'canonical_excited_index':e,'natural_width_per_source_unit':str(gamma),
        'seconds_per_source_unit':str(unit),'decay_rate_per_second':str(gamma/unit),
        'optical_angular_frequency_per_second':str(frequency),
        'preparation_scope':'the original named successful canonical F0 emission; full raw preparation is its next consumer'}


def _path_vectors(collections, splitter, efficiencies):
    sides=tuple(photons.collected_amplitudes(matrix) for matrix in collections)
    bras=photons.bsm_bras(splitter)
    paths=[]
    for index,bra in enumerate(bras):
        (dp,ds),(ep,es)=bra.detectors
        ports=tuple(bsm.PORTS.index(port) for port in bra.detectors)
        amplitude=C(dipole.sqrt_rational(efficiencies[ports[0]]*efficiencies[ports[1]]))
        first,second={},{}
        for (a,pa),x in sides[0].items():
            for (b,pb),y in sides[1].items():
                key=joint.atom_pair_index(a,b)
                if pa==ds and pb==es:
                    joint.local._add(first,key,amplitude*x*y*splitter[dp-1][0]*splitter[ep-1][1])
                if pa==es and pb==ds:
                    joint.local._add(second,key,amplitude*x*y*splitter[ep-1][0]*splitter[dp-1][1])
                combined=amplitude*x*y*bra.coefficients.get((pa,pb),ZERO)
                expected=(amplitude*x*y*(splitter[dp-1][0]*splitter[ep-1][1] if pa==ds and pb==es else ZERO)+
                          amplitude*x*y*(splitter[ep-1][0]*splitter[dp-1][1] if pa==es and pb==ds else ZERO))
                channel._require(combined==expected,'the two time paths must retain the original Bose BSM bra')
        paths.append((first,second))
    return tuple(paths)


class RetardedPhotonSource:
    def __init__(self, owner, *, flight_seconds, emission_origin_seconds=(0,0), gate_start_seconds=0, gate_seconds=None,
                 collection_a=None, collection_b=None, splitter=None, efficiencies=(1,1,1,1), fibre_coordinates=None):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded source execution changed')
        _guard()
        channel._require(type(self) is RetardedPhotonSource,'closed canonical retarded source required')
        parent,law=_source_law(owner)
        channel._require(type(flight_seconds) in (tuple,list) and len(flight_seconds)==2 and
                         type(emission_origin_seconds) in (tuple,list) and len(emission_origin_seconds)==2,
                         'two raw emission clocks and two raw photon flights required')
        flights=tuple(map(full.nonnegative,flight_seconds));origins=tuple(map(full.nonnegative,emission_origin_seconds))
        arrivals=tuple(a+b for a,b in zip(origins,flights))
        default_gate=gate_seconds is None
        start=full.nonnegative(gate_start_seconds)
        gate=(start,start+bsm.GATE_SECONDS) if default_gate else tuple(map(full.exact,gate_seconds))
        channel._require(len(gate)==2 and 0<=gate[0]<=gate[1],'ordered raw physical arrival gate required')
        collections=tuple(map(photons.collection_matrix,(photons.ideal_collection() if collection_a is None else collection_a,
                              photons.ideal_collection() if collection_b is None else collection_b)))
        splitter=photons.beam_splitter_matrix(photons.balanced_beam_splitter() if splitter is None else splitter)
        efficiencies=bsm._rates(efficiencies,probabilities=True)
        if fibre_coordinates is not None:
            channel._require(type(fibre_coordinates) is dict and set(fibre_coordinates)=={'length_metres','group_indices'},
                             'raw fibre lengths and group indices required')
            lengths=tuple(map(full.nonnegative,fibre_coordinates['length_metres']))
            indices=tuple(map(full.exact,fibre_coordinates['group_indices']))
            channel._require(len(lengths)==len(indices)==2 and all(x>0 for x in lengths) and all(x>=1 for x in indices) and
                             flights==tuple(l*n/C_LIGHT for l,n in zip(lengths,indices)),
                             'the same source fibre coordinates must generate the raw flight clocks')
            fibre_coordinates={'length_metres':list(map(str,lengths)),'group_indices':list(map(str,indices))}
        self._owner=owner
        self._paths=_path_vectors(collections,splitter,efficiencies)
        self._value={'schema':SCHEMA,'common_atomic_programme':parent,'emission_source_law':law,
            'raw_flight_seconds':list(map(str,flights)),'raw_emission_origin_seconds':list(map(str,origins)),
            'source_arrival_origins_seconds':list(map(str,arrivals)),'raw_gate_seconds':list(map(str,gate)),
            'default_public_120ns_gate':default_gate,'raw_fibre_coordinates':fibre_coordinates,
            'raw_collection':[[[v.serialize() for v in row] for row in matrix] for matrix in collections],
            'raw_splitter':[[v.serialize() for v in row] for row in splitter],
            'raw_efficiencies':list(map(str,efficiencies)),
            'source_Bose_paths':[{'first':[[i,v.serialize()] for i,v in sorted(a.items())],
                                 'second':[[i,v.serialize()] for i,v in sorted(b.items())]} for a,b in self._paths],
            'time_carrier':{'single_leg':'ground atom tensor polarization q tensor L2 emission-time field; vacuum retained',
                'time_amplitude':'sqrt(Gamma)*exp(-(Gamma/2+i*omega)*(arrival-emission_origin-flight)) on its causal half-line',
                'propagation':'the photon time leg shifts by its own raw flight; atoms do not wait excited for that flight',
                'off_diagonal_emission_time_and_Bose_source_paths_retained':True,
                'gate_rule':'both APD clicks lie in the fixed original gate; first receipt is their later arrival',
                'unknown_flight_and_fibre_coordinates_are_inverse_variables':True},
            'actual_preparation_identified':False,'actual_fibre_coordinates_identified':False,
            'full_retry_source_certified':False,'actual_hardware_uniquely_identified':False,
            'controller_advance':False,'source_bindings':_bindings()}
        self._seal=channel._canonical(self._value)
        self._execution=_execution()

    @classmethod
    def from_fibre_coordinates(cls, owner, *, lengths_metres, group_indices, **kwargs):
        channel._require(cls is RetardedPhotonSource,'closed fibre-source factory required')
        lengths=tuple(map(full.exact,lengths_metres));indices=tuple(map(full.exact,group_indices))
        channel._require(len(lengths)==len(indices)==2,'both raw fibre coordinate pairs required')
        return cls(owner,flight_seconds=tuple(l*n/C_LIGHT for l,n in zip(lengths,indices)),
                   fibre_coordinates={'length_metres':list(map(str,lengths)),'group_indices':list(map(str,indices))},**kwargs)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('retarded source execution changed')
        _guard()
        _closed(self);_closed(self._owner)
        channel._require(type(self) is RetardedPhotonSource and self._execution==_execution() and
                         channel._canonical(self._value)==self._seal and self._value['source_bindings']==_bindings() and
                         atomic.MunichAtomicProgramme.record(self._owner)==self._value['common_atomic_programme'] and
                         [{'first':[[i,v.serialize()] for i,v in sorted(a.items())],
                           'second':[[i,v.serialize()] for i,v in sorted(b.items())]} for a,b in self._paths]==
                             self._value['source_Bose_paths'],
                         'the emission, field, optical or clock source changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls, record):
        channel._require(cls is RetardedPhotonSource and type(record) is dict and record.get('schema')==SCHEMA,
                         'closed retarded canonical source record required')
        owner=atomic.MunichAtomicProgramme.from_record(record['common_atomic_programme'])
        decode=lambda matrix:tuple(tuple(channel._complex_record(value) for value in row) for row in matrix)
        result=cls(owner,flight_seconds=record['raw_flight_seconds'],
            emission_origin_seconds=record['raw_emission_origin_seconds'],
            gate_start_seconds=record['raw_gate_seconds'][0],
            gate_seconds=None if record['default_public_120ns_gate'] else record['raw_gate_seconds'],
            collection_a=decode(record['raw_collection'][0]),collection_b=decode(record['raw_collection'][1]),
            splitter=decode(record['raw_splitter']),efficiencies=record['raw_efficiencies'],
            fibre_coordinates=record['raw_fibre_coordinates'])
        channel._require(result.record()==record,'retarded source or its physical scope differs')
        return result

    def _weights(self, time, gate_origin, bits):
        gamma=Q(self._value['emission_source_law']['decay_rate_per_second'])
        arrivals=tuple(map(Q,self._value['source_arrival_origins_seconds']))
        if time is not None and time<=max(gate_origin,*arrivals):
            return (Q(0),Q(0)),(Q(0),Q(0))
        masses=tuple(_difference(_cdf(gamma,a,time,bits),_cdf(gamma,a,gate_origin,bits)) for a in arrivals)
        overlap_mass=_difference(_cdf(gamma,max(arrivals),time,bits),_cdf(gamma,max(arrivals),gate_origin,bits))
        visibility=_exp_negative(gamma*abs(arrivals[0]-arrivals[1]),bits)
        return _product(*masses),_product(visibility,_square(overlap_mass))

    def _measure(self, left, right, gate_origin, gate_end, bits, scope):
        source_record=self.record()
        channel._require(type(bits) is int and 64<=bits<=1024,'registered outward scalar precision required')
        if right is not None:
            channel._require(left<=right and (gate_end is None or right<=gate_end),'restriction outside the original arrival gate')
        channel._require(left>=gate_origin,'a time restriction cannot reset the original gate origin')
        w0,c0=self._weights(left,gate_origin,bits);w1,c1=self._weights(right,gate_origin,bits)
        w,c=_difference(w1,w0),_difference(c1,c0)
        if right==left:
            w=c=(Q(0),Q(0))
        matrices,error=[],Q(0)
        for first,second in self._paths:
            diagonal=_outer(first,first);_add(diagonal,_outer(second,second))
            cross=_outer(first,second);_add(cross,_outer(second,first))
            matrix={};_add(matrix,diagonal,w[0]);_add(matrix,cross,c[0]);matrices.append(matrix)
            error+=w[1]*_norm(diagonal,bits)+c[1]*_norm(cross,bits)
        return _copy({'schema':MEASURE_SCHEMA,'source_record':source_record,'observation_scope':scope,'scalar_bits':bits,
            'gate_origin_seconds':str(gate_origin),'gate_end_seconds':None if gate_end is None else str(gate_end),
            'restriction_seconds':[str(left),None if right is None else str(right)],
            'source_temporal_Gram':{'diagonal_weight_center':str(w[0]),'diagonal_weight_error':str(w[1]),
                'Bose_cross_weight_center':str(c[0]),'Bose_cross_weight_error':str(c[1]),
                'law':'gate cumulative Gram: Xi(T)=Fi(T)-Fi(G0); overlap integrates from G0; restricted mu is cumulative(V)-cumulative(U)',
                'exact_Gram_positive':'W >= abs(C) by Cauchy-Schwarz on the same original two-click time domain'},
            'four_pattern_poststates':[channel._input_record(matrix) for matrix in matrices],
            'pattern_inventory':[{'pattern_index':i,'physical_herald':name,'ports':list(ports)}
                                 for i,(name,ports) in enumerate(bsm.PATTERNS)],
            'global_trace_norm_error':str(error),'error_scope':'whole four-pattern quantum time instrument; scalar prices summed once',
            'pair_dimension':joint.DIMENSION,'atomic_poststate_clock':'at the second in-gate photon arrival; canonical B0 ground evolution is identity',
            'first_click_before_restriction_left_retained':True,'gate_pre_click_latched':False,
            'time_measure_mother':'same atom-polarization-time legs, all field/loss sectors and original gate origin',
            'exact_poststates_positive':True,'numerical_centres_assumed_positive':False,
            'input_prepared_density_or_wavepacket_supplied':False,'solver_executed':False,
            'full_retry_source_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False})

    def interval(self, left=None, right=None, *, bits=160):
        self.record()
        a,z=map(Q,self._value['raw_gate_seconds'])
        return self._measure(a if left is None else full.exact(left),z if right is None else full.exact(right),a,z,bits,
                             'fixed raw arrival gate first-receipt restriction')

    def whole_wavepacket(self, *, bits=160):
        self.record()
        origin=min(map(Q,self._value['source_arrival_origins_seconds']))
        return self._measure(origin,None,origin,None,bits,'ungated canonical one-shot comparison')

    def leg_amplitude(self, side, arrival_time, *, bits=160):
        source=self.record()
        channel._require(type(side) is int and side in (0,1) and type(bits) is int and 64<=bits<=1024,
                         'source side and registered scalar precision required')
        time=full.exact(arrival_time)
        gamma=Q(source['emission_source_law']['decay_rate_per_second'])
        frequency=Q(source['emission_source_law']['optical_angular_frequency_per_second'])
        flight=Q(source['raw_flight_seconds'][side]);origin=Q(source['raw_emission_origin_seconds'][side])
        age=time-flight-origin
        if age<0:
            value,error=ZERO,Q(0)
        else:
            scalar,radius=modes.complex_exponential(-gamma*age/2,-frequency*age,bits=bits)
            factor=C(dipole.sqrt_rational(gamma))
            value=factor*C(*scalar);error=_norm({(0,0):factor},bits)*radius
        return {'side':side,'arrival_time_seconds':str(time),'source_emission_time_seconds':str(time-flight),
            'relative_emission_age_seconds':str(age),'amplitude_center':value.serialize(),
            'amplitude_absolute_error':str(error),'source_record':source,'scalar_bits':bits,
            'time_leg_classicalized_before_detection':False}

    def pair_amplitude(self, pattern_index, first_detector_time, second_detector_time, *, bits=160):
        self.record()
        channel._require(type(pattern_index) is int and 0<=pattern_index<4,'one original detector pattern required')
        a=self.leg_amplitude(0,first_detector_time,bits=bits);b=self.leg_amplitude(1,second_detector_time,bits=bits)
        c=self.leg_amplitude(0,second_detector_time,bits=bits);d=self.leg_amplitude(1,first_detector_time,bits=bits)
        def product(x,y):
            u,v=channel._complex_record(x['amplitude_center']),channel._complex_record(y['amplitude_center'])
            e,f=Q(x['amplitude_absolute_error']),Q(y['amplitude_absolute_error'])
            return u*v,e*_norm({(0,0):v},bits)+f*_norm({(0,0):u},bits)+e*f
        first,e=product(a,b);second,f=product(c,d)
        x,y=self._paths[pattern_index];vector={}
        _add(vector,x,first);_add(vector,y,second)
        error=e*_norm({(i,0):v for i,v in x.items()},bits)+f*_norm({(i,0):v for i,v in y.items()},bits)
        return {'pattern_index':pattern_index,'detector_time_seconds':[str(full.exact(first_detector_time)),
                    str(full.exact(second_detector_time))],
            'first_receipt_time_seconds':str(max(full.exact(first_detector_time),full.exact(second_detector_time))),
            'full_pair_amplitude':[[i,v.serialize()] for i,v in sorted(vector.items())],
            'vector_norm_error_upper':str(error),'scalar_bits':bits,'source_record':self.record(),
            'Bose_paths_interfere_before_photon_trace':True}

    def verify(self, report):
        channel._require(type(report) is dict and report.get('schema')==MEASURE_SCHEMA and
                         report.get('source_record')==self.record(),'same retarded emission source measure required')
        if report['observation_scope']=='ungated canonical one-shot comparison':
            expected=self.whole_wavepacket(bits=report.get('scalar_bits',160))
        else:
            a,z=report['restriction_seconds'];expected=self.interval(a,z,bits=report.get('scalar_bits',160))
        channel._require(expected==report,'time gate, source paths, full poststate or shared error changed')
        return True

    def inventory_at(self, physical_time, *, bits=160):
        source_record=self.record();time=full.exact(physical_time)
        gamma=Q(self._value['emission_source_law']['decay_rate_per_second']);legs=[]
        for side,(origin,flight) in enumerate(zip(map(Q,self._value['raw_emission_origin_seconds']),map(Q,self._value['raw_flight_seconds']))):
            emitted=_cdf(gamma,origin,time,bits);arrived=_cdf(gamma,origin+flight,time,bits)
            flight_mass=_difference(emitted,arrived)
            legs.append({'side':side,'not_yet_emitted_center':str(1-emitted[0]),'not_yet_emitted_error':str(emitted[1]),
                'source_not_yet_started_center':'1' if time<origin else '0',
                'canonical_excited_survival_center':'0' if time<origin else str(1-emitted[0]),
                'canonical_excited_survival_error':'0' if time<origin else str(emitted[1]),
                'photon_in_flight_center':str(flight_mass[0]),'photon_in_flight_error':str(flight_mass[1]),
                'already_arrived_center':str(arrived[0]),'already_arrived_error':str(arrived[1]),
                'not_yet_excitation_origin':time<origin})
        return {'source_record':source_record,'physical_time_seconds':str(time),'legs':legs,
                'one_source_inventory_per_leg':True,'photon_absence_inferred_from_ground_atom':False,
                'loss_and_unobserved_field_sectors_remain_in_mother':True}

    def ground_shadow(self):
        self.record();one={}
        for (atom,q),amplitude in photons.emission_amplitudes().items():
            joint.local._add(one,(atom,atom),amplitude*amplitude.conjugate())
        return {(joint.atom_pair_index(a,b),joint.atom_pair_index(c,d)):x*y
                for (a,c),x in one.items() for (b,d),y in one.items()}

    def instant_shadow_flux(self):
        self.record()
        decode=lambda matrix:tuple(tuple(channel._complex_record(v) for v in row) for row in matrix)
        raw,_=atomic.MunichAtomicProgramme.bsm_gate(self._owner,
            collection_a=decode(self._value['raw_collection'][0]),collection_b=decode(self._value['raw_collection'][1]),
            efficiencies=tuple(map(Q,self._value['raw_efficiencies'])),background_rates=(0,0,0,0),
            splitter=decode(self._value['raw_splitter']))
        shadow=self.ground_shadow()
        return tuple(raw.port_action(shadow,port) for port in range(4))


def _guard():
    if _execution is not _EXECUTION_FUNCTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED_EXECUTION:
        raise ValueError('retarded source execution changed')


_EXECUTION_FUNCTION=_execution
_EXECUTION_CODE=_execution.__code__
_GUARD_FUNCTION=_guard
_GUARD_CODE=_guard.__code__
_EXPECTED_EXECUTION=_execution()
