"""Continuous full Mark/quantum curves are checked against their own source.

Modes are numerical proposals, not eigenvalue or hardware premises.  Exact
source frequencies shift the residual words before equal words are combined.
The complete curve is Hermitian projected, and the true stopped CPTP flow
contracts its integrated defect.  Endpoint exponential error is kept separate
from the uniform curve enclosure.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json

import retarded_gaussian_trajectory_source as trajectory
import prepared_retarded_gaussian_inlet as inlet
import retarded_receipt_activity_envelope as activity

field, gaussian, full, dipole, channel, joint, bsm = (trajectory.field, trajectory.gaussian,
    trajectory.full, trajectory.dipole, trajectory.channel, trajectory.joint, trajectory.bsm)
fourier = trajectory.density.fourier
SCHEMA = 'stage10-source-retarded-continuous-receipt-trajectory-certificate/v1'
_SOURCE_CHECK, _INLET_CHECK, _ACTIVITY_CHECK = trajectory._CHECK, inlet._CHECK, activity._CHECK
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in
          (trajectory, inlet, activity, gaussian, fourier, field, full, dipole, channel, joint, bsm)))}


def _key(key):
    mark, i, j = key
    return trajectory._key(mark), i, j


def _record_state(state):
    return [[list(m.counts), m.receipt, i, j, z.serialize()] for (m, i, j), z in sorted(state.items(), key=lambda x:_key(x[0])) if z]


def _read_state(raw, source):
    if type(raw) is dict:
        result = dict(raw)
    else:
        _require(type(raw) is list, 'complete original marked state required')
        result = {}
        for row in raw:
            _require(type(row) is list and len(row) == 5, 'original Mark and full pair matrix coordinates required')
            counts, receipt, i, j, z = row
            _require(type(counts) is list, 'literal original count tuple required')
            key = bsm.Mark(tuple(counts), receipt), i, j
            _require(key not in result, 'original marked matrix coordinates must be unique')
            result[key] = channel._complex_record(z)
    trajectory.RetardedGaussianTrajectorySource._blocks(source, result)
    _require(all(result.get((m, j, i), dipole.ComplexRadical()) == z.conjugate() for (m, i, j), z in result.items()),
             'complete Hermitian marked input required; its numerical centre need not be positive')
    return result


def _pairs(state, bits):
    result, rounding = full._midpoint_matrix({(n, 0):z for n, z in enumerate(state.values())}, bits)
    keys = tuple(state); answer = {keys[n]:pair for (n, _), pair in result.items()}
    answer, quantization = fourier.exact._dyadic_state(answer, bits)
    return answer, sum(rounding.values(), Q(0))+quantization


def _exact(pairs):
    return {key:dipole.ComplexRadical(*value) for key, value in pairs.items() if value != (0, 0)}


def _add(target, state, factor=(Q(1), Q(0))):
    fourier._add_rational(target, state, factor)


def _norm(state):
    return sum((abs(a)+abs(b) for a,b in state.values()), Q(0))


def _hermitian(state):
    result = {}; keys = set(state)|{(m,j,i) for m,i,j in state}
    for m,i,j in keys:
        a,b = state.get((m,i,j),(Q(0),Q(0))); c,d = state.get((m,j,i),(Q(0),Q(0)))
        value = (a+c)/2, (b-d)/2
        if value != (0, 0):
            result[m,i,j] = value
    return result


def _difference(first, second):
    result = dict(first); _add(result, second, (Q(-1), Q(0)))
    return _norm(result)


def _power(value, n):
    result = dipole.ComplexRadical(1)
    for _ in range(n):
        result *= value
    return result


def _rows(state, bits):
    q = 1 << bits
    return [[list(m.counts), m.receipt, i, j, int(a*q), int(b*q)]
            for (m,i,j),(a,b) in sorted(state.items(), key=lambda x:_key(x[0])) if a or b]


def _coefficient(rows, bits, source):
    _require(type(rows) is list, 'complete dyadic marked coefficient required')
    result = {}; q = 1 << bits
    for row in rows:
        _require(type(row) is list and len(row) == 6 and type(row[0]) is list and
                 all(type(n) is int for n in row[2:]), 'original Mark and dyadic full pair entries required')
        counts, receipt, i, j, a, b = row; mark = bsm.Mark(tuple(counts), receipt)
        key = mark, i, j
        _require(key not in result and (a or b), 'canonical unique nonzero coefficient required')
        trajectory.RetardedGaussianTrajectorySource._blocks(source, {key:dipole.ComplexRadical(1)})
        result[key] = Q(a,q), Q(b,q)
    return result


def _modes(piece, bits, source):
    _require(type(piece) is dict and set(piece) == {'duration_seconds','modes'} and type(piece['modes']) is list and piece['modes'],
             'untrusted complete exponential-polynomial source piece required')
    width = full.exact(piece['duration_seconds']); _require(width > 0, 'positive source duration required')
    groups = {}
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode) == {'lambda_per_second','coefficients'} and
                 type(mode['lambda_per_second']) is list and len(mode['lambda_per_second']) == 2 and
                 type(mode['coefficients']) is list and 1 <= len(mode['coefficients']) <= 65,
                 'complete complex mode and all polynomial coefficients required')
        lr,li = map(full.exact, mode['lambda_per_second'])
        _require(lr*width <= Q(1,2), 'mode growth must satisfy Re(lambda)*Delta <= 1/2')
        for n, rows in enumerate(mode['coefficients']):
            matrix = _coefficient(rows,bits,source)
            _add(groups.setdefault((lr,li),{}).setdefault(n,{}),matrix,(Q(1,2),Q(0)))
            adjoint = {(m,j,i):(a,-b) for (m,i,j),(a,b) in matrix.items()}
            _add(groups.setdefault((lr,-li),{}).setdefault(n,{}),adjoint,(Q(1,2),Q(0)))
    return width, groups


class _Columns:
    def __init__(self, source, bits):
        self.source, self.bits, self.cache = source, bits, {}
        self.actions = {}

    def column(self, component, key, active):
        name = component, key, active
        if name not in self.cache:
            mark,i,j = key
            exact = trajectory.RetardedGaussianTrajectorySource._component(self.source, component,
                {mark:{(i,j):dipole.ComplexRadical(1)}}, active)
            centre, price = _pairs(exact,self.bits)
            self.cache[name] = centre, price, exact
        return self.cache[name]

    def action(self, component, state, active):
        if len(state)>128:
            return _Columns.whole_action(self,component,state,active)
        result = {}; error = Q(0); exact_zero = True
        for key,pair in state.items():
            image, price, exact = self.column(component,key,active)
            _add(result,image,pair); error += (abs(pair[0])+abs(pair[1]))*price
            exact_zero = exact_zero and not exact
        return result,error,exact_zero

    def whole_action(self, component, state, active):
        # The same linear source is evaluated before rounding.  This keeps
        # every spectator coordinate without constructing one cache per Eij.
        key=component,id(state),active
        saved=self.actions.get(key)
        if saved is not None and saved[0] is state:
            return saved[1]
        exact=trajectory.RetardedGaussianTrajectorySource._component(self.source,component,
            trajectory.RetardedGaussianTrajectorySource._blocks(self.source,_exact(state)),active)
        centre,error=_pairs(exact,self.bits)
        result=centre,error,not exact
        self.actions[key]=state,result
        return result

    def phase_error(self, component, state, active):
        if component != 'quiet' and component[0] == 'drive' and active[component[1]]:
            return self.source._parts[component[1]][3]*_norm({k:v for k,v in state.items() if k[0].receipt is None})
        return Q(0)


def _descriptors(source, columns, start, stop, states, envelope_order):
    raw = source._value['retarded_source']['complete_driven_field_source']
    _,active = trajectory.RetardedGaussianTrajectorySource._clock(source,start)
    trajectory.RetardedGaussianTrajectorySource._clock(source,stop)
    active = tuple(active); width = stop-start
    births = tuple(Q(a)+Q(b) for a,b in zip(raw['emission_origins_seconds'],raw['flight_seconds']))
    _require(not any(start < birth < stop for birth in births), 'partition the original arm activation boundary')
    legs = raw['Gaussian_source_legs']; omega = tuple(Q(r['carrier_angular_frequency_per_second']) for r in legs)
    answer = []
    for component in trajectory.COMPONENTS:
        if component == 'quiet':
            answer.append((component,Q(0),[(Q(1),Q(0))],Q(0),False)); continue
        zero = all(columns.action(component,state,active)[2] for state in states)
        if zero:
            answer.append((component,Q(0),[(Q(0),Q(0))],Q(1),True)); continue
        if component[0] == 'drive':
            side = component[1]; local = max(Q(0),start-births[side])
            coeffs,tail = gaussian._envelope_polynomial(legs[side],local,width,envelope_order,columns.bits)
            answer.append((component,Q(0),[(v,Q(0)) for v in coeffs],tail,False))
        else:
            side,other = component[1:]; frequency = omega[other]-omega[side]
            angle = -omega[side]*(start-births[side])+omega[other]*(start-births[other])
            phase,price = gaussian._exponential(Q(0),angle,columns.bits)
            answer.append((component,frequency,[phase],price,False))
    return active, answer


def _evaluate(groups, width, u, bits):
    result = {}; price = Q(0)
    for (lr,li),polynomial in groups.items():
        scalar,error = gaussian._exponential(lr*width*u,li*width*u,bits)
        for n,matrix in polynomial.items():
            _add(result,matrix,(scalar[0]*u**n,scalar[1]*u**n))
            price += error*u**n*_norm(matrix)
    return _hermitian(result),price


def _piece(source, columns, piece, current, start, mode_bits, exp_bits, envelope_order):
    width,groups = _modes(piece,mode_bits,source)
    states = [matrix for polynomial in groups.values() for matrix in polynomial.values()]
    active,descriptors = _descriptors(source,columns,start,start+width,states,envelope_order)
    residual = {}; rounding = tails = phases = Q(0)
    for exponent,polynomial in groups.items():
        lr,li = exponent
        for n,matrix in polynomial.items():
            _add(residual.setdefault(exponent,{}).setdefault(n,{}),matrix,(width*lr,width*li))
            if n:
                _add(residual.setdefault(exponent,{}).setdefault(n-1,{}),matrix,(Q(n),Q(0)))
            for component,w,coeffs,tail,zero in descriptors:
                image,error,_ = columns.action(component,matrix,active)
                target = lr,li+w
                for j,(a,b) in enumerate(coeffs):
                    _add(residual.setdefault(target,{}).setdefault(n+j,{}),image,(-width*a,-width*b))
                    rounding += 2*width*(abs(a)+abs(b))*error/Q(n+j+1)
                tails += 2*width*tail*(_norm(image)+error)/Q(n+1)
                phases += 2*width*columns.phase_error(component,matrix,active)/Q(n+1)
    defect = 2*sum((_norm(matrix)/Q(n+1) for polynomial in residual.values() for n,matrix in polynomial.items()),Q(0))
    begin,e0 = _evaluate(groups,width,Q(0),exp_bits)
    end,e1 = _evaluate(groups,width,Q(1),exp_bits)
    join = _difference(begin,current)+e0
    uniform = join+defect+rounding+tails+phases
    record = {'source_detector_interval_seconds':list(map(str,(start,start+width))),
        'source_exact_frequency_words_after_merge':len(residual),
        'complete_marked_coordinate_inventory':len(set().union(*(set(m) for m in states))) if states else 0,
        'Hermitian_projection_of_entire_complex_curve':True,
        'integrated_original_source_residual':str(field._price_upper(defect,columns.bits)),
        'source_radical_column_rounding_price':str(field._price_upper(rounding,columns.bits)),
        'source_Gaussian_and_relative_phase_tail_price':str(field._price_upper(tails,columns.bits)),
        'source_drive_phase_price':str(field._price_upper(phases,columns.bits)),
        'complete_join_price':str(field._price_upper(join,columns.bits)),
        'piece_uniform_rotating_error_from_input':str(field._price_upper(uniform,columns.bits)),
        'endpoint_exponential_scalar_price':str(field._price_upper(e1,columns.bits)),
        'zero_component_from_original_columns':[list(c) if isinstance(c,tuple) else c for c,_,_,_,zero in descriptors if zero],
        'Hamiltonian_norm_exponential_used':False}
    return width,end,uniform,e1,record


def _gamma_price(source, initial_norm, start, stop, bits):
    raw = source._value['retarded_source']; pulses = source._law._field._pulses
    local0,_ = trajectory.RetardedGaussianTrajectorySource._clock(source,start)
    local1,_ = trajectory.RetardedGaussianTrajectorySource._clock(source,stop)
    clock = raw['complete_driven_field_source']['reference_clock']; g = Q(clock['Gamma_numerical_centre'])
    lo,hi = map(Q,clock['angular_Gamma_enclosure_per_second']);delta = max(g-lo,hi-g)
    nojump = 2*sum((gaussian.GaussianAtomicPulseSource.Gamma_math_price(p,a,b,bits=bits)
                    for p,a,b in zip(pulses,local0,local1)),Q(0))
    natural = delta/g*(stop-start)*sum((gaussian._norm(gaussian._matrix(p.record()['complete_natural_R_per_second']),bits) for p in pulses),Q(0))
    background = 2*delta/g*(stop-start)*sum(map(Q,raw['BG_source']['BG_rates_per_second']),Q(0))
    return initial_norm*(nojump+natural+background), {'source_no_jump_density_difference_per_input_norm':str(field._price_upper(nojump,bits)),
        'complete_natural_recycling_difference_per_input_norm':str(field._price_upper(natural,bits)),
        'four_BG_marked_generator_difference_per_input_norm':str(field._price_upper(background,bits))}


def _initial(source, raw, start, bits):
    initial = _read_state(raw,source)
    rotating,frame = trajectory.RetardedGaussianTrajectorySource.frame(source,start,initial,inverse=True)
    centre,rounding = _pairs(rotating,bits)
    centre = _hermitian(centre)
    norm = sum((bsm._entry_norm(m,bits=bits) for m in trajectory.RetardedGaussianTrajectorySource._blocks(source,initial).values()),Q(0))
    return initial,centre,frame+rounding,norm


class RetardedReceiptTrajectoryCertificate:
    def __init__(self, source, *, source_inlet=None):
        _CHECK(); field._closed(source)
        _require(type(source) is trajectory.RetardedGaussianTrajectorySource,
                 'closed source-generated stopped trajectory required; arbitrary G or effects are not input')
        raw = trajectory.RetardedGaussianTrajectorySource.record(source)
        self._source,self._inlet = source,source_inlet
        input_record = None
        if source_inlet is not None:
            field._closed(source_inlet)
            _require(type(source_inlet) is inlet.PreparedRetardedGaussianInlet and source_inlet._law is source._law,
                     'the very same source-issued retarded inlet is required; target rho is not input')
            input_record = inlet.PreparedRetardedGaussianInlet.record(source_inlet)
        self._value = {'schema':SCHEMA,'stopped_trajectory_source':raw,'source_issued_inlet':input_record,
            'numerical_initial_is_actual_hardware_member':False,'full_Mark_counts_and_1089_matrices_retained':True,
            'all_emission_numbers_resummed':True,'retarded_coimage_is_actual_detector_time_atom':False,
            'full_field_and_queue_mother_retained':True,'source_bindings':_bindings(),'controller_advance':False}
        self._seal = _digest(self._value); _ISSUED[id(self)] = self._seal,source,source_inlet

    @classmethod
    def from_inlet(cls, source_inlet, *, bits=192):
        _CHECK();field._closed(source_inlet)
        _require(cls is RetardedReceiptTrajectoryCertificate and type(source_inlet) is inlet.PreparedRetardedGaussianInlet,
                 'closed PreparedRetardedGaussianInlet required')
        inlet.PreparedRetardedGaussianInlet.record(source_inlet)
        return cls(trajectory.RetardedGaussianTrajectorySource(source_inlet._law,bits=bits),source_inlet=source_inlet)

    def record(self):
        _CHECK();field._closed(self); owned = _ISSUED.get(id(self))
        _require(type(self) is RetardedReceiptTrajectoryCertificate and
            set(vars(self)) == {'_source','_inlet','_value','_seal'} and owned == (self._seal,self._source,self._inlet) and
            self._value['source_bindings'] == _bindings() and _digest(self._value) == self._seal and
            trajectory.RetardedGaussianTrajectorySource.record(self._source) == self._value['stopped_trajectory_source'] and
            (self._inlet is None or inlet.PreparedRetardedGaussianInlet.record(self._inlet) == self._value['source_issued_inlet']),
            'original trajectory, actual input issuance or continuous certificate source changed')
        return _copy(self._value)

    def _input(self, initial, upstream_error):
        if self._inlet is None:
            _require(initial is not None, 'generic numerical control must supply its complete Hermitian matrix')
            return _read_state(initial,self._source),full.nonnegative(upstream_error),False
        _require(initial is None and full.nonnegative(upstream_error) == 0,
                 'issued input and its old error come only from complete_pending_initial')
        raw = inlet.PreparedRetardedGaussianInlet.complete_pending_initial(self._inlet)
        return raw['complete_pending_state'],Q(raw['whole_upstream_trace_norm_error']),True

    def generate_trial(self, initial=None, stop=None, *, start=None, slices=1, order=32, mode_bits=160, envelope_order=10):
        raw = RetardedReceiptTrajectoryCertificate.record(self)
        original,_,issued = RetardedReceiptTrajectoryCertificate._input(self,initial,0)
        g0,g1 = map(Q,raw['stopped_trajectory_source']['retarded_source']['gate_seconds'])
        start = g0 if start is None else full.nonnegative(start); stop = g1 if stop is None else full.nonnegative(stop)
        _require(g0 <= start <= stop <= g1 and (not issued or start == g0), 'curve starts at its original source input cut')
        gaussian._precision(mode_bits)
        _require(type(slices) is int and slices>0 and type(order) is int and 0<=order<=64, 'finite untrusted writer budget required')
        _,current,_,_ = _initial(self._source,original,start,mode_bits)
        columns = _Columns(self._source,mode_bits);pieces=[]
        field_record = raw['stopped_trajectory_source']['retarded_source']['complete_driven_field_source']
        births = tuple(Q(a)+Q(b) for a,b in zip(field_record['emission_origins_seconds'],field_record['flight_seconds']))
        edges = sorted({start+n*(stop-start)/slices for n in range(slices+1)}|
                       {b for b in births if start<b<stop})
        for origin,end in zip(edges,edges[1:]):
            width=end-origin
            active,descriptors=_descriptors(self._source,columns,origin,end,[current],envelope_order)
            modes=[current]
            for degree in range(order):
                derivative={}
                for component,w,poly,_,_ in descriptors:
                    for j in range(degree+1):
                        scalar=dipole.ComplexRadical()
                        for k,(a,b) in enumerate(poly[:j+1]):
                            scalar += dipole.ComplexRadical(a,b)*_power(dipole.ComplexRadical(0,w*width),j-k)*(Q(1,factorial(j-k)))
                        pair=scalar.real.as_rational(),scalar.imag.as_rational()
                        image,_,_=columns.action(component,modes[degree-j],active)
                        _add(derivative,image,pair)
                proposal={k:(a*width/(degree+1),b*width/(degree+1)) for k,(a,b) in derivative.items()}
                proposal,_=fourier.exact._dyadic_state(_hermitian(proposal),mode_bits);modes.append(proposal)
            piece={'duration_seconds':str(width),'modes':[{'lambda_per_second':['0','0'],
                'coefficients':[_rows(m,mode_bits) for m in modes]}]}
            pieces.append(piece);current={}
            for matrix in modes:_add(current,matrix)
        return {'schema':SCHEMA+'/untrusted-curve','source_record':raw,'complete_initial_marked_state':_record_state(original),
            'source_issued_input_used':issued,'source_detector_interval_seconds':list(map(str,(start,stop))),
            'mode_bits':mode_bits,'pieces':pieces,'writer_correctness_assumed':False}

    def certify(self, trial, *, upstream_error=0, coefficient_bits=192, exponential_bits=192, envelope_order=10):
        raw = RetardedReceiptTrajectoryCertificate.record(self)
        _require(type(trial) is dict and set(trial) == {'schema','source_record','complete_initial_marked_state','source_issued_input_used',
            'source_detector_interval_seconds','mode_bits','pieces','writer_correctness_assumed'} and
            trial['schema'] == SCHEMA+'/untrusted-curve' and trial['source_record'] == raw and trial['writer_correctness_assumed'] is False,
            'untrusted continuous curve must bind its original stopped source')
        source=self._source;mode_bits=trial['mode_bits'];gaussian._precision(mode_bits)
        gaussian._precision(coefficient_bits);gaussian._precision(exponential_bits)
        if self._inlet is None:
            initial,inherited,issued=RetardedReceiptTrajectoryCertificate._input(self,trial['complete_initial_marked_state'],upstream_error)
        else:
            initial,inherited,issued=RetardedReceiptTrajectoryCertificate._input(self,None,upstream_error)
            _require(_record_state(initial) == trial['complete_initial_marked_state'], 'the curve replaced its issued complete source input')
        _require(trial['source_issued_input_used'] is issued and type(trial['pieces']) is list,
                 'input issuance cannot be supplied as a curve flag')
        start,stop=map(full.nonnegative,trial['source_detector_interval_seconds'])
        source._clock(start);source._clock(stop);_require(start<=stop, 'ordered source interval required')
        _require(not issued or start==Q(raw['stopped_trajectory_source']['retarded_source']['gate_seconds'][0]),
                 'issued source curve must start at its real gate input')
        original,current,entry,initial_norm=_initial(source,initial,start,coefficient_bits)
        if issued:
            initial_norm = min(initial_norm,Q(raw['source_issued_inlet']['source_centre_trace_norm_upper']))
        columns=_Columns(source,coefficient_bits);time=start;accumulated=entry;records=[]
        for piece in trial['pieces']:
            before=accumulated
            width,current,uniform,endpoint,detail=_piece(source,columns,piece,current,time,mode_bits,exponential_bits,envelope_order)
            time+=width;accumulated+=uniform+endpoint
            detail['previous_rotating_endpoint_error']=str(field._price_upper(before,coefficient_bits))
            records.append(detail)
        _require(time == stop, 'the complete curve must cover its declared source interval')
        physical,frame=trajectory.RetardedGaussianTrajectorySource.frame(source,stop,_exact(current))
        model,model_record=_gamma_price(source,initial_norm,start,stop,coefficient_bits)
        total=inherited+accumulated+frame+model
        return {'schema':SCHEMA+'/checked-curve','source_record':raw,'untrusted_trial':_copy(trial),
            'complete_physical_marked_endpoint':_record_state(physical),'whole_upstream_trace_norm_error_once':str(inherited),
            'source_initial_trace_norm_upper':str(field._price_upper(initial_norm,coefficient_bits)),
            'source_rotating_curve_error':str(field._price_upper(accumulated,coefficient_bits)),
            'physical_frame_readout_error':str(field._price_upper(frame,coefficient_bits)),
            'mathematical_Gamma_full_marked_price':str(field._price_upper(model,coefficient_bits)),
            'Gamma_price_components':model_record,'global_trace_norm_error':str(field._price_upper(total,coefficient_bits)),
            'source_detector_interval_seconds':list(map(str,(start,stop))),'piece_records':records,
            'source_issued_input_used':issued,'actual_hardware_member_asserted':False,
            'endpoint_price_substituted_for_uniform_error':False,'Hermitian_CPTP_contraction_used':True,
            'coefficient_bits':coefficient_bits,'exponential_bits':exponential_bits,'envelope_order':envelope_order}

    def verify(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-curve', 'complete continuous source certificate required')
        expected=RetardedReceiptTrajectoryCertificate.certify(self,report['untrusted_trial'],
            upstream_error=report['whole_upstream_trace_norm_error_once'] if self._inlet is None else 0,
            coefficient_bits=report['coefficient_bits'],exponential_bits=report['exponential_bits'],envelope_order=report['envelope_order'])
        _require(expected == report, 'actual source residual, full endpoint, uniform price or inherited error changed')
        return expected

    def _readout(self, checked, time):
        start,stop=map(Q,checked['source_detector_interval_seconds']);time=full.nonnegative(time)
        _require(start<=time<=stop, 'readout belongs to this verified continuous source interval')
        bits=checked['coefficient_bits'];exp_bits=checked['exponential_bits']
        if not checked['untrusted_trial']['pieces']:
            state=_read_state(checked['complete_physical_marked_endpoint'],self._source)
            local=Q(checked['source_rotating_curve_error'])+Q(checked['physical_frame_readout_error'])
        else:
            edge=start;state=None
            for piece,price in zip(checked['untrusted_trial']['pieces'],checked['piece_records']):
                width,groups=_modes(piece,checked['untrusted_trial']['mode_bits'],self._source)
                if edge<=time<=edge+width:
                    curve,eval_error=_evaluate(groups,width,(time-edge)/width,exp_bits)
                    state,frame=trajectory.RetardedGaussianTrajectorySource.frame(self._source,time,_exact(curve))
                    local=Q(price['previous_rotating_endpoint_error'])+Q(price['piece_uniform_rotating_error_from_input'])+eval_error+frame
                    break
                edge+=width
            _require(state is not None, 'verified pieces must cover the requested source readout')
        model,parts=_gamma_price(self._source,Q(checked['source_initial_trace_norm_upper']),start,time,bits)
        inherited=Q(checked['whole_upstream_trace_norm_error_once'])
        return {'physical_detector_clock_seconds':str(time),'complete_retarded_marked_state':_record_state(state),
            'new_curve_frame_and_Gamma_error':str(field._price_upper(local+model,bits)),
            'whole_upstream_error_once':str(inherited),
            'whole_marked_trace_norm_error':str(field._price_upper(inherited+local+model,bits)),
            'Gamma_price_components':parts,'fresh_interior_exponential_and_frame_price_consumed':True,
            'endpoint_error_substituted_for_uniform_curve_error':False}

    def readout(self, report, time):
        checked=RetardedReceiptTrajectoryCertificate.verify(self,report)
        return RetardedReceiptTrajectoryCertificate._readout(self,checked,time)

    def first_receipt_interval(self, report, lower, upper):
        checked = RetardedReceiptTrajectoryCertificate.verify(self,report)
        original = _read_state(checked['untrusted_trial']['complete_initial_marked_state'],self._source)
        marks = tuple(sorted({m for m,_,_ in original},key=trajectory._key))
        _require(marks and all(m.receipt is None for m in marks),
                 'future first-receipt readout requires the complete pending source input')
        start,stop = map(Q,checked['source_detector_interval_seconds'])
        lower,upper=map(full.nonnegative,(lower,upper))
        _require(start<=lower<=upper<=stop, 'receipt restriction belongs to its original continuous source interval')
        envelope = activity.RetardedReceiptActivityEnvelope(self._source._law,bits=checked['coefficient_bits'])
        if self._inlet is not None:
            inherited = activity.RetardedReceiptActivityEnvelope.input_error_payment(envelope,
                checked['whole_upstream_trace_norm_error_once'],start_marks=marks,input_time=start,interval=(lower,upper))
        else:
            error=Q(checked['whole_upstream_trace_norm_error_once'])
            inherited={'schema':SCHEMA+'/generic-error-without-issued-Mark-support',
                'whole_upstream_trace_norm_error':str(error),'first_receipt_input_error_payment':str(error if lower<upper else 0),
                'input_effect_contraction_upper':'1' if lower<upper else '0',
                'generic_error_support_inferred_from_centre_marks':False,'whole_upstream_error_consumed_once':True}
        last=RetardedReceiptTrajectoryCertificate._readout(self,checked,upper)
        first=RetardedReceiptTrajectoryCertificate._readout(self,checked,lower) if lower>start else None
        local=Q(last['new_curve_frame_and_Gamma_error'])+(Q(first['new_curve_frame_and_Gamma_error']) if first else 0)
        whole = Q(inherited['first_receipt_input_error_payment'])+local
        endpoint=_read_state(last['complete_retarded_marked_state'],self._source)
        beginning=_read_state(first['complete_retarded_marked_state'],self._source) if first else {}
        patterns=[{} for _ in range(4)]; pending={}
        for (mark,i,j),z in endpoint.items():
            if mark.receipt is None:
                field._add(pending,{(mark,i,j):z})
            else:
                field._add(patterns[mark.receipt],{(i,j):z})
        for (mark,i,j),z in beginning.items():
            if mark.receipt is not None:
                field._add(patterns[mark.receipt],{(i,j):z},-1)
        if lower==upper:
            patterns=[{} for _ in range(4)];whole=Q(0)
        return {'schema':SCHEMA+'/whole-first-receipt-readout','continuous_curve_certificate':checked,
            'physical_first_receipt_interval_seconds':list(map(str,(lower,upper))),
            'four_pattern_poststates':[{'pattern_index':h,'pattern_name':bsm.PATTERNS[h][0],
                'complete_retarded_poststate':channel._input_record(matrix)} for h,matrix in enumerate(patterns)],
            'complete_pending_complement':_record_state(pending),
            'whole_four_pattern_trace_norm_error':str(field._price_upper(whole,checked['coefficient_bits'])),
            'whole_input_error_payment_once':inherited,'all_pattern_error_is_one_direct_sum_bound':True,
            'pending_complement_error_not_multiplied_by_receipt_cap':True,
            'complete_time_field_and_queue_mother':checked['source_record'],
            'first_arrivals_before_restriction_lower_retained':True,
            'retarded_coimage_is_actual_detector_time_atom':False,'actual_hardware_member_asserted':False}

    def first_receipt_outcomes(self, report):
        start,stop=map(Q,report['source_detector_interval_seconds'])
        return RetardedReceiptTrajectoryCertificate.first_receipt_interval(self,report,start,stop)


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None)),repr(getattr(value,'__defaults__',None)),repr(getattr(value,'__kwdefaults__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_key,_record_state,_read_state,_pairs,_exact,_add,_norm,_hermitian,_difference,_power,_rows,
        _coefficient,_modes,_descriptors,_evaluate,_piece,_gamma_price,_initial,_function,_signature,_check,
        trajectory.RetardedGaussianTrajectorySource.record,trajectory.RetardedGaussianTrajectorySource._clock,
        trajectory.RetardedGaussianTrajectorySource._blocks,trajectory.RetardedGaussianTrajectorySource._component,
        trajectory.RetardedGaussianTrajectorySource.frame,inlet.PreparedRetardedGaussianInlet.record,
        inlet.PreparedRetardedGaussianInlet.complete_pending_initial,gaussian._envelope_polynomial,gaussian._exponential,
        gaussian.GaussianAtomicPulseSource.Gamma_math_price,gaussian._norm,gaussian._matrix,
        activity.RetardedReceiptActivityEnvelope.__init__,activity.RetardedReceiptActivityEnvelope.input_error_payment,
        fourier._add_rational,fourier.exact._dyadic_state,full._midpoint_matrix,bsm._entry_norm,
        channel._canonical,channel._complex_record,field._closed,field._price_upper)
    methods=tuple(_function(v) for cls in (RetardedReceiptTrajectoryCertificate,_Columns) for v in vars(cls).values()
                  if callable(v) or isinstance(v,classmethod))
    return tuple(map(_function,helpers)),methods,SCHEMA,tuple(bsm.PATTERNS)


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature()==_EXPECTED and trajectory._CHECK is _SOURCE_CHECK and
        inlet._CHECK is _INLET_CHECK and activity._CHECK is _ACTIVITY_CHECK, 'continuous source residual execution changed')
    _SOURCE_CHECK();_INLET_CHECK();_ACTIVITY_CHECK()


_CHECK,_SIGNATURE=_check,_signature
_EXPECTED=_signature()
