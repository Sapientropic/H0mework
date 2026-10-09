"""The original first-receipt query descends to three zero-count coimages.

For the admitted source, each polarization's detected Gram has zero
cross-arm blocks. Zero counts therefore factor through two original local
TNI flows. Inclusion-exclusion reads the complete any-first-herald event.
"""
from fractions import Fraction as Q
import hashlib
import json

import retarded_gaussian_bsm_source as law
import gaussian_operator_flow_rha0037_1 as operator
import late_registered_source_rha0038 as previous

gaussian,dipole,channel,joint,bsm=law.gaussian,law.dipole,law.channel,law.joint,law.bsm
SCHEMA='stage10-source-first-receipt-zero-count-coimage/rha0039'
PORT_SETS={'perp':(0,2),'parallel':(1,3),'all':(0,1,2,3)}
_ISSUED={}


def require(value,reason):
    if not value:raise ValueError(reason)


def digest(value):return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _marks(source):
    todo=[bsm.INITIAL];seen=set(todo)
    for mark in todo:
        for port in range(4):
            target=bsm.BSMSource.target(source._gate,mark,port)
            if target not in seen:seen.add(target);todo.append(target)
    return todo


def mark_restrictions(source):
    patterns={tuple(sorted(ports)) for _,ports in bsm.PATTERNS}
    require(patterns=={tuple(sorted((p,q))) for p in PORT_SETS['perp'] for q in PORT_SETS['parallel']},
            'the original four supported patterns must be exactly the polarization cross pairs')
    records=[]
    for name,ports in PORT_SETS.items():
        count=0
        for mark in _marks(source):
            inside=mark.receipt is None and not any(mark.counts[p] for p in ports)
            for port in range(4):
                target=bsm.BSMSource.target(source._gate,mark,port)
                after=target.receipt is None and not any(target.counts[p] for p in ports)
                require(after==(inside and port not in ports),
                        'zero-count marginal is not closed under the original first-receipt Mark law')
                count+=1
        records.append({'query':name,'original_Mark_port_transitions_checked':count,
            'original_forbidden_port_set':list(ports),'no_forbidden_count_faces_have_no_receipt':True})
    return records


def compiled_queries(source):
    require(type(source) is law.RetardedGaussianBSMSource,'closed original retarded source required; transfer table is not input')
    raw=source.record();previous.static_blocks(raw);mark=mark_restrictions(source)
    transfer=source._transfer;rows=[]
    for name,ports in PORT_SETS.items():
        gram=[[sum((transfer[p][mu]*transfer[p][nu].conjugate() for p in ports),dipole.ComplexRadical())
            for nu in range(6)] for mu in range(6)]
        require(all(not gram[mu][nu] for mu in range(6) for nu in range(6) if (mu<3)!=(nu<3)),
                'this exact source query has cross-arm loss; retain the coupled zero-count generator')
        _,expected,complement=joint.passive_transfer(tuple(transfer[p] for p in ports))
        require(all(gram[mu][nu]==expected[nu][mu] for mu in range(6) for nu in range(6)),
                'original passive Gram and detected action coefficient differ')
        # The selected rows are a restriction of the same passive transfer;
        # the original full transfer and each selected complement are PSD.
        local=[[] for _ in range(2)];recycle_norms=[Q(0),Q(0)]
        for group,rate,modes in source._groups:
            for mu,(side,first) in modes:
                for nu,(other,second) in modes:
                    if side!=other:continue
                    coefficient=rate*(dipole.ComplexRadical(int(mu==nu))-gram[mu][nu])
                    if not coefficient:continue
                    local[side].append({'group':list(group),'mu':mu,'nu':nu,'coefficient_per_second':coefficient.serialize(),
                        'forward_left':channel._input_record(first),'forward_right_adjoint':channel._input_record(dipole.matrix_adjoint(second))})
                    recycle_norms[side]+=gaussian._norm({(0,0):coefficient},192)*gaussian._norm(first,192)*gaussian._norm(second,192)
        rows.append({'query':name,'ports':list(ports),'selected_transfer_Gram':law.optical._matrix(expected),
            'selected_transfer_complement':law.optical._matrix(complement),'cross_arm_Gram_zero_checked':True,
            'complete_unobserved_local_recycling':local,'local_recycle_norm_bounds_per_second':list(map(str,recycle_norms)),
            'background_no_count_rate_per_second':str(sum((Q(raw['BG_source']['BG_rates_per_second'][p]) for p in ports),Q(0)))})
    return raw,mark,rows


class ZeroCountReceiptSource:
    def __init__(self,original):
        raw,marks,queries=compiled_queries(original)
        self._original=original;self._value={'schema':SCHEMA,'original_retarded_source':raw,
            'source_identity':{'source':'positiveSmoothUnifiedSource','root_visit':10,'material_row':0,'current_tick':16,'next_tick':17},
            'complete_Mark_restrictions':marks,'complete_queries':queries,
            'zero_count_readout':'no_perp + no_parallel - no_all is the original pending-no-receipt mass',
            'any_first_receipt_readout':'original input trace - no_perp - no_parallel + no_all',
            'source_factorization_scope':'this exact original source; all three polarization Gram cross-arm blocks checked',
            'specific_Psi_label_probability_claimed':False,'source_time_queue_mother_reset':False,
            'all_physical_natural_recycling_retained':True,'actual_hardware_uniquely_identified':False,'controller_advance':False}
        self._seal=digest(self._value);_ISSUED[id(self)]=(original,self._seal)

    def record(self):
        require(type(self) is ZeroCountReceiptSource and set(vars(self))=={'_original','_value','_seal'} and
            _ISSUED.get(id(self))==(self._original,self._seal) and digest(self._value)==self._seal and
            self._original.record()==self._value['original_retarded_source'],'original zero-count source changed')
        return json.loads(channel._canonical(self._value))

    def query(self,name='all'):
        raw=self.record();require(name in PORT_SETS,'registered zero-count query required')
        return next(row for row in raw['complete_queries'] if row['query']==name)


class LocalNoCountCoflow:
    def __init__(self,source,side,*,query='all',start=None,stop=None,bits=192):
        require(type(source) is ZeroCountReceiptSource and type(side) is int and side in (0,1),
                'closed original zero-count source and physical side required')
        raw=source.record();subset=source.query(query);law_raw=raw['original_retarded_source'];g0,g1=map(Q,law_raw['gate_seconds'])
        a,b=(g0 if start is None else Q(start)),(g1 if stop is None else Q(stop))
        require(g0<=a<b<=g1,'the same original detector query interval is required')
        local_a,local_b=source._original.local_times(a)[side],source._original.local_times(b)[side]
        require(local_a>=0 and local_b-local_a==b-a,'both original legs must be active throughout the chosen query')
        pulse=law_raw['complete_driven_field_source']['Gaussian_source_legs'][side];gaussian._precision(bits)
        parts,frequency=operator.compiled_parts(pulse,bits)
        self._source=source;self._value={'schema':SCHEMA+'/local-no-count-adjoint-coflow',
            'zero_count_source_sha256':digest(raw),'original_Gaussian_source':pulse,'side':side,'query':query,
            'source_detector_interval_seconds':list(map(str,(a,b))),'source_local_interval_seconds':list(map(str,(local_a,local_b))),
            'flow_interval_seconds':['0',str(b-a)],'coefficient_bits':bits,'D1_frame_frequency_per_second':str(frequency),
            'scalar_Gaussian_centre_in_flow_coordinate':str(local_b-Q(pulse['centre_seconds'])),
            'complete_unobserved_local_recycling':subset['complete_unobserved_local_recycling'][side],
            'local_recycle_norm_upper_per_second':subset['local_recycle_norm_bounds_per_second'][side],
            'source_clock':'local_b-u','adjoint_equation':'E prime = L_no_count(local_b-u)^*(E); E(0)=I',
            'physical_effect_readout':'D(local_a) E(b-a) D(local_a)^*',
            'all_natural_loss_and_unobserved_recycling_retained':True,'operator_contraction_from_CP_subunitality':True,
            'actual_hardware_uniquely_identified':False,'controller_advance':False}
        self._parts=parts;self._seal=digest(self._value);_ISSUED[id(self)]=(source,self._seal,digest(_parts_record(parts)))

    def record(self):
        require(type(self) is LocalNoCountCoflow and set(vars(self))=={'_source','_value','_parts','_seal'} and
            _ISSUED.get(id(self))==(self._source,self._seal,digest(_parts_record(self._parts))) and digest(self._value)==self._seal and
            digest(self._source.record())==self._value['zero_count_source_sha256'],'original local no-count coflow changed')
        return json.loads(channel._canonical(self._value))


def _parts_record(parts):
    k,ek,v,ev=parts
    return [[i,j,str(a),str(b)] for (i,j),(a,b) in sorted(k.items())],str(ek),[[i,j,str(a),str(b)] for (i,j),(a,b) in sorted(v.items())],str(ev)


class Columns:
    def __init__(self,coflow):
        require(type(coflow) is LocalNoCountCoflow,'closed original no-count coflow required')
        self.original=coflow;self.raw=coflow.record();self.bits=self.raw['coefficient_bits'];self.cache={}
        self.k,self.ek,self.v,self.ev=coflow._parts
        self.recycle=[]
        for row in self.raw['complete_unobserved_local_recycling']:
            self.recycle.append((channel._complex_record(row['coefficient_per_second']),
                gaussian._matrix(row['forward_left']),gaussian._matrix(row['forward_right_adjoint'])))

    def exact_column(self,component,key):
        require(component in ('quiet','drive') and type(key) is tuple and len(key)==2 and
                all(type(i) is int and 0<=i<33 for i in key),'original no-count component and complete33 address required')
        e={key:dipole.ComplexRadical(1)};pairs=self.k if component=='quiet' else self.v
        k={address:dipole.ComplexRadical(*value) for address,value in pairs.items()}
        result=dipole.matrix_product(dipole.matrix_adjoint(k),e)
        gaussian.field._add(result,dipole.matrix_product(e,k))
        if component=='quiet':
            for c,left,right_adj in self.recycle:
                gaussian.field._add(result,dipole.matrix_product(dipole.matrix_product(right_adj,e),left),c)
        return result

    def column(self,component,key):
        index=component,key
        if index not in self.cache:
            exact=self.exact_column(component,key);centres,errors=gaussian.full._midpoint_matrix(exact,self.bits)
            centres,rounding=operator.basis.density.fourier.exact._dyadic_state(centres,self.bits)
            # K columns were rounded once from their same original source.
            price=sum(errors.values(),Q(0))+rounding+2*(self.ek if component=='quiet' else self.ev)
            self.cache[index]=centres,price
        return self.cache[index]

    def action(self,component,matrix):
        result={};price=Q(0)
        for key,pair in matrix.items():
            column,error=self.column(component,key)
            operator.basis.density.fourier._add_rational(result,column,pair);price+=(abs(pair[0])+abs(pair[1]))*error
        return result,price
