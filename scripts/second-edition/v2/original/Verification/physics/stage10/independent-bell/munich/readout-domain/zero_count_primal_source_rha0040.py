"""The same original zero-count action advances its own inlet factors."""
from fractions import Fraction as Q
import json

import zero_count_receipt_rha0039 as base
import completed_retarded_inlet_rha0028 as paid

SCHEMA='stage10-source-first-receipt-primal-zero-count-flow/rha0040'
_ISSUED={}
gaussian,dipole,channel=base.gaussian,base.dipole,base.channel
fourier=base.operator.basis.density.fourier


def frame(raw,matrix,time,*,inverse=False,bits=192):
    frequencies=[Q(raw['D1_frame_frequency_per_second']) if s.family=='D1' else
        Q(raw['original_Gaussian_source']['carrier_angular_frequency_per_second']) if s.family=='D2' else Q(0)
        for s in dipole.STATES]
    answer={};price=Q(0);phases={}
    for (i,j),z in matrix.items():
        angle=(frequencies[j]-frequencies[i])*Q(time)*(-1 if inverse else 1)
        if angle not in phases:phases[angle]=gaussian._exponential(0,angle,bits) if angle else ((Q(1),Q(0)),Q(0))
        phase,error=phases[angle];answer[i,j]=gaussian.field._product(phase,z);price+=error*(abs(z[0])+abs(z[1]))
    projected=fourier._hermitian(answer)
    return projected,price+fourier._difference(answer,projected)


class LocalNoCountPrimalFlow:
    def __init__(self,current,parent,side=0,factor_index=0,*,query='all',stop=None,bits=192):
        base.require(type(current) is paid.inlet.PreparedRetardedGaussianInlet and
            type(parent) is base.ZeroCountReceiptSource and parent._original is current._law and
            type(side) is int and side in (0,1) and type(factor_index) is int,
            'the same original inlet, zero-count source and source-issued factor required')
        initial=paid.inlet.PreparedRetardedGaussianInlet.record(current)
        coflow=base.LocalNoCountCoflow(parent,side,query=query,stop=stop,bits=bits)
        raw={key:value for key,value in coflow.record().items() if key not in
             ('adjoint_equation','physical_effect_readout','operator_contraction_from_CP_subunitality')}
        rows=initial['checked_local_density_inventories'][side]
        base.require(0<=factor_index<len(rows),'factor override lies outside the source-owned inventory')
        selected=rows[factor_index];physical=channel._read_input(selected['complete_retarded_local_endpoint'],33)
        pairs,errors=gaussian.full._midpoint_matrix(physical,bits)
        a,b=map(Q,raw['source_local_interval_seconds'])
        rotated,phase=frame(raw,pairs,a,inverse=True,bits=bits)
        rotated,quantization=fourier.exact._dyadic_state(rotated,96)
        self._current,self._parent,self._coflow=current,parent,coflow
        self._value={**raw,'schema':SCHEMA,'source_current_sha256':base.digest(initial),
            'factor_index':factor_index,'factor_id':selected['factor_id'],'source_clock':'local_a+u',
            'scalar_Gaussian_centre_in_flow_coordinate':str(Q(raw['original_Gaussian_source']['centre_seconds'])-a),
            'source_initial_physical_matrix':selected['complete_retarded_local_endpoint'],
            'source_initial_rotating_matrix':[[i,j,str(x),str(y)] for (i,j),(x,y) in sorted(rotated.items())],
            'source_initial_frame_and_quantization_price':str(sum(errors.values(),Q(0))+phase+quantization),
            'initial_entry_norm_upper':str(paid.inlet.bsm._entry_norm(physical,bits=bits)),
            'primal_equation':'rho prime = L_no_count(local_a+u)(rho)',
            'physical_density_readout':'D(local_a+u) rho(u) D(local_a+u)^*',
            'trace_norm_contraction_from_CP_TNI':True,'signed_factor_positivity_assumed':False,
            'old_whole_inlet_error_applied_per_factor':False,'caller_initial_matrix_used':False}
        self._seal=base.digest(self._value);_ISSUED[id(self)]=(current,parent,coflow,self._seal)

    def record(self):
        base.require(type(self) is LocalNoCountPrimalFlow and set(vars(self))=={'_current','_parent','_coflow','_value','_seal'} and
            _ISSUED.get(id(self))==(self._current,self._parent,self._coflow,self._seal) and base.digest(self._value)==self._seal and
            self._parent._original is self._current._law and base.digest(paid.inlet.PreparedRetardedGaussianInlet.record(self._current))==self._value['source_current_sha256'],
            'the original primal source, inlet or factor changed')
        self._coflow.record()
        return json.loads(channel._canonical(self._value))


class Columns:
    def __init__(self,flow):
        base.require(type(flow) is LocalNoCountPrimalFlow,'closed original primal zero-count flow required')
        self.flow=flow;self.raw=flow.record();self.bits=self.raw['coefficient_bits'];self.cache={}
        self.k,self.ek,self.v,self.ev=flow._coflow._parts
        self.recycle=[(channel._complex_record(r['coefficient_per_second']),
            gaussian._matrix(r['forward_left']),gaussian._matrix(r['forward_right_adjoint']))
            for r in self.raw['complete_unobserved_local_recycling']]

    def exact_column(self,component,key):
        base.require(component in ('quiet','drive') and type(key) is tuple and len(key)==2 and
            all(type(i) is int and 0<=i<33 for i in key),'complete source primal component and address required')
        matrix={key:dipole.ComplexRadical(1)}
        k={address:dipole.ComplexRadical(*z) for address,z in (self.k if component=='quiet' else self.v).items()}
        result=dipole.matrix_product(k,matrix)
        gaussian.field._add(result,dipole.matrix_product(matrix,dipole.matrix_adjoint(k)))
        if component=='quiet':
            for c,left,right in self.recycle:
                gaussian.field._add(result,dipole.matrix_product(dipole.matrix_product(left,matrix),right),c)
        return result

    def column(self,component,key):
        if (component,key) not in self.cache:
            result=self.exact_column(component,key)
            centre,errors=gaussian.full._midpoint_matrix(result,self.bits)
            centre,rounding=fourier.exact._dyadic_state(centre,self.bits)
            self.cache[component,key]=centre,sum(errors.values(),Q(0))+rounding+2*(self.ek if component=='quiet' else self.ev)
        return self.cache[component,key]

    def action(self,component,matrix):
        result={};price=Q(0)
        for key,z in matrix.items():
            column,error=self.column(component,key);fourier._add_rational(result,column,z);price+=(abs(z[0])+abs(z[1]))*error
        return result,price
