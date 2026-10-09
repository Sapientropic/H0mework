import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalRealActionFeed

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherOrdinaryWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumOriginalDensity PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open PreparationVacuumOrderedRealSignal PreparationVacuumOriginalGreenFeedback
open PreparationVacuumSourceFieldFamily PreparationVacuumFullFieldRiesz PreparationVacuumGaugeSourceInjection
open Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
abbrev Operator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent physicalTime preparedDual preparedPrimal
  noetherReader noetherReaderContact noetherPreparedCurrent

def sourceHamiltonian (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Operator:=jointGenerator p F 0 0

private theorem spectralShift (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z 0=sourceHamiltonian p F-z • (1:Operator) :=by
  unfold sourceHamiltonian
  unfold jointGenerator
  have zero : (0:ℂ) • (1:Operator)=0:=by apply ContinuousLinearMap.ext;intro v;exact zero_smul ℂ v
  rw [zero,sub_zero]

private theorem inverse_commutes {A : Type*} [Ring A] [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (H K : A) (z : ℂ) (shift : K=H-z • 1) (unit : IsUnit K) :
    Ring.inverse K*H=H*Ring.inverse K :=by
  have commute : H*K=K*H:=by rw [shift,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  have left:=Ring.inverse_mul_cancel K unit
  have right:=Ring.mul_inverse_cancel K unit
  calc
    Ring.inverse K*H=Ring.inverse K*H*(K*Ring.inverse K) :=by rw [right,mul_one]
    _=Ring.inverse K*(H*K)*Ring.inverse K :=by simp only [mul_assoc]
    _=Ring.inverse K*(K*H)*Ring.inverse K :=by rw [commute]
    _=H*Ring.inverse K :=by rw [←mul_assoc (Ring.inverse K) K,left,one_mul]

theorem sourceResolvent_commutes (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) :
    jointResolvent p F z 0*sourceHamiltonian p F=sourceHamiltonian p F*jointResolvent p F z 0 :=by
  unfold jointResolvent
  exact inverse_commutes _ _ z (spectralShift p F z) (jointGenerator_unit p F z hz)

theorem sourceTime_commutes (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (age : ℝ) :
    physicalTime p F age 0*sourceHamiltonian p F=sourceHamiltonian p F*physicalTime p F age 0 :=by
  unfold physicalTime
  exact (SourceFiniteUnitary.time_commutes (sourceHamiltonian p F) (sourceHamiltonian p F) (Commute.refl _) age).symm.eq

theorem preparedPrimal_time (q : PhysicalResponsePoint) (age : ℝ) (hw : q.w.im≠0) :
    HasDerivAt (fun t=>preparedPrimal q 0 t)
      ((-Complex.I) • sourceHamiltonian q.p q.F (preparedPrimal q 0 age)) age :=by
  have time:=SourceFiniteUnitary.time_derivative (sourceHamiltonian q.p q.F) age (responseRight q)
  let R:=(jointResolvent q.p q.F q.w 0).restrictScalars ℝ
  have generated:=R.hasFDerivAt.comp_hasDerivAt age time
  have commute:=sourceResolvent_commutes q.p q.F q.w hw
  have order:=(SourceFiniteUnitary.time_commutes (sourceHamiltonian q.p q.F) (sourceHamiltonian q.p q.F) (Commute.refl _) age).symm.eq
  convert! generated using 1
  all_goals simp only [preparedPrimal,R,physicalTime,sourceHamiltonian,Function.comp_apply,map_smul,
    ContinuousLinearMap.coe_restrictScalars]
  all_goals first
    | (funext t;dsimp only [physicalTime,Pi.mul_apply,mul_apply_eq_comp,Function.comp_apply];rfl)
    | (have matrix : sourceHamiltonian q.p q.F*jointResolvent q.p q.F q.w 0*
          SourceFiniteUnitary.time (sourceHamiltonian q.p q.F) age=
        jointResolvent q.p q.F q.w 0*SourceFiniteUnitary.time (sourceHamiltonian q.p q.F) age*
          sourceHamiltonian q.p q.F:=by
        rw [←commute,mul_assoc,←order,mul_assoc]
       change (-Complex.I) • sourceHamiltonian q.p q.F (jointResolvent q.p q.F q.w 0
         (SourceFiniteUnitary.time (sourceHamiltonian q.p q.F) age (responseRight q)))=
         jointResolvent q.p q.F q.w 0 ((-Complex.I) •
           SourceFiniteUnitary.time (sourceHamiltonian q.p q.F) age (sourceHamiltonian q.p q.F (responseRight q)))
       rw [map_smul]
       simpa only [sourceHamiltonian,mul_apply_eq_comp] using
         congrArg (fun A : Operator=>(-Complex.I) • A (responseRight q)) matrix)

theorem preparedDual_time (q : PhysicalResponsePoint) (age : ℝ) (hz : q.z.im≠0) (v : H) :
    HasDerivAt (fun t=>preparedDual q 0 t v)
      (preparedDual q 0 age (Complex.I • sourceHamiltonian (q.p+q.k) q.F v)) age :=by
  have time:=independentDual_time q 0 age
  let ev : (H→L[ℂ] ℂ)→L[ℝ] ℂ:=(ContinuousLinearMap.apply ℂ ℂ (jointResolvent (q.p+q.k) q.F q.z 0 v)).restrictScalars ℝ
  have generated:=ev.hasFDerivAt.comp_hasDerivAt age time
  have commute:=sourceResolvent_commutes (q.p+q.k) q.F q.z hz
  convert! generated using 1
  all_goals simp only [preparedDual,independentDual,ev,Function.comp_apply,ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.coe_restrictScalars,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    mul_apply_eq_comp,smul_apply,map_smul,inner_smul_right,sourceHamiltonian]
  all_goals first
    | (funext t;dsimp only [Function.comp_apply,independentDual];rfl)
    | (change Complex.I • inner ℂ (responseLeft q)
          (physicalTime (q.p+q.k) q.F (-age) 0 (jointResolvent (q.p+q.k) q.F q.z 0
            (sourceHamiltonian (q.p+q.k) q.F v)))=
          inner ℂ (responseLeft q) (physicalTime (q.p+q.k) q.F (-age) 0
            (Complex.I • sourceHamiltonian (q.p+q.k) q.F (jointResolvent (q.p+q.k) q.F q.z 0 v)))
       simp only [map_smul,inner_smul_right,smul_eq_mul]
       simpa only [sourceHamiltonian,mul_apply_eq_comp] using
        congrArg (fun u : H=>Complex.I*inner ℂ (responseLeft q) (physicalTime (q.p+q.k) q.F (-age) 0 u))
          (congrArg (fun A : Operator=>A v) commute))

private theorem bracketSlide {A : Type*} [Ring A] (L R J S T H K : A)
    (RH : R*H=H*R) (SK : S*K=K*S) (TK : T*K=K*T) :
    L*H*R*J*S*T-L*R*J*S*T*K=L*R*(H*J-J*K)*S*T :=by
  have left : L*H*R*J*S*T=L*R*H*J*S*T:=by
    simpa only [mul_assoc] using congrArg (fun B=>L*B*J*S*T) RH.symm
  have right : L*R*J*S*T*K=L*R*J*K*S*T:=by
    calc
      _=L*R*J*S*(T*K):=by simp only [mul_assoc]
      _=L*R*J*S*(K*T):=by rw [TK]
      _=L*R*J*(S*K)*T:=by simp only [mul_assoc]
      _=L*R*J*(K*S)*T:=by rw [SK]
      _=_:=by simp only [mul_assoc]
  rw [left,right]
  simp only [mul_sub,sub_mul,mul_assoc]

private theorem bracketDerivative {A : Type*} [Ring A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] (L R J S T H K : A)
    (RH : R*H=H*R) (SK : S*K=K*S) (TK : T*K=K*T) :
    (Complex.I • (L*H))*R*J*S*T+L*R*J*S*((-Complex.I) • (T*K))=
      Complex.I • (L*R*(H*J-J*K)*S*T) :=by
  simp only [smul_mul_assoc,mul_smul_comm]
  rw [neg_smul,←sub_eq_add_neg,←smul_sub]
  simpa only [mul_assoc] using congrArg (fun A=>Complex.I • A) (bracketSlide L R J S T H K RH SK TK)

/-- This uses the actual complete generator on both source legs. -/
def noetherTimeInsertion (q : PhysicalResponsePoint) (reader : Field289) : Operator:=
  sourceHamiltonian (q.p+q.k) q.F*noetherReader reader q.p q.F 0-
    noetherReader reader q.p q.F 0*sourceHamiltonian q.p q.F

def noetherTimeCurrent (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) : ℂ:=
  Complex.I*preparedDual q 0 age (noetherTimeInsertion q reader (preparedPrimal q 0 age))

theorem noetherPreparedCurrent_time (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun t=>noetherPreparedCurrent q reader 0 t) (noetherTimeCurrent q reader age) age :=by
  have TL:= (timeJets_generated (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).1
  have TR:= (timeJets_generated (sourceHamiltonian q.p q.F) 1 0 age).1
  have left:=(TL.mul_const (jointResolvent (q.p+q.k) q.F q.z 0)).mul_const (noetherReader reader q.p q.F 0)
  have product:=(left.mul_const (jointResolvent q.p q.F q.w 0)).mul TR
  have actual:=paired_derivative product (responseLeft q) (responseRight q)
  have value : (fun t=>noetherPreparedCurrent q reader 0 t)=
      (fun t=>inner ℂ (responseLeft q)
        (((timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 t).value*
          jointResolvent (q.p+q.k) q.F q.z 0*noetherReader reader q.p q.F 0*
          jointResolvent q.p q.F q.w 0*(timeJet (sourceHamiltonian q.p q.F) 1 0 t).value)
        (responseRight q))) :=by
    funext t
    simp only [noetherPreparedCurrent,preparedDual,preparedPrimal,independentDual,timeJet,
      neg_one_mul,one_mul,add_zero,zero_add,Function.comp_apply,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,mul_apply_eq_comp,physicalTime,sourceHamiltonian]
  have leftValue : (timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).value=
      physicalTime (q.p+q.k) q.F (-age) 0 :=by
    simp only [timeJet,neg_one_mul,add_zero,physicalTime,sourceHamiltonian]
  have rightValue : (timeJet (sourceHamiltonian q.p q.F) 1 0 age).value=
      physicalTime q.p q.F age 0 :=by
    simp only [timeJet,one_mul,add_zero,physicalTime,sourceHamiltonian]
  have leftDerivative : (timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).first=
      Complex.I • (physicalTime (q.p+q.k) q.F (-age) 0*sourceHamiltonian (q.p+q.k) q.F) :=by
    simp only [timeJet,neg_one_mul,add_zero,neg_one_smul,mul_smul_comm,neg_smul,one_smul,neg_neg,physicalTime,sourceHamiltonian]
  have rightDerivative : (timeJet (sourceHamiltonian q.p q.F) 1 0 age).first=
      (-Complex.I) • (physicalTime q.p q.F age 0*sourceHamiltonian q.p q.F) :=by
    simp only [timeJet,one_mul,add_zero,one_smul,mul_smul_comm,physicalTime,sourceHamiltonian]
  have derivativeMatrix :
      (timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).first*
        jointResolvent (q.p+q.k) q.F q.z 0*noetherReader reader q.p q.F 0*
        jointResolvent q.p q.F q.w 0*(timeJet (sourceHamiltonian q.p q.F) 1 0 age).value+
      (timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).value*
        jointResolvent (q.p+q.k) q.F q.z 0*noetherReader reader q.p q.F 0*
        jointResolvent q.p q.F q.w 0*(timeJet (sourceHamiltonian q.p q.F) 1 0 age).first=
      Complex.I • (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        noetherTimeInsertion q reader*jointResolvent q.p q.F q.w 0*physicalTime q.p q.F age 0) :=by
    rw [leftDerivative,rightDerivative,leftValue,rightValue]
    simpa only [noetherTimeInsertion] using bracketDerivative
      (physicalTime (q.p+q.k) q.F (-age) 0) (jointResolvent (q.p+q.k) q.F q.z 0)
      (noetherReader reader q.p q.F 0) (jointResolvent q.p q.F q.w 0)
      (physicalTime q.p q.F age 0) (sourceHamiltonian (q.p+q.k) q.F) (sourceHamiltonian q.p q.F)
      (sourceResolvent_commutes (q.p+q.k) q.F q.z hz) (sourceResolvent_commutes q.p q.F q.w hw)
      (sourceTime_commutes q.p q.F age)
  have derivative:=congrArg (fun A : Operator=>inner ℂ (responseLeft q) (A (responseRight q))) derivativeMatrix
  have readback : inner ℂ (responseLeft q)
      (((timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).first*
        jointResolvent (q.p+q.k) q.F q.z 0*noetherReader reader q.p q.F 0*
        jointResolvent q.p q.F q.w 0*(timeJet (sourceHamiltonian q.p q.F) 1 0 age).value+
      (timeJet (sourceHamiltonian (q.p+q.k) q.F) (-1) 0 age).value*
        jointResolvent (q.p+q.k) q.F q.z 0*noetherReader reader q.p q.F 0*
        jointResolvent q.p q.F q.w 0*(timeJet (sourceHamiltonian q.p q.F) 1 0 age).first) (responseRight q))=
      noetherTimeCurrent q reader age :=by
    simpa only [noetherTimeCurrent,preparedDual,preparedPrimal,independentDual,
      smul_apply,mul_apply_eq_comp,Function.comp_apply,map_smul,inner_smul_right,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply] using derivative
  simp only [Pi.mul_apply] at actual
  rw [readback,←value] at actual
  exact actual

end LowEnergy.PreparationVacuumNoetherOrdinaryWard
