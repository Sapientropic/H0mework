import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceConstraintRead
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationAbelZeroRead

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalConstraint114
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalZeroRead
open PreparationVacuumJointFieldResponse PreparationVacuumPhysicalHalfAxis
open PreparationVacuumPhysicalPoleAmputation PreparationVacuumPhysicalFeedback
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback
open CanonicalGradedCurrent FullYSourceCutoffVolterra
open scoped BigOperators InnerProductSpace Matrix Interval
attribute [local irreducible] actualC actualA physicalTime sourcePoleRead sourceProjection
  rawReader jointResolvent jointGenerator

open PreparationVacuumPhysicalGradeZeroRead PreparationVacuumUncutYukawa
open GaussNativePotential
open GaussCoreLabel GaussYukawaCoefficient GaussQuantumMultiplier PreparationVacuumActionFieldLift
open PreparationVacuumCurrentNativeLaplaceBridge
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPropagationPencil PreparationVacuumCurrentSignalOperator
open PreparationVacuumPhysicalPoleHalfResponse PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationVacuumGaugeSourceInjection
open MeasureTheory Set


open PreparationVacuumPhysicalNumberOneRead PreparationVacuumSourceActionJets
open PreparationVacuumSourceFieldFamily
open PreparationVacuumFullFieldRiesz GaussCoreDifferential

open PreparationVacuumOriginalGreenFeedback

open PreparationVacuumPhysicalAbelZeroRead Filter
open scoped Topology

theorem sourceConstraintDirection_color :
    (1/2 : ℝ) • (PreparationVacuumLowerClassical.originalUnit 6-
      PreparationVacuumLowerClassical.originalUnit 7)=
      SourceQuantumResidualGaugeSlice.colorGenerator 2 := by
  apply PreparationCoordinates.rawCoordinates.injective
  rw [map_smul,map_sub]
  simp only [PreparationVacuumLowerClassical.originalUnit,LinearEquiv.apply_symm_apply]
  change _=PreparationCoordinates.rawRead (SourceQuantumResidualGaugeSlice.colorGenerator 2)
  unfold PreparationCoordinates.rawRead
  rw [SourceQuantumResidualGaugeSlice.colorGenerator_coordinates]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply,Fin.ext_iff]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem sourceConstraintDirection_stabilizer :
    (1/2 : ℝ) • (PreparationVacuumLowerClassical.originalUnit 6-
      PreparationVacuumLowerClassical.originalUnit 7)=
      (-1/2 : ℝ) • (PreparationVacuumSourceChartBudget.sourceStabilizer 2).val := by
  apply PreparationCoordinates.rawCoordinates.injective
  rw [map_smul,map_sub,map_smul,PreparationVacuumSourceChartBudget.sourceStabilizer_raw]
  simp only [PreparationVacuumLowerClassical.originalUnit,LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> norm_num [Pi.single_apply,Fin.ext_iff]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

/-- The row114 color/phase read is kept separate from an electromagnetic-unit claim. -/
def sourceConstraintCharge (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  constraintChargeRead (fun i=>sourcePoleActionEuler q pL pR left right 0 t i)

def sourceConstraintChargeFirst (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) : ℂ :=
  ((sourceActualCurrentJet q pL pR left right t 15).first-
    (sourceActualCurrentJet q pL pR left right t 16).first)/2

def sourceConstraintCovariant (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (t : ℝ) : ℂ :=
  constraintCovariantRead spatial (fun i=>sourcePoleActionEuler q pL pR left right 0 t i)

set_option backward.isDefEq.respectTransparency false in
theorem sourceConstraintCharge_derivative (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (t : ℝ) :
    HasDerivAt (sourceConstraintCharge q pL pR left right)
      (sourceConstraintChargeFirst q pL pR left right t) t := by
  have h:=((sourceActualCurrentJet_generated q pL pR left right t 15).1.sub
    (sourceActualCurrentJet_generated q pL pR left right t 16).1).div_const (2:ℂ)
  convert! h using 1
  funext s
  simp only [sourceActualCurrentJet_value,sourceConstraintCharge,constraintChargeRead,Pi.sub_apply]

private theorem actualCurrent_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (i : Fin 289) :
    Continuous (fun t=>sourcePoleActionEuler q pL pR left right 0 t i) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h:=(sourceActualCurrentJet_generated q pL pR left right t i).1
  simp only [sourceActualCurrentJet_value] at h
  exact h.continuousAt

private theorem charge_first_continuous (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) : Continuous (sourceConstraintChargeFirst q pL pR left right) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (((sourceActualCurrentJet_generated q pL pR left right t 15).2.sub
    (sourceActualCurrentJet_generated q pL pR left right t 16).2).div_const (2:ℂ)).continuousAt

private def chargeLinear : (Fin 289→ℂ)→ₗ[ℂ] ℂ where
  toFun:=constraintChargeRead
  map_add' v w:=by unfold constraintChargeRead;simp only [Pi.add_apply];ring
  map_smul' a v:=by unfold constraintChargeRead;simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring
private def covariantLinear (spatial : Fin 3→ℂ) : (Fin 289→ℂ)→ₗ[ℂ] ℂ where
  toFun:=constraintCovariantRead spatial
  map_add' v w:=by unfold constraintCovariantRead;simp only [Pi.add_apply];ring
  map_smul' a v:=by unfold constraintCovariantRead;simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring

private theorem actual_linear_window (L : (Fin 289→ℂ)→ₗ[ℂ] ℂ)
    (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum) (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    L (sourcePoleCurrentWindow q pL pR left right lambda T)=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*L (fun i=>sourcePoleActionEuler q pL pR left right 0 t i) := by
  let f : ℝ→(Fin 289→ℂ):=fun t i=>sourcePoleActionEuler q pL pR left right 0 t i
  have hf : Continuous f:=continuous_pi fun i=>actualCurrent_continuous q pL pR left right i
  have hw : Continuous (fun t=>laplaceWeight lambda t • f t):=by
    have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
    exact weight.smul hf
  have hv : (∫t in (0:ℝ)..T,laplaceWeight lambda t • f t)=sourcePoleCurrentWindow q pL pR left right lambda T:=by
    funext i
    have h:=(ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℂ] ℂ).intervalIntegral_comp_comm
      (hw.intervalIntegrable (μ:=volume) 0 T)
    change (∫t in (0:ℝ)..T,laplaceWeight lambda t*f t i)=(∫t in (0:ℝ)..T,laplaceWeight lambda t • f t) i at h
    exact h.symm
  have h:=L.toContinuousLinearMap.intervalIntegral_comp_comm (hw.intervalIntegrable (μ:=volume) 0 T)
  simp only [map_smul,smul_eq_mul] at h
  rw [hv] at h
  exact h.symm

private theorem weight_derivative (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t := by
  unfold laplaceWeight
  convert! (((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.const_mul (-lambda)).cexp) using 1
  simp [Complex.ofRealCLM]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem source_charge_IBP (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) :
    lambda*(∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCharge q pL pR left right t)=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintChargeFirst q pL pR left right t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  have cQ : Continuous (sourceConstraintCharge q pL pR left right):=
    continuous_iff_continuousAt.mpr fun t=>(sourceConstraintCharge_derivative q pL pR left right t).continuousAt
  have cD:=charge_first_continuous q pL pR left right
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  have generated (t : ℝ) : HasDerivAt (fun s=>laplaceWeight lambda s*sourceConstraintCharge q pL pR left right s)
      (laplaceWeight lambda t*sourceConstraintChargeFirst q pL pR left right t-
        lambda*(laplaceWeight lambda t*sourceConstraintCharge q pL pR left right t)) t:=by
    have h:=(weight_derivative lambda t).mul (sourceConstraintCharge_derivative q pL pR left right t)
    convert! h using 1
    ring
  have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>generated t)
    (((weight.mul cD).sub (continuous_const.mul (weight.mul cQ))).intervalIntegrable (μ:=volume) 0 T)
  have iD : IntervalIntegrable (fun t=>laplaceWeight lambda t*sourceConstraintChargeFirst q pL pR left right t) volume 0 T:=
    (weight.mul cD).intervalIntegrable 0 T
  have iQ : IntervalIntegrable (fun t=>lambda*(laplaceWeight lambda t*sourceConstraintCharge q pL pR left right t)) volume 0 T:=
    (continuous_const.mul (weight.mul cQ)).intervalIntegrable 0 T
  rw [intervalIntegral.integral_sub iD iQ,intervalIntegral.integral_const_mul] at h
  simp only [laplaceWeight,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul] at h
  unfold laplaceWeight
  linear_combination -h

theorem sourceActualCosource114_chargeBoundary (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (T : ℝ) :
    sourceActualCurrentCosource q pL pR left right spatial lambda T 114=
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintChargeFirst q pL pR left right t)+
      (∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t)-
        (laplaceWeight lambda T*sourceConstraintCharge q pL pR left right T-
          sourceConstraintCharge q pL pR left right 0) := by
  rw [sourceActualCosource114_generated]
  rw [show constraintChargeRead (sourcePoleCurrentWindow q pL pR left right lambda T)=
    ∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCharge q pL pR left right t from
      actual_linear_window chargeLinear q pL pR left right lambda T]
  rw [source_charge_IBP]
  rw [show constraintCovariantRead spatial (sourcePoleCurrentWindow q pL pR left right lambda T)=
    ∫t in (0:ℝ)..T,laplaceWeight lambda t*sourceConstraintCovariant q pL pR left right spatial t from
      actual_linear_window (covariantLinear spatial) q pL pR left right lambda T]
  ring



def sourceConstraintHalf114 (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) : ℂ :=
  (originalReadback (fullMomentum spatial lambda)*ᵥsourcePoleCurrentHalf q pL pR left right lambda) 114

theorem sourceActualCosource114_halfAxis (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) (off : 0<lambda.re) :
    Tendsto (fun T=>sourceActualCurrentCosource q pL pR left right spatial lambda T 114)
      atTop (𝓝 (sourceConstraintHalf114 q pL pR left right spatial lambda)) := by
  have h:=sourceActualCurrentCosource_halfAxis q pL pR left right spatial lambda off
  exact h 114

theorem sourceConstraintHalf114_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (spatial : Fin 3→ℂ) (lambda : ℂ) :
    sourceConstraintHalf114 q pL pR left right spatial lambda=
      lambda*constraintChargeRead (sourcePoleCurrentHalf q pL pR left right lambda)+
        constraintCovariantRead spatial (sourcePoleCurrentHalf q pL pR left right lambda) := by
  unfold sourceConstraintHalf114
  rw [constraint114_source_linear,constraintUnsupported_actualHalf_zero,add_zero]

def sourceConstraintChargeResidue (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℂ :=
  (sourceStaticResidue q left right 0 6-sourceStaticResidue q left right 0 7)/2

def sourceConstraintCovariantResidue (q : PhysicalResponsePoint) (left right : RestStateIndex) : ℂ :=
  (3/10 : ℂ)*rootTwo*(sourceStaticResidue q left right 2 1-sourceStaticResidue q left right 1 0)

theorem sourceConstraintCharge_Abel_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*constraintChargeRead (sourcePoleCurrentHalf q 0 0 left right (eta : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceConstraintChargeResidue q left right)) := by
  have h:=((sourceActualStaticHalf_Abel_zero q left right 0 6 nonrealL nonrealR).sub
    (sourceActualStaticHalf_Abel_zero q left right 0 7 nonrealL nonrealR)).div_const (2:ℂ)
  simp only [show gaugeSlot (0 : Fin 4) (6 : Fin 12) = (15 : Fin 289) from rfl,
    show gaugeSlot (0 : Fin 4) (7 : Fin 12) = (16 : Fin 289) from rfl] at h
  convert! h using 1
  funext eta
  unfold constraintChargeRead
  change (eta : ℂ)*((_ - _)/2)=((eta : ℂ)*_-(eta : ℂ)*_)/2
  ring

theorem sourceConstraint114_Abel_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun eta : ℝ=>(eta : ℂ)*sourceConstraintHalf114 q 0 0 left right 0 (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (sourceConstraintCovariantResidue q left right)) := by
  have hQ:=sourceConstraintCharge_Abel_zero q left right nonrealL nonrealR
  have hcast : Tendsto (fun eta : ℝ=>(eta : ℂ)) (nhdsWithin 0 (Ioi 0)) (𝓝 (0:ℂ)):=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hC:=((sourceActualStaticHalf_Abel_zero q left right 2 1 nonrealL nonrealR).sub
    (sourceActualStaticHalf_Abel_zero q left right 1 0 nonrealL nonrealR)).const_mul ((3/10 : ℂ)*rootTwo)
  simp only [show gaugeSlot (2 : Fin 4) (1 : Fin 12) = (34 : Fin 289) from rfl,
    show gaugeSlot (1 : Fin 4) (0 : Fin 12) = (21 : Fin 289) from rfl] at hC
  have h:=(hcast.mul hQ).add hC
  simp only [zero_mul,zero_add] at h
  convert! h using 1
  funext eta
  rw [sourceConstraintHalf114_generated]
  unfold constraintCovariantRead
  simp only [Pi.zero_apply,zero_mul,zero_add,zero_div]
  change (eta : ℂ)*((eta : ℂ)*constraintChargeRead _+(3/10 : ℂ)*rootTwo*(_-_))=
    (eta : ℂ)*((eta : ℂ)*constraintChargeRead _)+(3/10 : ℂ)*rootTwo*((eta : ℂ)*_-(eta : ℂ)*_)
  ring

end LowEnergy.PreparationVacuumPhysicalConstraint114
