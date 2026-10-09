import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalWardHalf
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPreparationActionBoundary

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalResidual
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussDensityCore GaussComposite.SourceGraph
open PreparationVacuumSourcePreparedState PreparationVacuumSourcePreparedResponse
open PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation PreparationChartGuard
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedJointGraph ActualDressedNoether
open GaussComposite.PhysicalEMDressedCharacter
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumNoetherChart PreparationVacuumPhysicalFeedback
open scoped Topology InnerProductSpace BigOperators Matrix LinearPMap
local instance : NormedAddCommGroup ScalarZero := inferInstance
local instance : InnerProductSpace ℂ ScalarZero := inferInstance
local instance : CompleteSpace ScalarZero := inferInstance
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourcePreparation sourceProfile
  sourceOperator sourceEnergy sourcePrepared sourceLeg

open ActualDressedPreparationEnergy ActualDressedTemporalHalf ActualDressedSylvester
open PreparationVacuumNoetherOrdinaryWard Filter
local instance : NormedAlgebra ℝ ResponseOp:=NormedAlgebra.restrictScalars ℝ ℂ _

/-- Both original domain-point endpoints use the same source operator and the same actual state transports. -/
def preparationLeftObserver (event : DressedEvent) : ResponseOp→L[ℂ]ℂ :=
  -(innerSL ℂ (preparationCreationMap event (sourceOperator (preparationPoint event)))).comp
      (ContinuousLinearMap.apply ℂ H (sourceDressedUnit event.epsilon event.precision))+
    (innerSL ℂ (sourcePrepared (sourceOperator (preparationPoint event)))).comp
      (ContinuousLinearMap.apply ℂ H (prepared (sourceProfile event.epsilon event.precision)))

def preparationRightObserver (event : DressedEvent) : ResponseOp→L[ℂ]ℂ :=
  -(innerSL ℂ (sourceDressedUnit event.epsilon event.precision)).comp
      (ContinuousLinearMap.apply ℂ H (preparationCreationMap event (sourceOperator (preparationPoint event))))+
    (innerSL ℂ (prepared (sourceProfile event.epsilon event.precision))).comp
      (ContinuousLinearMap.apply ℂ H (sourcePrepared (sourceOperator (preparationPoint event))))

def preparationWardObserver (event : DressedEvent) : ResponseOp→L[ℂ]ℂ :=
  preparationLeftObserver event-preparationRightObserver event

attribute [local irreducible] preparationLeftObserver preparationRightObserver preparationWardObserver

private theorem residual_image {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (T : E→L[ℂ]G) (x y : E) (c : ℂ) :
    T x=c • T y+T (x-c • y) := by
  rw [map_sub,map_smul]
  abel

private theorem energy_pair_residual {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E→L[ℂ]E) (x y rc rb : E) (energy : ℝ) :
    -inner ℂ ((energy:ℂ) • x+rc) (A x)+inner ℂ ((energy:ℂ) • y+rb) (A y)-
      (-inner ℂ x (A ((energy:ℂ) • x+rc))+inner ℂ y (A ((energy:ℂ) • y+rb)))=
      -inner ℂ rc (A x)+inner ℂ rb (A y)+inner ℂ x (A rc)-inner ℂ y (A rb) := by
  simp only [map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  ring

/-- The real source energy cancels between the two actual endpoints; only its generated residual survives. -/
theorem preparation_ward_residual_return (event : DressedEvent) (A : ResponseOp) :
    preparationWardObserver event A=
      -inner ℂ (preparationCreationMap event (preparationResidual event))
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (sourcePrepared (preparationResidual event))
        (A (prepared (sourceProfile event.epsilon event.precision)))+
      inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (preparationCreationMap event (preparationResidual event)))-
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (A (sourcePrepared (preparationResidual event))) :=by
  have creation : preparationCreationMap event (sourceOperator (preparationPoint event))=
      (sourceEnergy:ℂ) • sourceDressedUnit event.epsilon event.precision+
        preparationCreationMap event (preparationResidual event) :=by
    have source:=residual_image (preparationCreationMap event) (sourceOperator (preparationPoint event))
      (preparationPoint event).val (sourceEnergy:ℂ)
    have endpoint:=congrArg
      (fun y : H=>(sourceEnergy:ℂ) • y+preparationCreationMap event (preparationResidual event))
      (preparation_creation_actual event)
    exact source.trans endpoint
  have background : sourcePrepared (sourceOperator (preparationPoint event))=
      (sourceEnergy:ℂ) • prepared (sourceProfile event.epsilon event.precision)+
        sourcePrepared (preparationResidual event) :=by
    have source:=residual_image sourcePrepared (sourceOperator (preparationPoint event))
      (preparationPoint event).val (sourceEnergy:ℂ)
    have endpoint:=congrArg
      (fun y : H=>(sourceEnergy:ℂ) • y+sourcePrepared (preparationResidual event))
      (preparation_background event)
    exact source.trans endpoint
  have endpoints:=congrArg₂ (fun c b : H=>
    -inner ℂ c (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ b (A (prepared (sourceProfile event.epsilon event.precision)))-
      (-inner ℂ (sourceDressedUnit event.epsilon event.precision) (A c)+
        inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (A b))) creation background
  have expand : preparationWardObserver event A=
      -inner ℂ (preparationCreationMap event (sourceOperator (preparationPoint event)))
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (sourcePrepared (sourceOperator (preparationPoint event)))
        (A (prepared (sourceProfile event.epsilon event.precision)))-
      (-inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (preparationCreationMap event (sourceOperator (preparationPoint event))))+
       inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (A (sourcePrepared (sourceOperator (preparationPoint event))))) := by
    unfold preparationWardObserver preparationLeftObserver preparationRightObserver
    rfl
  exact expand.trans (endpoints.trans
    (energy_pair_residual A (sourceDressedUnit event.epsilon event.precision)
      (prepared (sourceProfile event.epsilon event.precision))
      (preparationCreationMap event (preparationResidual event))
      (sourcePrepared (preparationResidual event)) sourceEnergy))

private theorem paired_operator_price (x y : H) (A : ResponseOp) :
    ‖inner ℂ x (A y)‖≤‖x‖*‖A‖*‖y‖ :=by
  exact (norm_inner_le_norm x (A y)).trans
    ((mul_le_mul_of_nonneg_left (A.le_opNorm y) (norm_nonneg x)).trans_eq (mul_assoc _ _ _).symm)

private theorem residual_prices (event : DressedEvent) :
    ‖preparationCreationMap event (preparationResidual event)‖≤(2*‖sourceLeg true 1 0‖)*event.epsilon ∧
    ‖sourcePrepared (preparationResidual event)‖≤event.epsilon :=by
  constructor
  · exact ((preparationCreationMap event).le_opNorm _).trans
      (mul_le_mul (preparation_creation_map_price event) (preparation_residual_price event).le
        (norm_nonneg _) (mul_nonneg (by norm_num) (sourceLeg true 1 0).opNorm_nonneg))
  · rw [sourcePrepared_norm]
    exact (preparation_residual_price event).le

private theorem background_unit (event : DressedEvent) :
    ‖prepared (sourceProfile event.epsilon event.precision)‖=1 :=by
  rw [←preparation_background]
  simpa only [sourcePrepared,preparationPoint,ContinuousLinearMap.comp_apply] using
    (sourcePreparation event.epsilon event.precision).unit

/-- This operator-norm estimate controls every bounded complete response at once, without a state-convergence premise. -/
theorem preparation_ward_observer_price (event : DressedEvent) :
    ‖preparationWardObserver event‖≤2*(2*‖sourceLeg true 1 0‖+1)*event.epsilon :=by
  have legNonnegative:= (sourceLeg true 1 0).opNorm_nonneg
  apply (preparationWardObserver event).opNorm_le_bound
    (mul_nonneg (by nlinarith : 0≤2*(2*‖sourceLeg true 1 0‖+1)) event.precision.le)
  intro A
  rw [preparation_ward_residual_return]
  have prices:=residual_prices event
  have unit:=source_dressed_unit_norm event.epsilon event.precision
  have vacuum:=background_unit event
  have cL:=paired_operator_price (preparationCreationMap event (preparationResidual event))
    (sourceDressedUnit event.epsilon event.precision) A
  have cR:=paired_operator_price (sourceDressedUnit event.epsilon event.precision)
    (preparationCreationMap event (preparationResidual event)) A
  have bL:=paired_operator_price (sourcePrepared (preparationResidual event))
    (prepared (sourceProfile event.epsilon event.precision)) A
  have bR:=paired_operator_price (prepared (sourceProfile event.epsilon event.precision))
    (sourcePrepared (preparationResidual event)) A
  rw [unit,mul_one] at cL
  rw [unit,one_mul] at cR
  rw [vacuum,mul_one] at bL
  rw [vacuum,one_mul] at bR
  have cLprice:=cL.trans (mul_le_mul_of_nonneg_right prices.1 (norm_nonneg A))
  have cRprice:=cR.trans (mul_le_mul_of_nonneg_left prices.1 (norm_nonneg A))
  have bLprice:=bL.trans (mul_le_mul_of_nonneg_right prices.2 (norm_nonneg A))
  have bRprice:=bR.trans (mul_le_mul_of_nonneg_left prices.2 (norm_nonneg A))
  have triangle := norm_sub_le
    (-inner ℂ (preparationCreationMap event (preparationResidual event))
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (sourcePrepared (preparationResidual event))
        (A (prepared (sourceProfile event.epsilon event.precision)))+
      inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (preparationCreationMap event (preparationResidual event))))
    (inner ℂ (prepared (sourceProfile event.epsilon event.precision))
      (A (sourcePrepared (preparationResidual event))))
  refine triangle.trans ?_
  have three:=norm_add_le
    (-inner ℂ (preparationCreationMap event (preparationResidual event))
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (sourcePrepared (preparationResidual event))
        (A (prepared (sourceProfile event.epsilon event.precision))))
    (inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (preparationCreationMap event (preparationResidual event))))
  have two:=norm_add_le
    (-inner ℂ (preparationCreationMap event (preparationResidual event))
        (A (sourceDressedUnit event.epsilon event.precision)))
    (inner ℂ (sourcePrepared (preparationResidual event))
        (A (prepared (sourceProfile event.epsilon event.precision))))
  rw [norm_neg] at two
  nlinarith

theorem preparation_ward_observer_limit (event : DressedEvent) :
    Tendsto (fun n : ℕ=>preparationWardObserver (preparationEventSequence event n)) atTop (𝓝 0) :=by
  have precision : Tendsto preparationPrecision atTop (𝓝 0) :=by
    change Tendsto (fun n : ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have normLimit : Tendsto (fun n : ℕ=>‖preparationWardObserver (preparationEventSequence event n)‖)
      atTop (𝓝 (0:ℝ)) := by
    refine squeeze_zero (fun n=>(preparationWardObserver (preparationEventSequence event n)).opNorm_nonneg)
      (fun n=>preparation_ward_observer_price _) ?_
    simpa only [preparationEventSequence,mul_zero] using
      precision.const_mul (2*(2*‖sourceLeg true 1 0‖+1))
  have normal:=(tendsto_zero_iff_norm_tendsto_zero
    (f:=fun n : ℕ=>preparationWardObserver (preparationEventSequence event n))).mpr normLimit
  convert! normal using 1

end LowEnergy.GaussComposite.ActualDressedTemporalResidual
