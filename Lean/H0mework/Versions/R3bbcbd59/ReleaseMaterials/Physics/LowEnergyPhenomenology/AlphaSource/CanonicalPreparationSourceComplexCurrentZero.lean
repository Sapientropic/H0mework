import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceActualGapRadius

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalCausalZeroRead
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

open PreparationVacuumPhysicalConstraint114 PreparationVacuumSourceFieldFamily
open PreparationVacuumLowerClassical PreparationVacuumOriginalDensity
open SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumFockGauge PreparationVacuumActualFieldQuantization
open GaussHistoryHilbert
open GaussNativeMatter
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

open PreparationVacuumPhysicalColorCharge PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard CanonicalGradedCharge GaussFockLabel GaussFockPair
open SourceQuantumFockGauge GaussCoreLabel NativeHistoryGrade QuantizationCheck.Fermion

open PreparationVacuumPhysicalPoleLegDynamics
open PreparationVacuumNoetherChart PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge
open PreparationVacuumFieldConstraintResponse PreparationVacuumNoetherOrdinaryWard
local instance : NormedAlgebra ℝ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] noetherReader noetherForm sourceApprox sourceTestApprox

open PreparationVacuumPhysicalColorWard
local instance : NormedAlgebra ℚ (H→L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] sourcePolePrepared sourceExcitedProjection

open PreparationVacuumNonlinearFieldCurve
open PreparationVacuumPhysicalN1WardCollapse PreparationVacuumRestModeCoupling
open PreparationVacuumNativeLocalWard PreparationVacuumNativeFieldInjection
open StageNineHolonomicField
open Stage9C.Material.SpinPair StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation


open PreparationVacuumPhysicalModeContact GaussLiveMomentum CanonicalPhysicalWardCore




open scoped ContDiff



open PreparationVacuumPhysicalGaussColorTorque



open FullQuantum
open scoped Matrix.Norms.L2Operator

local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace




open PreparationVacuumPhysicalGaussMaterialContact PreparationVacuumActionDecomposition
open CanonicalPhysicalSpatial






open PreparationVacuumPhysicalN1MaterialWard

open PreparationVacuumPhysicalNativeColourReturn SourceJointResidualEnergy

open PreparationVacuumPhysicalChargeTimeZero

theorem sourceComplexStaticAbel_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (off : 0<lambda.re) (small : ‖lambda‖<sourceGapRadius q.F) :
    ‖lambda*sourceStaticAbel q left right mu a lambda-sourceStaticResidue q left right mu a‖ ≤
      2*‖lambda‖*sourceStaticErrorPrice q left right mu a := by
  classical
  unfold sourceStaticAbel sourceStaticResidue sourceStaticErrorPrice
  simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases equalEnergy : channelValue q.F i=channelValue q.F j
  · simp only [if_pos equalEnergy]
    have gap : sourceStaticGap q.F i j=0 := sub_eq_zero.mpr equalEnergy
    have nonzero : lambda≠0 := fun zero=>off.ne' (by rw [zero];rfl)
    simp only [sourceStaticDenominator,gap,Complex.ofReal_zero,mul_zero,sub_zero,
      ←mul_assoc,mul_inv_cancel₀ nonzero,one_mul,sub_self,norm_zero,le_refl]
  · simp only [if_neg equalEnergy,sub_zero]
    rw [←mul_assoc,norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (sourceSmall_abelFactor_price q.F i j lambda small (sub_ne_zero.mpr equalEnergy))
      (norm_nonneg _)).trans_eq (by ring)

theorem sourceComplexStaticHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (lambda : ℂ) (off : 0<lambda.re) (small : ‖lambda‖<sourceGapRadius q.F)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot mu a)-sourceStaticResidue q left right mu a‖ ≤
      2*‖lambda‖*sourceStaticErrorPrice q left right mu a := by
  rw [sourceStaticHalf_generated q left right mu a lambda off nonrealL nonrealR]
  exact sourceComplexStaticAbel_controlled q left right mu a lambda off small

theorem sourceComplexTimeAbel_price (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (small : ‖lambda‖<sourceGapRadius q.F) :
    ‖sourceChargeTimeAbel q left right lambda‖ ≤ 2*sourceChargeTimePrice q left right := by
  unfold sourceChargeTimeAbel sourceChargeTimePrice
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [sourceChargeTimeCoefficient,←mul_assoc,norm_mul]
  exact mul_le_mul_of_nonneg_right (sourceSmall_frequencyFactor_price q.F i j lambda small) (norm_nonneg _)

theorem sourceComplexChargeTimeHalf_controlled (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (lambda : ℂ) (off : 0<lambda.re) (small : ‖lambda‖<sourceGapRadius q.F)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    ‖lambda*sourceChargeTimeHalf q left right lambda‖ ≤ 2*‖lambda‖*sourceChargeTimePrice q left right := by
  rw [sourceChargeTimeHalf_generated q left right lambda off nonrealL nonrealR,norm_mul]
  exact (mul_le_mul_of_nonneg_left (sourceComplexTimeAbel_price q left right lambda small) (norm_nonneg _)).trans_eq (by ring)

private theorem norm_small_eventually (F : GaussUnitaryHistory.Index) :
    ∀ᶠlambda : ℂ in nhdsWithin 0 {lambda | 0<lambda.re},‖lambda‖<sourceGapRadius F := by
  have h : Tendsto (fun lambda : ℂ=>‖lambda‖) (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using
      (continuous_norm.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℂ) {lambda | 0<lambda.re}≤𝓝 0))
  exact h.eventually (Iio_mem_nhds (sourceGapRadius_positive F))

theorem sourceComplexStaticHalf_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (mu : Fin 4) (a : Fin 12) (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun lambda : ℂ=>lambda*sourcePoleCurrentHalf q 0 0 left right lambda (gaugeSlot mu a))
      (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (sourceStaticResidue q left right mu a)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (g:=fun lambda : ℂ=>2*‖lambda‖*sourceStaticErrorPrice q left right mu a)
    (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,norm_small_eventually q.F] with lambda off small
    exact sourceComplexStaticHalf_controlled q left right mu a lambda off small nonrealL nonrealR
  · have norm : Tendsto (fun lambda : ℂ=>‖lambda‖) (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using
        (continuous_norm.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℂ) {lambda | 0<lambda.re}≤𝓝 0))
    simpa only [mul_zero,zero_mul] using (norm.const_mul 2).mul_const (sourceStaticErrorPrice q left right mu a)

theorem sourceComplexChargeTimeHalf_zero (q : PhysicalResponsePoint) (left right : RestStateIndex)
    (nonrealL : q.z.im≠0) (nonrealR : q.w.im≠0) :
    Tendsto (fun lambda : ℂ=>lambda*sourceChargeTimeHalf q left right lambda)
      (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (0 : ℂ)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g:=fun lambda : ℂ=>2*‖lambda‖*sourceChargeTimePrice q left right)
    (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin,norm_small_eventually q.F] with lambda off small
    exact sourceComplexChargeTimeHalf_controlled q left right lambda off small nonrealL nonrealR
  · have norm : Tendsto (fun lambda : ℂ=>‖lambda‖) (nhdsWithin 0 {lambda | 0<lambda.re}) (𝓝 (0 : ℝ)) := by
      simpa only [norm_zero] using
        (continuous_norm.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : nhdsWithin (0 : ℂ) {lambda | 0<lambda.re}≤𝓝 0))
    simpa only [mul_zero,zero_mul] using (norm.const_mul 2).mul_const (sourceChargeTimePrice q left right)

end LowEnergy.PreparationVacuumPhysicalCausalZeroRead
