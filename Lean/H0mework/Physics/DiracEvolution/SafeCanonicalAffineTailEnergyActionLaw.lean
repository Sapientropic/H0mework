import H0mework.Physics.DiracEvolution.SafeCanonicalAffineTailEnergyCenter
import H0mework.Physics.DiracEvolution.SafeCanonicalAffinePhysicalGreenEquation

/-!
# Canonical affine tail-energy action law

This file builds the single time-`L²` mother-action read consumed by the
source-owned tail-energy center.  It does not introduce a graph carrier,
solution field, residual, or evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineGreenAssembly
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffinePhysicalGreenEquation
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineBoundaryStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyCenter
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineWeakLimitOccurrence
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalFiniteStep
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSameSourceGalerkinFamily
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGalerkinEvolution
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterGreenRateL2Read
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterFiniteL2MassRead
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterL2MassActualization
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterFiberMassRiesz
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterWeakGalerkinEnergy
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open scoped BoundedContinuousFunction ComplexOrder Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

def canonicalAffineMassTestRieszField
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    MatterCoordinateCarrier :=
  matterFiberMassRiesz
    (fixedP506L0CauchySafeMatterWeakMassMatrix point.1 point.2)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
      (diracMatterSpacetimeCoordinatePoint point.1 point.2))

def canonicalAffineActionTestRieszField
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (point : ℝ × DiracMatterSpatialCoordinates) :
    MatterCoordinateCarrier :=
  weight point.1 •
      fixedP506L0CauchySafeMatterGreenRateRieszField
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        point.1 point.2 +
    deriv weight point.1 •
      canonicalAffineMassTestRieszField a b test point

private theorem canonicalAffineMassTestRieszField_joint_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (canonicalAffineMassTestRieszField a b test) := by
  change Continuous (fun point : ℝ × DiracMatterSpatialCoordinates ↦
    matterFiberMassRieszCoordinateBilinear
      (fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
        point.1 point.2)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
        (diracMatterSpacetimeCoordinatePoint point.1 point.2)))
  have matrixContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
    fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField
      point.1 point.2) :=
    fixedP506L0CauchySafeMatterWeakMassMatrixCoordinateField_joint_continuous
  have testContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
    cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
      (diracMatterSpacetimeCoordinatePoint point.1 point.2)) := by
    exact (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
      a b test).continuous.comp
        diracMatterSpacetimeCoordinatePoint_joint_contDiff.continuous
  exact (matterFiberMassRieszCoordinateBilinear.continuous.comp
    matrixContinuous).clm_apply testContinuous

private theorem canonicalAffineGreenRateRieszField_joint_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Continuous (fun point : ℝ × DiracMatterSpatialCoordinates ↦
      fixedP506L0CauchySafeMatterGreenRateRieszField
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        point.1 point.2) := by
  have fiberReadContinuous : Continuous (fun point :
      ℝ × DiracMatterSpatialCoordinates ↦
    fixedP506L0CauchySafeMatterGreenRateFiberRead
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      point) := by
    rw [continuous_clm_apply]
    intro trialCoordinates
    exact fixedP506L0CauchySafeMatterGreenRateFiberRead_apply_continuous
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
        a b test) trialCoordinates
  exact (InnerProductSpace.toDual ℝ MatterCoordinateCarrier).symm.continuous.comp
    fiberReadContinuous

theorem canonicalAffineActionTestRieszField_joint_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Continuous (canonicalAffineActionTestRieszField a b test weight) := by
  unfold canonicalAffineActionTestRieszField
  apply Continuous.add
  · exact weightRegular.continuous.comp continuous_fst |>.smul
      (canonicalAffineGreenRateRieszField_joint_continuous a b test)
  · exact weightRegular.continuous_deriv le_rfl |>.comp continuous_fst |>.smul
      (canonicalAffineMassTestRieszField_joint_continuous a b test)

private theorem canonicalAffineActionTestRieszField_memLp
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ) :
    MemLp (fun space ↦ canonicalAffineActionTestRieszField
      a b test weight (time, space)) 2 (volume.restrict (Icc a b)) := by
  have fieldContinuous : Continuous (fun space ↦
      canonicalAffineActionTestRieszField a b test weight (time, space)) :=
    (canonicalAffineActionTestRieszField_joint_continuous
      a b test weight weightRegular).comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    fieldContinuous.continuousOn
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  apply MemLp.of_bound fieldContinuous.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

def canonicalAffineActionTestRieszL2
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  (canonicalAffineActionTestRieszField_memLp
    a b test weight weightRegular time).toLp
      (fun space ↦ canonicalAffineActionTestRieszField
        a b test weight (time, space))

private theorem canonicalAffineActionTestRieszL2_coe_ae
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ) :
    canonicalAffineActionTestRieszL2 a b test weight weightRegular time
        =ᵐ[volume.restrict (Icc a b)]
      fun space ↦ canonicalAffineActionTestRieszField
        a b test weight (time, space) :=
  (canonicalAffineActionTestRieszField_memLp
    a b test weight weightRegular time).coeFn_toLp

private theorem canonicalAffineActionTestRieszL2_norm_sub_sq
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time referenceTime : ℝ) :
    ‖canonicalAffineActionTestRieszL2 a b test weight weightRegular time -
        canonicalAffineActionTestRieszL2 a b test weight weightRegular
          referenceTime‖ ^ 2 =
      ∫ space in Icc a b,
        ‖canonicalAffineActionTestRieszField
              a b test weight (time, space) -
            canonicalAffineActionTestRieszField
              a b test weight (referenceTime, space)‖ ^ 2 := by
  rw [cauchySafeMatterSpatialL2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [
      Lp.coeFn_sub
        (canonicalAffineActionTestRieszL2
          a b test weight weightRegular time)
        (canonicalAffineActionTestRieszL2
          a b test weight weightRegular referenceTime),
      canonicalAffineActionTestRieszL2_coe_ae
        a b test weight weightRegular time,
      canonicalAffineActionTestRieszL2_coe_ae
        a b test weight weightRegular referenceTime]
    with space subRead timeRead referenceRead
  rw [subRead]
  change
    ‖canonicalAffineActionTestRieszL2
          a b test weight weightRegular time space -
        canonicalAffineActionTestRieszL2
          a b test weight weightRegular referenceTime space‖ ^ 2 = _
  rw [timeRead, referenceRead]

theorem canonicalAffineActionTestRieszL2_continuous
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Continuous (canonicalAffineActionTestRieszL2
      a b test weight weightRegular) := by
  rw [continuous_iff_continuousAt]
  intro referenceTime
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have integralContinuous : Continuous (fun time ↦
      ∫ space in Icc a b,
        ‖canonicalAffineActionTestRieszField
              a b test weight (time, space) -
            canonicalAffineActionTestRieszField
              a b test weight (referenceTime, space)‖ ^ 2) := by
    apply continuous_parametric_integral_of_continuous
      (hs := isCompact_Icc)
    have joint := canonicalAffineActionTestRieszField_joint_continuous
      a b test weight weightRegular
    fun_prop
  have squareTendsto : Tendsto
      (fun time ↦
        ‖canonicalAffineActionTestRieszL2
              a b test weight weightRegular time -
            canonicalAffineActionTestRieszL2
              a b test weight weightRegular referenceTime‖ ^ 2)
      (nhds referenceTime) (nhds 0) := by
    have integralTendsto := integralContinuous.continuousAt
      (x := referenceTime)
    have endpointEq :
        ((fun time ↦
          ∫ space in Icc a b,
            ‖canonicalAffineActionTestRieszField
                  a b test weight (time, space) -
                canonicalAffineActionTestRieszField
                  a b test weight (referenceTime, space)‖ ^ 2)
          referenceTime) = 0 := by
      simp
    change Tendsto _ (nhds referenceTime) (nhds
      ((fun time ↦
        ∫ space in Icc a b,
          ‖canonicalAffineActionTestRieszField
                a b test weight (time, space) -
              canonicalAffineActionTestRieszField
                a b test weight (referenceTime, space)‖ ^ 2)
        referenceTime)) at integralTendsto
    rw [endpointEq] at integralTendsto
    exact integralTendsto.congr'
      (Filter.Eventually.of_forall fun time ↦
        (canonicalAffineActionTestRieszL2_norm_sub_sq
          a b test weight weightRegular time referenceTime).symm)
  have sqrtTendsto :=
    Real.continuous_sqrt.continuousAt.tendsto.comp squareTendsto
  have sqrtTendstoZero : Tendsto
      ((fun value : ℝ ↦ √value) ∘ fun time ↦
        ‖canonicalAffineActionTestRieszL2
              a b test weight weightRegular time -
            canonicalAffineActionTestRieszL2
              a b test weight weightRegular referenceTime‖ ^ 2)
      (nhds referenceTime) (nhds 0) := by
    simpa only [Real.sqrt_zero] using sqrtTendsto
  exact sqrtTendstoZero.congr'
    (Filter.Eventually.of_forall fun time ↦ by
      simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)])

def canonicalAffineActionTestRieszBoundedPath
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    (Icc 0 timeEnd : Set ℝ) →ᵇ CauchySafeMatterSpatialL2 a b :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun time ↦ canonicalAffineActionTestRieszL2
        a b test weight weightRegular time.1,
      continuousOn_iff_continuous_restrict.mp
        (canonicalAffineActionTestRieszL2_continuous
          a b test weight weightRegular).continuousOn⟩

def canonicalAffineActionTestTimeL2
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
  BoundedContinuousFunction.toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ
    (canonicalAffineActionTestRieszBoundedPath
      timeEnd a b test weight weightRegular)

private theorem canonicalAffineActionTestTimeL2_coe_ae
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular =ᵐ[
        canonicalAffineTimeMeasure timeEnd]
      fun time ↦ canonicalAffineActionTestRieszL2
        a b test weight weightRegular time.1 :=
  BoundedContinuousFunction.coeFn_toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ
    (canonicalAffineActionTestRieszBoundedPath
      timeEnd a b test weight weightRegular)

private theorem canonicalAffineCorrectionTimeL2History_coe_ae
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b testCount =ᵐ[
        canonicalAffineTimeMeasure timeEnd]
      fun time ↦ canonicalAffineCorrectionL2
        timeEnd timeNonnegative a b testCount time.1 :=
  BoundedContinuousFunction.coeFn_toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ
    (canonicalAffineCorrectionL2BoundedPath
      timeEnd timeNonnegative a b testCount)

private theorem canonicalAffineTimeL2_inner_def
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (first second : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)) :
    inner ℝ first second =
      ∫ time, inner ℝ (first time) (second time)
        ∂canonicalAffineTimeMeasure timeEnd :=
  L2.inner_def first second

private theorem integral_inner_congr_ae
    {X E : Type*}
    [MeasurableSpace X]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (μ : Measure X)
    {first first' second second' : X → E}
    (firstEq : first =ᵐ[μ] first')
    (secondEq : second =ᵐ[μ] second') :
    (∫ point, inner ℝ (first point) (second point) ∂μ) =
      ∫ point, inner ℝ (first' point) (second' point) ∂μ := by
  apply integral_congr_ae
  filter_upwards [firstEq, secondEq] with point firstRead secondRead
  rw [firstRead, secondRead]

theorem canonicalAffineActionTestTimeL2_inner_history_eq_subtypeIntegral
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (testCount : ℕ) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b testCount) =
      ∫ time : Icc 0 timeEnd,
        inner ℝ
          (canonicalAffineActionTestRieszL2
            a b test weight weightRegular time.1)
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b testCount time.1)
        ∂canonicalAffineTimeMeasure timeEnd := by
  calc
    _ = ∫ time : Icc 0 timeEnd,
        inner ℝ
          (canonicalAffineActionTestTimeL2
            timeEnd a b test weight weightRegular time)
          (canonicalAffineCorrectionTimeL2History
            timeEnd timeNonnegative a b testCount time)
        ∂canonicalAffineTimeMeasure timeEnd :=
      canonicalAffineTimeL2_inner_def timeEnd a b _ _
    _ = _ := integral_inner_congr_ae
      (canonicalAffineTimeMeasure timeEnd)
      (canonicalAffineActionTestTimeL2_coe_ae
        timeEnd a b test weight weightRegular)
      (canonicalAffineCorrectionTimeL2History_coe_ae
        timeEnd timeNonnegative a b testCount)

private theorem canonicalAffineMassTestRieszField_memLp
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) :
    MemLp (fun space ↦ canonicalAffineMassTestRieszField
      a b test (time, space)) 2 (volume.restrict (Icc a b)) := by
  have fieldContinuous : Continuous (fun space ↦
      canonicalAffineMassTestRieszField a b test (time, space)) :=
    (canonicalAffineMassTestRieszField_joint_continuous a b test).comp
      (continuous_const.prodMk continuous_id)
  obtain ⟨C, bound⟩ := isCompact_Icc.exists_bound_of_continuousOn
    fieldContinuous.continuousOn
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  apply MemLp.of_bound fieldContinuous.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
  exact bound space spaceMem

def canonicalAffineMassTestRieszL2
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) : CauchySafeMatterSpatialL2 a b :=
  (canonicalAffineMassTestRieszField_memLp a b test time).toLp
    (fun space ↦ canonicalAffineMassTestRieszField a b test (time, space))

private theorem canonicalAffineMassTestRieszL2_coe_ae
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) :
    canonicalAffineMassTestRieszL2 a b test time =ᵐ[
        volume.restrict (Icc a b)]
      fun space ↦ canonicalAffineMassTestRieszField
        a b test (time, space) :=
  (canonicalAffineMassTestRieszField_memLp a b test time).coeFn_toLp

private theorem canonicalAffineGreenRateRieszL2_coe_ae
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) :
    fixedP506L0CauchySafeMatterGreenRateRieszL2
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
            a b test)
          time a b =ᵐ[volume.restrict (Icc a b)]
      fixedP506L0CauchySafeMatterGreenRateRieszField
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        time := by
  unfold fixedP506L0CauchySafeMatterGreenRateRieszL2
  exact MemLp.coeFn_toLp _

private theorem canonicalAffineActionTestRieszL2_eq
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ) :
    canonicalAffineActionTestRieszL2
        a b test weight weightRegular time =
      weight time •
          fixedP506L0CauchySafeMatterGreenRateRieszL2
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            time a b +
        deriv weight time • canonicalAffineMassTestRieszL2 a b test time := by
  apply Lp.ext
  filter_upwards [
      canonicalAffineActionTestRieszL2_coe_ae
        a b test weight weightRegular time,
      Lp.coeFn_add
        (weight time •
          fixedP506L0CauchySafeMatterGreenRateRieszL2
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test) time a b)
        (deriv weight time • canonicalAffineMassTestRieszL2 a b test time),
      Lp.coeFn_smul (weight time)
        (fixedP506L0CauchySafeMatterGreenRateRieszL2
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
          (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
            a b test) time a b),
      canonicalAffineGreenRateRieszL2_coe_ae a b test time,
      Lp.coeFn_smul (deriv weight time)
        (canonicalAffineMassTestRieszL2 a b test time),
      canonicalAffineMassTestRieszL2_coe_ae a b test time]
    with space actionRead addRead greenSmulRead greenRead massSmulRead massRead
  calc
    _ = canonicalAffineActionTestRieszField
          a b test weight (time, space) := actionRead
    _ = weight time •
          fixedP506L0CauchySafeMatterGreenRateRieszField
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            time space +
        deriv weight time • canonicalAffineMassTestRieszField
          a b test (time, space) := rfl
    _ = weight time •
          fixedP506L0CauchySafeMatterGreenRateRieszL2
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test) time a b space +
        deriv weight time •
          canonicalAffineMassTestRieszL2 a b test time space := by
      exact congrArg₂ (· + ·)
        (congrArg (fun value ↦ weight time • value) greenRead.symm)
        (congrArg (fun value ↦ deriv weight time • value) massRead.symm)
    _ = (weight time •
          fixedP506L0CauchySafeMatterGreenRateRieszL2
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test) time a b) space +
        (deriv weight time •
          canonicalAffineMassTestRieszL2 a b test time) space :=
      congrArg₂ (· + ·) greenSmulRead.symm massSmulRead.symm
    _ = _ := addRead.symm

private theorem canonicalAffineActionTestRieszL2_inner_eq
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ)
    (trial : CauchySafeMatterSpatialL2 a b) :
    inner ℝ
        (canonicalAffineActionTestRieszL2
          a b test weight weightRegular time)
        trial =
      weight time *
          fixedP506L0CauchySafeMatterGreenRateL2Read
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            time a b trial +
        deriv weight time *
          inner ℝ (canonicalAffineMassTestRieszL2 a b test time) trial := by
  calc
    _ = inner ℝ
          (weight time •
              fixedP506L0CauchySafeMatterGreenRateRieszL2
                (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest
                  a b test)
                (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
                  a b test)
                time a b +
            deriv weight time •
              canonicalAffineMassTestRieszL2 a b test time)
          trial := congrArg (fun field ↦ inner ℝ field trial)
            (canonicalAffineActionTestRieszL2_eq
              a b test weight weightRegular time)
    _ = _ := by
      simp [fixedP506L0CauchySafeMatterGreenRateL2Read,
        coe_innerSL_apply, inner_add_left, inner_smul_left]

theorem canonicalAffineMassTestRieszL2_inner_eq_integral
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (trial : CauchySafeMatterSpatialL2 a b) :
    inner ℝ (canonicalAffineMassTestRieszL2 a b test time) trial =
      ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (trial space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [canonicalAffineMassTestRieszL2_coe_ae a b test time]
    with space massRead
  change inner ℝ
      (canonicalAffineMassTestRieszL2 a b test time space)
      (trial space) = _
  rw [massRead]
  unfold canonicalAffineMassTestRieszField
  rw [cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_slice,
    matterFiberMassRiesz_pairing]
  rw [matterFiberMassPairing_apply, matterFiberMassPairing_apply]
  exact diracExteriorMatterEnergyPairing_symm _
    (fixedP506L0CauchySafeMatterWeakMassMatrix_posDef
      time space).isHermitian _ _

/-- The canonical mass-test Riesz vector reads precisely the existing spatial
mass functional on any physical `L²` field. -/
theorem canonicalAffineMassTestRieszL2_inner_eq_spatialMassRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (trial : CauchySafeMatterSpatialL2 a b) :
    inner ℝ (canonicalAffineMassTestRieszL2 a b test time) trial =
      fixedP506L0CauchySafeMatterSpatialMassRead time a b trial test := by
  calc
    _ = ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (trial space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space) :=
      canonicalAffineMassTestRieszL2_inner_eq_integral a b test time trial
    _ = _ := by
      rw [fixedP506L0CauchySafeMatterSpatialMassRead]
      apply integral_congr_ae
      filter_upwards [
        (cauchySafeMatterSmoothCompactTest_memLp a b
          (cauchySafeMatterCanonicalInteriorDenseTest a b test)).coeFn_toLp]
          with space testRead
      change matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (trial space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space) =
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (trial space)
          (((cauchySafeMatterSmoothCompactTest_memLp a b
            (cauchySafeMatterCanonicalInteriorDenseTest a b test)).toLp
              (cauchySafeMatterCanonicalInteriorDenseTest a b test)) space)
      rw [testRead]

private theorem canonicalAffineMassTestRieszL2_inner_correction_eq_pairing
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (time : Icc 0 timeEnd) :
    inner ℝ (canonicalAffineMassTestRieszL2 a b test time.1)
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1) =
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).pairing time.1 := by
  let basis :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis a b testCount
  let basisRegular :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular a b testCount
  let basisCompact :=
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact a b testCount
  let coefficient :=
    fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
      timeEnd timeNonnegative a b testCount
  let testCoefficient :=
    fixedP506L0CauchySafeMatterCanonicalTestCoefficient
      a b testCount test
  let denseTest := cauchySafeMatterCanonicalInteriorDenseTest a b test
  have testRepresentation : ∀ space,
      fixedMatterTrialCoordinates basis testCoefficient space =
        (denseTest : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
          space := by
    intro space
    unfold fixedMatterTrialCoordinates
    simp only [testCoefficient,
      fixedP506L0CauchySafeMatterCanonicalTestCoefficient, dif_pos entered]
    exact Classical.choose_spec
      (cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
        a b testCount test entered) space
  have finiteReadEq := fixedMatterFiniteMassRead_eq_galerkinWeakTestPairing
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    a b
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
      a b testCount)
    coefficient testCoefficient time.1 (operatorBound time.1 time.2)
    denseTest testRepresentation
  have finiteReadIntegral := fixedMatterFiniteMassRead_eq_integral
    C basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
    (coefficient time.1) time.1 a b (operatorBound time.1 time.2) denseTest
  have correctionCoe : ∀ᵐ space ∂volume.restrict (Icc a b),
      canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1 space =
        fixedMatterTrialCoordinates basis (coefficient time.1) space := by
    exact fixedMatterTrialL2_coe_ae
      basis (fun mode ↦ (basisRegular mode).continuous) basisCompact
      (coefficient time.1) a b
  calc
    _ = ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b testCount time.1 space)
          ((denseTest : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
            space) := canonicalAffineMassTestRieszL2_inner_eq_integral
              a b test time.1 _
    _ = ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time.1 space)
          (fixedMatterTrialCoordinates basis (coefficient time.1) space)
          ((denseTest : DiracMatterSpatialCoordinates → MatterCoordinateCarrier)
            space) := by
      apply integral_congr_ae
      filter_upwards [correctionCoe] with space correctionRead
      rw [correctionRead]
    _ = fixedMatterFiniteMassRead C basis
          (fun mode ↦ (basisRegular mode).continuous) basisCompact
          (coefficient time.1) time.1 a b (operatorBound time.1 time.2)
          denseTest := finiteReadIntegral.symm
    _ = galerkinWeakTestPairing
          (fixedP506L0CauchySafeMatterWeakMassForm basis
            (fun mode ↦ (basisRegular mode).continuous) basisCompact)
          coefficient testCoefficient time.1 := finiteReadEq
    _ = _ := rfl

private theorem canonicalAffineCorrectionL2_greenRate
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (time : ℝ) :
    fixedP506L0CauchySafeMatterGreenRateL2Read
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
          a b test)
        time a b
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time) =
      (canonicalAffineCorrectionPairingPath
        timeEnd timeNonnegative a b testCount test).rate time +
        boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) := by
  have finiteGreen := canonicalAffineFiniteMatterL2_greenRate
    timeEnd timeNonnegative a b boxOrder testCount test entered time
  have sourceGreen := canonicalSourceLift_greenRate
    a b boxOrder testCount test entered time
  unfold canonicalAffineFiniteMatterL2 at finiteGreen
  rw [map_add, sourceGreen] at finiteGreen
  linarith

private theorem canonicalAffineActionTestRieszL2_inner_correction_eq
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : Icc 0 timeEnd) :
    inner ℝ
        (canonicalAffineActionTestRieszL2
          a b test weight weightRegular time.1)
        (canonicalAffineCorrectionL2
          timeEnd timeNonnegative a b testCount time.1) =
      weight time.1 *
          ((canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).rate time.1 +
            boundaryLiftStiffnessFunctional a b testCount time.1
              (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                a b testCount test)) +
        deriv weight time.1 *
          (canonicalAffineCorrectionPairingPath
            timeEnd timeNonnegative a b testCount test).pairing time.1 := by
  calc
    _ = weight time.1 *
          fixedP506L0CauchySafeMatterGreenRateL2Read
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            time.1 a b
            (canonicalAffineCorrectionL2
              timeEnd timeNonnegative a b testCount time.1) +
        deriv weight time.1 *
          inner ℝ (canonicalAffineMassTestRieszL2 a b test time.1)
            (canonicalAffineCorrectionL2
              timeEnd timeNonnegative a b testCount time.1) :=
      canonicalAffineActionTestRieszL2_inner_eq
        a b test weight weightRegular time.1 _
    _ = _ := by
      rw [canonicalAffineCorrectionL2_greenRate
          timeEnd timeNonnegative a b boxOrder testCount test entered time.1,
        canonicalAffineMassTestRieszL2_inner_correction_eq_pairing
          timeEnd timeNonnegative a b C operatorBound
          testCount test entered time]

private theorem canonicalAffine_subtypeIntegral_eq_intervalIntegral
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (field : ℝ → ℝ) :
    (∫ time : Icc 0 timeEnd, field time.1
        ∂canonicalAffineTimeMeasure timeEnd) =
      ∫ time in 0..timeEnd, field time := by
  unfold canonicalAffineTimeMeasure
  rw [integral_subtype_comap measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le timeNonnegative]

private theorem canonicalAffineActionTestTimeL2_inner_history_eq_intervalIntegral
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b testCount) =
      ∫ time in 0..timeEnd,
        weight time *
            ((canonicalAffineCorrectionPairingPath
                timeEnd timeNonnegative a b testCount test).rate time +
              boundaryLiftStiffnessFunctional a b testCount time
                (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                  a b testCount test)) +
          deriv weight time *
            (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).pairing time := by
  calc
    _ = ∫ time : Icc 0 timeEnd,
        inner ℝ
          (canonicalAffineActionTestRieszL2
            a b test weight weightRegular time.1)
          (canonicalAffineCorrectionL2
            timeEnd timeNonnegative a b testCount time.1)
        ∂canonicalAffineTimeMeasure timeEnd :=
      canonicalAffineActionTestTimeL2_inner_history_eq_subtypeIntegral
        timeEnd timeNonnegative a b test weight weightRegular testCount
    _ = ∫ time : Icc 0 timeEnd,
        (weight time.1 *
            ((canonicalAffineCorrectionPairingPath
                timeEnd timeNonnegative a b testCount test).rate time.1 +
              boundaryLiftStiffnessFunctional a b testCount time.1
                (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                  a b testCount test)) +
          deriv weight time.1 *
            (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).pairing time.1)
        ∂canonicalAffineTimeMeasure timeEnd := by
      apply integral_congr_ae
      filter_upwards with time
      exact canonicalAffineActionTestRieszL2_inner_correction_eq
        timeEnd timeNonnegative a b boxOrder C operatorBound
        testCount test entered weight weightRegular time
    _ = _ := canonicalAffine_subtypeIntegral_eq_intervalIntegral
      timeEnd timeNonnegative (fun time ↦
        weight time *
            ((canonicalAffineCorrectionPairingPath
                timeEnd timeNonnegative a b testCount test).rate time +
              boundaryLiftStiffnessFunctional a b testCount time
                (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                  a b testCount test)) +
          deriv weight time *
            (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).pairing time)

private theorem canonicalAffineActionTest_interval_eq_boundary
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    (∫ time in 0..timeEnd,
        weight time *
            ((canonicalAffineCorrectionPairingPath
                timeEnd timeNonnegative a b testCount test).rate time +
              boundaryLiftStiffnessFunctional a b testCount time
                (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                  a b testCount test)) +
          deriv weight time *
            (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).pairing time) =
      ∫ time in 0..timeEnd,
        weight time * boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) := by
  let path := canonicalAffineCorrectionPairingPath
    timeEnd timeNonnegative a b testCount test
  let testCoefficient := fixedP506L0CauchySafeMatterCanonicalTestCoefficient
    a b testCount test
  have weightContinuous : Continuous weight := weightRegular.continuous
  have derivativeContinuous : Continuous (deriv weight) :=
    weightRegular.continuous_deriv le_rfl
  have weightedRateIntegrable : IntervalIntegrable
      (fun time ↦ weight time * path.rate time) volume 0 timeEnd :=
    (weightContinuous.continuousOn.mul path.rateContinuousOn
      ).intervalIntegrable_of_Icc timeNonnegative
  have weightedPairingIntegrable : IntervalIntegrable
      (fun time ↦ deriv weight time * path.pairing time) volume 0 timeEnd :=
    (derivativeContinuous.continuousOn.mul path.pairingContinuousOn
      ).intervalIntegrable_of_Icc timeNonnegative
  have boundaryContinuous : Continuous (fun time ↦
      boundaryLiftStiffnessFunctional a b testCount time testCoefficient) :=
    (boundaryLiftStiffnessFunctional_continuous a b testCount).clm_apply
      continuous_const
  have weightedBoundaryIntegrable : IntervalIntegrable
      (fun time ↦ weight time *
        boundaryLiftStiffnessFunctional a b testCount time testCoefficient)
      volume 0 timeEnd :=
    (weightContinuous.mul boundaryContinuous).continuousOn
      |>.intervalIntegrable_of_Icc timeNonnegative
  have weightedRate := path.weighted_integral_rate
    timeNonnegative weight weightRegular
  have pathInitial : path.pairing 0 = 0 := by
    change galerkinWeakTestPairing
      (fixedP506L0CauchySafeMatterCanonicalWeakMassForm a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve
        timeEnd timeNonnegative a b testCount)
      (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
        a b testCount test) 0 = 0
    unfold galerkinWeakTestPairing
    rw [fixedP506L0CauchySafeMatterCanonicalAffineCorrectionCurve_initial]
    simp
  have cancellation :
      (∫ time in 0..timeEnd,
          weight time * path.rate time +
            deriv weight time * path.pairing time) = 0 := by
    rw [intervalIntegral.integral_add
      weightedRateIntegrable weightedPairingIntegrable]
    rw [weightEndZero, pathInitial, zero_mul, mul_zero,
      sub_zero] at weightedRate
    simp only [zero_sub] at weightedRate
    linarith
  calc
    _ = ∫ time in 0..timeEnd,
        (weight time * path.rate time +
            deriv weight time * path.pairing time) +
          weight time *
            boundaryLiftStiffnessFunctional a b testCount time
              testCoefficient := by
      apply intervalIntegral.integral_congr
      intro time _timeMem
      ring
    _ = (∫ time in 0..timeEnd,
          weight time * path.rate time +
            deriv weight time * path.pairing time) +
        ∫ time in 0..timeEnd,
          weight time *
            boundaryLiftStiffnessFunctional a b testCount time
              testCoefficient :=
      intervalIntegral.integral_add
        (weightedRateIntegrable.add weightedPairingIntegrable)
        weightedBoundaryIntegrable
    _ = _ := by rw [cancellation, zero_add]

def canonicalAffineSourceBoundaryActionDensity
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (time : ℝ) : ℝ :=
  weight time *
    (canonicalSourceLiftMassRate a b test time -
      fixedP506L0CauchySafeMatterGreenRateL2Read
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
        (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
          a b test)
        time a b
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b))

def canonicalAffineSourceBoundaryActionValue
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ) : ℝ :=
  ∫ time in 0..timeEnd,
    canonicalAffineSourceBoundaryActionDensity a b test weight time

private theorem canonicalAffineBoundaryActionDensity_eq_source
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (weight : ℝ → ℝ)
    (time : ℝ) :
    weight time * boundaryLiftStiffnessFunctional a b testCount time
        (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
          a b testCount test) =
      canonicalAffineSourceBoundaryActionDensity a b test weight time := by
  have sourceGreen := canonicalSourceLift_greenRate
    a b boxOrder testCount test entered time
  unfold canonicalAffineSourceBoundaryActionDensity
  congr 1
  linarith

private theorem canonicalAffineActionTestTimeL2_inner_history_eq_sourceValue
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (C : ℝ)
    (operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C)
    (testCount test : ℕ)
    (entered : cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineCorrectionTimeL2History
          timeEnd timeNonnegative a b testCount) =
      canonicalAffineSourceBoundaryActionValue
        timeEnd a b test weight := by
  calc
    _ = ∫ time in 0..timeEnd,
        weight time *
            ((canonicalAffineCorrectionPairingPath
                timeEnd timeNonnegative a b testCount test).rate time +
              boundaryLiftStiffnessFunctional a b testCount time
                (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
                  a b testCount test)) +
          deriv weight time *
            (canonicalAffineCorrectionPairingPath
              timeEnd timeNonnegative a b testCount test).pairing time :=
      canonicalAffineActionTestTimeL2_inner_history_eq_intervalIntegral
        timeEnd timeNonnegative a b boxOrder C operatorBound
        testCount test entered weight weightRegular
    _ = ∫ time in 0..timeEnd,
        weight time * boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) :=
      canonicalAffineActionTest_interval_eq_boundary
        timeEnd timeNonnegative a b testCount test weight weightRegular
        weightEndZero
    _ = _ := by
      unfold canonicalAffineSourceBoundaryActionValue
      apply intervalIntegral.integral_congr
      intro time _timeMem
      exact canonicalAffineBoundaryActionDensity_eq_source
        a b boxOrder testCount test entered weight time

/-- The source-owned whole-time tail-energy center inherits every compactly
supported weighted mother-action read from the eventual exact canonical
affine history.  No subsequence, representative, graph completion, or target
field enters the theorem. -/
theorem canonicalAffineCorrectionTimeL2TailEnergyCenter_weightedActionLaw
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineCorrectionTimeL2TailEnergyCenter
          timeEnd timeNonnegative a b boxOrder) =
      canonicalAffineSourceBoundaryActionValue
        timeEnd a b test weight := by
  let boundExistence := exists_fixedMassPairingOperatorBoundOnBox
    0 timeEnd a b timeNonnegative boxOrder
  let C := Classical.choose boundExistence
  have operatorBound : ∀ time ∈ Icc 0 timeEnd,
      ∀ space ∈ Icc a b,
        ‖matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)‖ ≤ C :=
    (Classical.choose_spec boundExistence).2
  have centerRead :=
    canonicalAffineCorrectionTimeL2TailEnergyCenter_read_eq_of_eventually_exact
      timeEnd timeNonnegative a b boxOrder
      (innerSL ℝ (canonicalAffineActionTestTimeL2
        timeEnd a b test weight weightRegular))
      (canonicalAffineSourceBoundaryActionValue timeEnd a b test weight)
      (cauchySafeMatterCanonicalInteriorTestEntry test)
      (by
        intro testCount entered
        simpa only [coe_innerSL_apply] using
          canonicalAffineActionTestTimeL2_inner_history_eq_sourceValue
            timeEnd timeNonnegative a b boxOrder C operatorBound
            testCount test entered weight weightRegular weightEndZero)
  simpa only [coe_innerSL_apply] using centerRead

/-- The fixed source lift as one constant whole-time Bochner `L²` field. -/
def canonicalAffineSourceLiftTimeL2
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
  BoundedContinuousFunction.toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ
    (BoundedContinuousFunction.const (Icc 0 timeEnd)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b))

/-- The unique source-generated total affine output: fixed source lift plus
the minimum-energy correction selected by the complete canonical history. -/
def canonicalAffinePhysicalTimeL2Output
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd) :=
  canonicalAffineSourceLiftTimeL2 timeEnd a b +
    canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder

/-- The generated affine output reads as the source lift plus the canonical
minimum-energy correction at almost every time. -/
theorem canonicalAffinePhysicalTimeL2Output_coe_ae
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b) :
    canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
      fun time ↦ canonicalAffineSourceLiftTimeL2 timeEnd a b time +
        canonicalAffineCorrectionTimeL2TailEnergyCenter
          timeEnd timeNonnegative a b boxOrder time := by
  exact Lp.coeFn_add
    (canonicalAffineSourceLiftTimeL2 timeEnd a b)
    (canonicalAffineCorrectionTimeL2TailEnergyCenter
      timeEnd timeNonnegative a b boxOrder)

theorem canonicalAffineSourceLiftTimeL2_coe_ae
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    canonicalAffineSourceLiftTimeL2 timeEnd a b =ᵐ[
        canonicalAffineTimeMeasure timeEnd]
      fun _time ↦
        fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b := by
  exact BoundedContinuousFunction.coeFn_toLp 2
    (canonicalAffineTimeMeasure timeEnd) ℝ
    (BoundedContinuousFunction.const (Icc 0 timeEnd)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b))

private theorem canonicalAffineSourceInitialL2_zero_coe_ae
    (a b : DiracMatterSpatialCoordinates) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space =
        matterCoordinateEquiv diracSpinTwoMatterProbe := by
  have sourceRead : ∀ᵐ space ∂volume.restrict (Icc a b),
      fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space =
        fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates
          0 space := by
    unfold fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
    exact MemLp.coeFn_toLp _
  filter_upwards [sourceRead] with space read
  rw [read, fixedP506L0CauchySafeMatterCanonicalSourceInitialCoordinates_zero]

theorem canonicalAffineMassTestRieszL2_inner_sourceLift_eq
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ) :
    inner ℝ (canonicalAffineMassTestRieszL2 a b test time)
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) =
      canonicalSourceLiftMassRead a b test time := by
  calc
    _ = ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b space)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space) :=
      canonicalAffineMassTestRieszL2_inner_eq_integral a b test time _
    _ = ∫ space in Icc a b,
        matterFiberMassPairing
          (fixedP506L0CauchySafeMatterWeakMassMatrix time space)
          (matterCoordinateEquiv diracSpinTwoMatterProbe)
          ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space) := by
      apply integral_congr_ae
      filter_upwards [canonicalAffineSourceInitialL2_zero_coe_ae a b]
        with space sourceRead
      rw [sourceRead]
    _ = canonicalSourceLiftMassRead a b test time := rfl

private theorem canonicalAffineActionTestRieszL2_inner_sourceLift_eq
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (time : ℝ) :
    inner ℝ
        (canonicalAffineActionTestRieszL2
          a b test weight weightRegular time)
        (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) =
      weight time *
          fixedP506L0CauchySafeMatterGreenRateL2Read
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            time a b
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) +
        deriv weight time * canonicalSourceLiftMassRead a b test time := by
  calc
    _ = weight time *
          fixedP506L0CauchySafeMatterGreenRateL2Read
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
            (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
              a b test)
            time a b
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) +
        deriv weight time *
          inner ℝ (canonicalAffineMassTestRieszL2 a b test time)
            (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) :=
      canonicalAffineActionTestRieszL2_inner_eq
        a b test weight weightRegular time _
    _ = _ := congrArg₂ (· + ·) rfl
      (congrArg (fun value ↦ deriv weight time * value)
        (canonicalAffineMassTestRieszL2_inner_sourceLift_eq
          a b test time))

private theorem canonicalAffineActionTestTimeL2_inner_sourceLift_eq_integral
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineSourceLiftTimeL2 timeEnd a b) =
      ∫ time in 0..timeEnd,
        inner ℝ
          (canonicalAffineActionTestRieszL2
            a b test weight weightRegular time)
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b) := by
  calc
    _ = ∫ time : Icc 0 timeEnd,
        inner ℝ
          (canonicalAffineActionTestTimeL2
            timeEnd a b test weight weightRegular time)
          (canonicalAffineSourceLiftTimeL2 timeEnd a b time)
        ∂canonicalAffineTimeMeasure timeEnd :=
      canonicalAffineTimeL2_inner_def timeEnd a b _ _
    _ = ∫ time : Icc 0 timeEnd,
        inner ℝ
          (canonicalAffineActionTestRieszL2
            a b test weight weightRegular time.1)
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b)
        ∂canonicalAffineTimeMeasure timeEnd :=
      integral_inner_congr_ae
        (canonicalAffineTimeMeasure timeEnd)
        (canonicalAffineActionTestTimeL2_coe_ae
          timeEnd a b test weight weightRegular)
        (canonicalAffineSourceLiftTimeL2_coe_ae timeEnd a b)
    _ = _ := canonicalAffine_subtypeIntegral_eq_intervalIntegral
      timeEnd timeNonnegative (fun time ↦
        inner ℝ
          (canonicalAffineActionTestRieszL2
            a b test weight weightRegular time)
          (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b))

private theorem canonicalAffineActionTestTimeL2_inner_sourceLift_eq_boundary
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffineSourceLiftTimeL2 timeEnd a b) =
      -canonicalAffineSourceBoundaryActionValue
          timeEnd a b test weight -
        weight 0 * canonicalSourceLiftMassRead a b test 0 := by
  let sourceAction : ℝ → ℝ := fun time ↦
    inner ℝ
      (canonicalAffineActionTestRieszL2
        a b test weight weightRegular time)
      (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2 0 a b)
  let boundaryAction : ℝ → ℝ := fun time ↦
    canonicalAffineSourceBoundaryActionDensity a b test weight time
  have sourceActionContinuous : Continuous sourceAction :=
    (canonicalAffineActionTestRieszL2_continuous
      a b test weight weightRegular).inner continuous_const
  have boundaryActionContinuous : Continuous boundaryAction := by
    let testCount := cauchySafeMatterCanonicalInteriorTestEntry test
    have boundaryEq : boundaryAction = fun time ↦
        weight time * boundaryLiftStiffnessFunctional a b testCount time
          (fixedP506L0CauchySafeMatterCanonicalTestCoefficient
            a b testCount test) := by
      funext time
      exact (canonicalAffineBoundaryActionDensity_eq_source
        a b boxOrder testCount test le_rfl weight time).symm
    rw [boundaryEq]
    exact weightRegular.continuous.mul
      ((boundaryLiftStiffnessFunctional_continuous a b testCount).clm_apply
        continuous_const)
  have sourceActionIntegrable : IntervalIntegrable sourceAction volume
      0 timeEnd :=
    sourceActionContinuous.continuousOn.intervalIntegrable_of_Icc
      timeNonnegative
  have boundaryActionIntegrable : IntervalIntegrable boundaryAction volume
      0 timeEnd :=
    boundaryActionContinuous.continuousOn.intervalIntegrable_of_Icc
      timeNonnegative
  have combinedBoundary :
      (∫ time in 0..timeEnd, sourceAction time + boundaryAction time) =
        -weight 0 * canonicalSourceLiftMassRead a b test 0 := by
    calc
      _ = ∫ time in 0..timeEnd,
          weight time * canonicalSourceLiftMassRate a b test time +
            deriv weight time *
              canonicalSourceLiftMassRead a b test time := by
        apply intervalIntegral.integral_congr
        intro time _timeMem
        change sourceAction time + boundaryAction time = _
        rw [show sourceAction time =
            weight time *
                fixedP506L0CauchySafeMatterGreenRateL2Read
                  (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest
                    a b test)
                  (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
                    a b test)
                  time a b
                  (fixedP506L0CauchySafeMatterCanonicalSourceInitialL2
                    0 a b) +
              deriv weight time *
                canonicalSourceLiftMassRead a b test time by
          exact canonicalAffineActionTestRieszL2_inner_sourceLift_eq
            a b test weight weightRegular time]
        unfold boundaryAction canonicalAffineSourceBoundaryActionDensity
        ring
      _ = (∫ time in 0..timeEnd,
          weight time * canonicalSourceLiftMassRate a b test time) +
        ∫ time in 0..timeEnd,
          deriv weight time * canonicalSourceLiftMassRead a b test time := by
        rw [intervalIntegral.integral_add]
        · exact (weightRegular.continuous.continuousOn.mul
            (canonicalSourceLiftMassPairingPath
              timeEnd a b test).rateContinuousOn
            ).intervalIntegrable_of_Icc timeNonnegative
        · exact ((weightRegular.continuous_deriv le_rfl).continuousOn.mul
            (canonicalSourceLiftMassPairingPath
              timeEnd a b test).pairingContinuousOn
            ).intervalIntegrable_of_Icc timeNonnegative
      _ = _ := by
        rw [canonicalSourceLiftMassRead_weighted_integral_rate
          timeEnd timeNonnegative a b test weight weightRegular,
          weightEndZero]
        ring
  rw [canonicalAffineActionTestTimeL2_inner_sourceLift_eq_integral
    timeEnd timeNonnegative a b test weight weightRegular]
  unfold canonicalAffineSourceBoundaryActionValue
  have sumBoundary :
      (∫ time in 0..timeEnd, sourceAction time) +
          ∫ time in 0..timeEnd, boundaryAction time =
        -weight 0 * canonicalSourceLiftMassRead a b test 0 := by
    rw [← intervalIntegral.integral_add
      sourceActionIntegrable boundaryActionIntegrable]
    exact combinedBoundary
  change (∫ time in 0..timeEnd, sourceAction time) =
    -(∫ time in 0..timeEnd, boundaryAction time) -
      weight 0 * canonicalSourceLiftMassRead a b test 0
  linarith

/-- Endpoint-zero weights retain the exact source initial mass boundary in
the generated total affine action. -/
theorem canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_endZero
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) =
      -weight 0 * canonicalSourceLiftMassRead a b test 0 := by
  calc
    _ = inner ℝ
          (canonicalAffineActionTestTimeL2
            timeEnd a b test weight weightRegular)
          (canonicalAffineSourceLiftTimeL2 timeEnd a b) +
        inner ℝ
          (canonicalAffineActionTestTimeL2
            timeEnd a b test weight weightRegular)
          (canonicalAffineCorrectionTimeL2TailEnergyCenter
            timeEnd timeNonnegative a b boxOrder) := by
      exact inner_add_right _ _ _
    _ = (-canonicalAffineSourceBoundaryActionValue
            timeEnd a b test weight -
          weight 0 * canonicalSourceLiftMassRead a b test 0) +
        canonicalAffineSourceBoundaryActionValue
          timeEnd a b test weight := congrArg₂ (· + ·)
      (canonicalAffineActionTestTimeL2_inner_sourceLift_eq_boundary
        timeEnd timeNonnegative a b boxOrder test weight weightRegular
          weightEndZero)
      (canonicalAffineCorrectionTimeL2TailEnergyCenter_weightedActionLaw
        timeEnd timeNonnegative a b boxOrder test weight weightRegular
          weightEndZero)
    _ = _ := by ring

/-- The source-generated total affine output satisfies the homogeneous
weighted distributional mother-action law.  The output is fixed by the
source history; no weak occurrence or representative is supplied. -/
theorem canonicalAffinePhysicalTimeL2Output_weightedActionLaw
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular)
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder) = 0 := by
  calc
    _ = -weight 0 * canonicalSourceLiftMassRead a b test 0 :=
      canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_endZero
        timeEnd timeNonnegative a b boxOrder test weight weightRegular
          weightEndZero
    _ = 0 := by rw [weightZero, neg_zero, zero_mul]

private def canonicalAffineTimeL2WeightedActionRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (trial : CauchySafeMatterSpatialL2 a b)
    (time : ℝ) : ℝ :=
  inner ℝ
    (canonicalAffineActionTestRieszL2
      a b test weight weightRegular time) trial

private theorem canonicalAffineActionTestTimeL2_inner_eq_weightedReadIntegral
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (trial : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)) :
    inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular) trial =
      ∫ time : Icc 0 timeEnd,
        canonicalAffineTimeL2WeightedActionRead
          a b test weight weightRegular (trial time) time.1
        ∂canonicalAffineTimeMeasure timeEnd := by
  apply (canonicalAffineTimeL2_inner_def timeEnd a b
    (canonicalAffineActionTestTimeL2
      timeEnd a b test weight weightRegular) trial).trans
  apply integral_congr_ae
  filter_upwards [canonicalAffineActionTestTimeL2_coe_ae
      timeEnd a b test weight weightRegular] with time actionRead
  exact congrArg (fun field ↦ inner ℝ field (trial time)) actionRead

private def canonicalAffineTimeL2MassRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (trial : CauchySafeMatterSpatialL2 a b)
    (time : ℝ) : ℝ :=
  inner ℝ (canonicalAffineMassTestRieszL2 a b test time) trial

private def canonicalAffineTimeL2GreenRateRead
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (trial : CauchySafeMatterSpatialL2 a b)
    (time : ℝ) : ℝ :=
  fixedP506L0CauchySafeMatterGreenRateL2Read
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test)
    (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
      a b test)
    time a b trial

/-- Action-mass read of the canonical total output at one time in the fixed
interval. -/
def canonicalAffinePhysicalTimeL2MassRead
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (time : Icc 0 timeEnd) : ℝ :=
  canonicalAffineTimeL2MassRead a b test
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder time) time.1

/-- The time-`L²` output's canonical mass read is exactly the existing
physical spatial mass read at that time. -/
theorem canonicalAffinePhysicalTimeL2MassRead_eq_spatialMassRead
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (time : Icc 0 timeEnd) :
    canonicalAffinePhysicalTimeL2MassRead
        timeEnd timeNonnegative a b boxOrder test time =
      fixedP506L0CauchySafeMatterSpatialMassRead time.1 a b
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) test := by
  change inner ℝ (canonicalAffineMassTestRieszL2 a b test time.1)
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder time) = _
  exact canonicalAffineMassTestRieszL2_inner_eq_spatialMassRead
    a b test time.1 _

/-- Green-rate read of the canonical total output at one time in the fixed
interval. -/
def canonicalAffinePhysicalTimeL2GreenRate
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (time : Icc 0 timeEnd) : ℝ :=
  canonicalAffineTimeL2GreenRateRead a b test
    (canonicalAffinePhysicalTimeL2Output
      timeEnd timeNonnegative a b boxOrder time) time.1

private theorem canonicalAffineTimeL2WeightedRead_integrable
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (trial : Lp (CauchySafeMatterSpatialL2 a b) 2
      (canonicalAffineTimeMeasure timeEnd)) :
    Integrable (fun time : Icc 0 timeEnd ↦
      canonicalAffineTimeL2WeightedActionRead
        a b test weight weightRegular
        (trial time) time.1)
      (canonicalAffineTimeMeasure timeEnd) := by
  have innerIntegrable := L2.integrable_inner (𝕜 := ℝ)
    (canonicalAffineActionTestTimeL2
      timeEnd a b test weight weightRegular) trial
  have readEq : (fun time : Icc 0 timeEnd ↦
      inner ℝ
        (canonicalAffineActionTestTimeL2
          timeEnd a b test weight weightRegular time)
        (trial time)) =ᵐ[canonicalAffineTimeMeasure timeEnd]
      (fun time : Icc 0 timeEnd ↦
        canonicalAffineTimeL2WeightedActionRead
          a b test weight weightRegular (trial time) time.1) := by
    filter_upwards [canonicalAffineActionTestTimeL2_coe_ae
        timeEnd a b test weight weightRegular] with time actionRead
    exact congrArg (fun field ↦ inner ℝ field (trial time)) actionRead
  exact (integrable_congr readEq).mp innerIntegrable

private theorem canonicalAffineTimeL2GreenRateRead_integrable
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    ∀ trial : Lp (CauchySafeMatterSpatialL2 a b) 2
        (canonicalAffineTimeMeasure timeEnd),
    Integrable (fun time : Icc 0 timeEnd ↦
      canonicalAffineTimeL2GreenRateRead a b test (trial time) time.1)
      (canonicalAffineTimeMeasure timeEnd) := by
  intro trial
  have weightedIntegrable :=
    canonicalAffineTimeL2WeightedRead_integrable
      timeEnd a b test (fun _ : ℝ ↦ 1) contDiff_const trial
  have readEq : (fun time : Icc 0 timeEnd ↦
      canonicalAffineTimeL2WeightedActionRead
        a b test (fun _ : ℝ ↦ 1) contDiff_const (trial time) time.1) =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
      (fun time : Icc 0 timeEnd ↦
        canonicalAffineTimeL2GreenRateRead
          a b test (trial time) time.1) :=
    Filter.Eventually.of_forall fun time ↦ by
      have read := canonicalAffineActionTestRieszL2_inner_eq
        a b test (fun _ : ℝ ↦ 1) contDiff_const time.1 (trial time)
      simpa [canonicalAffineTimeL2WeightedActionRead,
        canonicalAffineTimeL2GreenRateRead] using read
  exact (integrable_congr readEq).mp weightedIntegrable

private theorem canonicalAffineTimeL2MassRead_integrable
    (timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    ∀ trial : Lp (CauchySafeMatterSpatialL2 a b) 2
        (canonicalAffineTimeMeasure timeEnd),
    Integrable (fun time : Icc 0 timeEnd ↦
      canonicalAffineTimeL2MassRead a b test (trial time) time.1)
      (canonicalAffineTimeMeasure timeEnd) := by
  intro trial
  have weightedIntegrable :=
    canonicalAffineTimeL2WeightedRead_integrable
      timeEnd a b test id contDiff_id trial
  have timeRateIntegrable : Integrable (fun time : Icc 0 timeEnd ↦
      time.1 * canonicalAffineTimeL2GreenRateRead
        a b test (trial time) time.1)
      (canonicalAffineTimeMeasure timeEnd) := by
    apply (canonicalAffineTimeL2GreenRateRead_integrable
      timeEnd a b test trial).bdd_mul
    · exact continuous_subtype_val.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun time ↦ by
        simpa [Real.norm_eq_abs, abs_of_nonneg time.2.1] using time.2.2
  have differenceIntegrable := weightedIntegrable.sub timeRateIntegrable
  have readEq : (fun time : Icc 0 timeEnd ↦
      canonicalAffineTimeL2WeightedActionRead
          a b test id contDiff_id (trial time) time.1 -
        time.1 * canonicalAffineTimeL2GreenRateRead
          a b test (trial time) time.1) =ᵐ[
      canonicalAffineTimeMeasure timeEnd]
      (fun time : Icc 0 timeEnd ↦
        canonicalAffineTimeL2MassRead a b test (trial time) time.1) :=
    Filter.Eventually.of_forall fun time ↦ by
      have read := canonicalAffineActionTestRieszL2_inner_eq
        a b test id contDiff_id time.1 (trial time)
      simpa [canonicalAffineTimeL2WeightedActionRead, id,
        canonicalAffineTimeL2MassRead,
        canonicalAffineTimeL2GreenRateRead] using congrArg
          (fun value ↦ value -
            time.1 * canonicalAffineTimeL2GreenRateRead
              a b test (trial time) time.1) read
  exact (integrable_congr readEq).mp differenceIntegrable

private theorem canonicalAffinePhysicalTimeL2GreenRate_integrable
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    Integrable (canonicalAffinePhysicalTimeL2GreenRate
      timeEnd timeNonnegative a b boxOrder test)
      (canonicalAffineTimeMeasure timeEnd) := by
  exact canonicalAffineTimeL2GreenRateRead_integrable
    timeEnd a b test
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder)

private theorem canonicalAffinePhysicalTimeL2MassRead_integrable
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    Integrable (canonicalAffinePhysicalTimeL2MassRead
      timeEnd timeNonnegative a b boxOrder test)
      (canonicalAffineTimeMeasure timeEnd) := by
  exact canonicalAffineTimeL2MassRead_integrable
    timeEnd a b test
      (canonicalAffinePhysicalTimeL2Output
        timeEnd timeNonnegative a b boxOrder)

theorem canonicalAffinePhysicalTimeL2GreenRate_intervalIntegrable
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    IntervalIntegrable (fun time ↦
      canonicalAffinePhysicalTimeL2GreenRate
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)) volume 0 timeEnd := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le timePositive.le).2
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  apply (canonicalAffinePhysicalTimeL2GreenRate_integrable
    timeEnd timePositive.le a b boxOrder test).congr
  exact Filter.Eventually.of_forall fun time ↦ by
    simp only [Function.comp_apply, projIcc_val]

theorem canonicalAffinePhysicalTimeL2MassRead_intervalIntegrable
    (timeEnd : ℝ)
    (timePositive : 0 < timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ) :
    IntervalIntegrable (fun time ↦
      canonicalAffinePhysicalTimeL2MassRead
        timeEnd timePositive.le a b boxOrder test
          (projIcc 0 timeEnd timePositive.le time)) volume 0 timeEnd := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le timePositive.le).2
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  apply (canonicalAffinePhysicalTimeL2MassRead_integrable
    timeEnd timePositive.le a b boxOrder test).congr
  exact Filter.Eventually.of_forall fun time ↦ by
    simp only [Function.comp_apply, projIcc_val]

/-- The weak Volterra equation retains the exact source initial mass at its
only open endpoint. -/
theorem canonicalAffinePhysicalTimeL2Output_weightedIntegralActionLaw_of_endZero
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightEndZero : weight timeEnd = 0) :
    (∫ time : Icc 0 timeEnd,
        weight time.1 *
            canonicalAffinePhysicalTimeL2GreenRate
              timeEnd timeNonnegative a b boxOrder test time +
          deriv weight time.1 *
            canonicalAffinePhysicalTimeL2MassRead
              timeEnd timeNonnegative a b boxOrder test time
        ∂canonicalAffineTimeMeasure timeEnd) =
      -weight 0 * canonicalSourceLiftMassRead a b test 0 := by
  have actionBoundary :=
    canonicalAffinePhysicalTimeL2Output_weightedActionLaw_of_endZero
    timeEnd timeNonnegative a b boxOrder test weight weightRegular
      weightEndZero
  have integralEq :=
    canonicalAffineActionTestTimeL2_inner_eq_weightedReadIntegral
      timeEnd a b test weight weightRegular
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder)
  have weightedReadEq : ∀ time : Icc 0 timeEnd,
      canonicalAffineTimeL2WeightedActionRead
          a b test weight weightRegular
          (canonicalAffinePhysicalTimeL2Output
            timeEnd timeNonnegative a b boxOrder time) time.1 =
        weight time.1 *
            canonicalAffinePhysicalTimeL2GreenRate
              timeEnd timeNonnegative a b boxOrder test time +
          deriv weight time.1 *
            canonicalAffinePhysicalTimeL2MassRead
              timeEnd timeNonnegative a b boxOrder test time := by
    intro time
    exact canonicalAffineActionTestRieszL2_inner_eq
      a b test weight weightRegular time.1
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time)
  have weightedIntegralBoundary := integralEq.symm.trans actionBoundary
  have weightedIntegralEq : (∫ time : Icc 0 timeEnd,
      canonicalAffineTimeL2WeightedActionRead
        a b test weight weightRegular
        (canonicalAffinePhysicalTimeL2Output
          timeEnd timeNonnegative a b boxOrder time) time.1
      ∂canonicalAffineTimeMeasure timeEnd) =
      ∫ time : Icc 0 timeEnd,
        weight time.1 *
            canonicalAffinePhysicalTimeL2GreenRate
              timeEnd timeNonnegative a b boxOrder test time +
          deriv weight time.1 *
            canonicalAffinePhysicalTimeL2MassRead
              timeEnd timeNonnegative a b boxOrder test time
        ∂canonicalAffineTimeMeasure timeEnd := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall weightedReadEq
  exact weightedIntegralEq.symm.trans weightedIntegralBoundary

/-- Compactly supported weights read the homogeneous weak Volterra action. -/
theorem canonicalAffinePhysicalTimeL2Output_weightedIntegralActionLaw
    (timeEnd : ℝ)
    (timeNonnegative : 0 ≤ timeEnd)
    (a b : DiracMatterSpatialCoordinates)
    (boxOrder : a ≤ b)
    (test : ℕ)
    (weight : ℝ → ℝ)
    (weightRegular : ContDiff ℝ 1 weight)
    (weightZero : weight 0 = 0)
    (weightEndZero : weight timeEnd = 0) :
    (∫ time : Icc 0 timeEnd,
        weight time.1 *
            canonicalAffinePhysicalTimeL2GreenRate
              timeEnd timeNonnegative a b boxOrder test time +
          deriv weight time.1 *
            canonicalAffinePhysicalTimeL2MassRead
              timeEnd timeNonnegative a b boxOrder test time
        ∂canonicalAffineTimeMeasure timeEnd) = 0 := by
  rw [canonicalAffinePhysicalTimeL2Output_weightedIntegralActionLaw_of_endZero
    timeEnd timeNonnegative a b boxOrder test weight weightRegular
      weightEndZero,
    weightZero]
  ring

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterCanonicalAffineTailEnergyActionLaw
