import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import H0mework.Physics.ElectricJoint.FixedOriginResidualTransport
import H0mework.Physics.FixedJoint.FixedJointP286RequiredExteriorProfileRegularity
import H0mework.Physics.Coframe.ScalarMomentumCoframeReadout

/-!
# Fixed P506/L0 live-electric scalar origin closure

The global scalar writer integrates the source/current-generated acceleration
profile twice.  This module verifies its fixed-occurrence diagonal second-jet
readout and closes the live-electric scalar residual without feeding any
residual coordinate back into the writer.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginScalarClosure

open ProofFreeRicherAnholonomicSource
open Asymptotics Filter MeasureTheory Set
open StageNineCanonicalCauchyState
open StageNineCoframeHolonomicRegularity
open StageNineCoframeLocalDifferentiability
open StageNineCoframeVariation
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeCompleteJointActionGeneratedProfiles
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionResponseOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeFixedP506CompleteJointP286RequiredExteriorProfileRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonGlobalRegularity
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginResidualTransport
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FullOccurrenceScalarAccelerationRegularity
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualFirstGerm
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionPrincipal
open StageNineDiracDualFormNativeRecenteredScalarSecondJetActionResponse
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeScalarSecondJetActionResponseOperator
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286HolonomicSecondJetCarrier
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarMomentumCoframeReadout
open StageNineScalarPointwiseEquation
open StageNineScalarVariation
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra

open scoped ContDiff Interval Matrix.Norms.Elementwise Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance liveScalarP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance liveScalarP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIndexFintype

local instance liveScalarP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

local instance liveScalarBasePointNormedAddCommGroup :
    NormedAddCommGroup BasePoint :=
  PiLp.normedAddCommGroup 2 (fun _ : LorentzianIndex => ℝ)

local instance liveScalarBasePointNormedSpace :
    NormedSpace ℝ BasePoint :=
  PiLp.normedSpace 2 ℝ (fun _ : LorentzianIndex => ℝ)

local instance liveScalarCoordinateNormedAddCommGroup :
    NormedAddCommGroup ScalarCoordinateCarrier :=
  PiLp.normedAddCommGroup 2 (fun _ : ScalarBasisIndex => ℂ)

local instance liveScalarCoordinateNormedSpace :
    NormedSpace ℝ ScalarCoordinateCarrier :=
  PiLp.normedSpace 2 ℝ (fun _ : ScalarBasisIndex => ℂ)

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev FixedScalarAcceleration : BasePoint → ScalarCoordinateCarrier :=
  completeJointScalarAccelerationProfile positiveSmoothUnifiedSource FixedInput

private abbrev FixedScalarSecondPrimitive :
    BasePoint → ScalarCoordinateCarrier :=
  canonicalTimeSecondPrimitive FixedScalarAcceleration

private abbrev FixedCanonicalActual : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev FixedAlgebraicActual : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

private abbrev FixedScalarBase : StageNineHolonomicConfiguration :=
  recenteredCartanRepairedConstitutiveCurrent 0

private theorem canonical_time_single
    (time : ℝ) :
    EuclideanSpace.single canonicalLorentzianTimeDirection time =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private def normalizedTimeSliceCLM
    (parameter : ℝ) : BasePoint →L[ℝ] BasePoint :=
  parameter •
      canonicalTimeProjection.smulRight
        (coordinateDirection canonicalLorentzianTimeDirection) +
    canonicalSpatialInclusion.comp canonicalSpatialProjection

private theorem normalizedTimeSliceCLM_apply
    (parameter : ℝ) (point : BasePoint) :
    normalizedTimeSliceCLM parameter point =
      canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point) := by
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion,
    canonical_time_single]
  simp only [normalizedTimeSliceCLM, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    smul_smul]
  rw [mul_comm parameter]

private def normalizedTimeSliceBound : ℝ :=
  ‖canonicalTimeProjection.smulRight
      (coordinateDirection canonicalLorentzianTimeDirection)‖ +
    ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ + 1

private theorem normalizedTimeSliceBound_pos :
    0 < normalizedTimeSliceBound := by
  unfold normalizedTimeSliceBound
  positivity

private theorem normalizedTimeSliceCLM_norm_lt_bound
    {parameter : ℝ} (parameterMem : parameter ∈ Icc (0 : ℝ) 1) :
    ‖normalizedTimeSliceCLM parameter‖ <
      normalizedTimeSliceBound := by
  unfold normalizedTimeSliceCLM normalizedTimeSliceBound
  calc
    ‖parameter •
          canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection) +
        canonicalSpatialInclusion.comp canonicalSpatialProjection‖
        ≤ ‖parameter •
            canonicalTimeProjection.smulRight
              (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ :=
      norm_add_le _ _
    _ = |parameter| *
          ‖canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖canonicalTimeProjection.smulRight
            (coordinateDirection canonicalLorentzianTimeDirection)‖ +
          ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ := by
      have parameterAbs : |parameter| ≤ 1 := by
        rw [abs_of_nonneg parameterMem.1]
        exact parameterMem.2
      exact add_le_add
        (mul_le_of_le_one_left
          (norm_nonneg
            (canonicalTimeProjection.smulRight
              (coordinateDirection canonicalLorentzianTimeDirection)))
          parameterAbs)
        le_rfl
    _ < _ := by linarith

private def FixedNormalizedSecondAverage
    (point : BasePoint) : ScalarCoordinateCarrier :=
  ∫ outerParameter in (0 : ℝ)..1,
    outerParameter •
      ∫ innerParameter in (0 : ℝ)..1,
        FixedScalarAcceleration
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter) point)

private def FixedInnerAverage
    (point : BasePoint) (outerParameter : ℝ) :
    ScalarCoordinateCarrier :=
  ∫ innerParameter in (0 : ℝ)..1,
    FixedScalarAcceleration
      (normalizedTimeSliceCLM
        (outerParameter * innerParameter) point)

private def FixedInnerAverageDerivative
    (point : BasePoint) (outerParameter : ℝ) :
    BasePoint →L[ℝ] ScalarCoordinateCarrier :=
  ∫ innerParameter in (0 : ℝ)..1,
    (fderiv ℝ FixedScalarAcceleration
        (normalizedTimeSliceCLM
          (outerParameter * innerParameter) point)).comp
      (normalizedTimeSliceCLM
        (outerParameter * innerParameter))

private def FixedNormalizedSecondAverageDerivative
    (point : BasePoint) :
    BasePoint →L[ℝ] ScalarCoordinateCarrier :=
  ∫ outerParameter in (0 : ℝ)..1,
    outerParameter •
      FixedInnerAverageDerivative point outerParameter

private theorem fixedNormalizedSecondAverage_eq_inner
    (point : BasePoint) :
    FixedNormalizedSecondAverage point =
      ∫ outerParameter in (0 : ℝ)..1,
        outerParameter • FixedInnerAverage point outerParameter :=
  rfl

private theorem fixedScalarSecondPrimitive_scaleIdentity
    (point : BasePoint) :
    FixedScalarSecondPrimitive point =
      canonicalTimeProjection point ^ 2 •
        FixedNormalizedSecondAverage point := by
  unfold FixedScalarSecondPrimitive canonicalTimeSecondPrimitive
    FixedNormalizedSecondAverage
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  let innerPrimitive : ℝ → ScalarCoordinateCarrier := fun outerTime =>
    ∫ innerTime in (0 : ℝ)..outerTime,
      FixedScalarAcceleration
        (canonicalCauchySlicePoint innerTime space)
  have outerScale :
      (∫ outerTime in (0 : ℝ)..time, innerPrimitive outerTime) =
        time • ∫ outerParameter in (0 : ℝ)..1,
          innerPrimitive (time * outerParameter) := by
    simpa only [mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := innerPrimitive) (a := (0 : ℝ)) (b := (1 : ℝ)) time).symm
  rw [outerScale]
  have innerScale (outerParameter : ℝ) :
      innerPrimitive (time * outerParameter) =
        (time * outerParameter) •
          ∫ innerParameter in (0 : ℝ)..1,
            FixedScalarAcceleration
              (canonicalCauchySlicePoint
                (time * outerParameter * innerParameter) space) := by
    simpa [innerPrimitive] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun innerTime =>
          FixedScalarAcceleration
            (canonicalCauchySlicePoint innerTime space))
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (time * outerParameter)).symm
  simp_rw [innerScale]
  rw [← intervalIntegral.integral_smul]
  simp only [time, space, pow_two]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro outerParameter _
  simp only [smul_smul, mul_assoc]
  apply congrArg₂ (· • ·)
  · ring
  · apply intervalIntegral.integral_congr
    intro innerParameter _
    change
      FixedScalarAcceleration
          (canonicalCauchySlicePoint
            (canonicalTimeProjection point *
              (outerParameter * innerParameter))
            (canonicalSpatialProjection point)) =
        FixedScalarAcceleration
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter) point)
    exact congrArg FixedScalarAcceleration
      (normalizedTimeSliceCLM_apply
        (outerParameter * innerParameter) point).symm

private theorem fixedScalarAcceleration_exists_local_c1_bounded :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ bound : ℝ, 0 < bound ∧
        ∀ point ∈ Metric.ball (0 : BasePoint) radius,
          ContDiffAt ℝ 1 FixedScalarAcceleration point ∧
            ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound := by
  have regular :
      ContDiffAt ℝ 1 FixedScalarAcceleration 0 :=
    fixedP506L0CompleteJointScalarAccelerationProfile_contDiffAt_origin.of_le
      (by simp)
  have regularEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        ContDiffAt ℝ 1 FixedScalarAcceleration point :=
    regular.eventually (by simp)
  let bound : ℝ := ‖fderiv ℝ FixedScalarAcceleration 0‖ + 1
  have boundPositive : 0 < bound := by
    dsimp [bound]
    positivity
  have derivativeBoundEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound := by
    have derivativeContinuous :
        ContinuousAt (fderiv ℝ FixedScalarAcceleration) 0 :=
      regular.continuousAt_fderiv (by norm_num)
    have normTends :
        Tendsto
          (fun point => ‖fderiv ℝ FixedScalarAcceleration point‖)
          (𝓝 (0 : BasePoint))
          (𝓝 ‖fderiv ℝ FixedScalarAcceleration 0‖) :=
      derivativeContinuous.norm
    have strictBound :
        ‖fderiv ℝ FixedScalarAcceleration 0‖ < bound := by
      dsimp [bound]
      linarith
    exact
      (normTends.eventually
        (Iio_mem_nhds strictBound)).mono fun _ valueLt => valueLt.le
  obtain ⟨radius, radiusPositive, ballProperty⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      (regularEventually.and derivativeBoundEventually)
  exact
    ⟨radius, radiusPositive, bound, boundPositive,
      fun point pointMem => ballProperty point pointMem⟩

private theorem normalizedTimeSlice_mem_ball
    {targetRadius : ℝ} (targetRadiusPositive : 0 < targetRadius)
    {point : BasePoint}
    (pointMem :
      point ∈ Metric.ball (0 : BasePoint)
        (targetRadius / normalizedTimeSliceBound))
    {parameter : ℝ} (parameterMem : parameter ∈ Icc (0 : ℝ) 1) :
    normalizedTimeSliceCLM parameter point ∈
      Metric.ball (0 : BasePoint) targetRadius := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at pointMem ⊢
  calc
    ‖normalizedTimeSliceCLM parameter point‖
        ≤ ‖normalizedTimeSliceCLM parameter‖ * ‖point‖ :=
      (normalizedTimeSliceCLM parameter).le_opNorm point
    _ ≤ normalizedTimeSliceBound * ‖point‖ :=
      mul_le_mul_of_nonneg_right
        (normalizedTimeSliceCLM_norm_lt_bound parameterMem).le
        (norm_nonneg _)
    _ < normalizedTimeSliceBound *
          (targetRadius / normalizedTimeSliceBound) :=
      mul_lt_mul_of_pos_left pointMem normalizedTimeSliceBound_pos
    _ = targetRadius := by
      field_simp [normalizedTimeSliceBound_pos.ne']

private theorem unitInterval_mul_mem
    {first second : ℝ}
    (firstMem : first ∈ Icc (0 : ℝ) 1)
    (secondMem : second ∈ Icc (0 : ℝ) 1) :
    first * second ∈ Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg firstMem.1 secondMem.1,
    mul_le_one₀ firstMem.2 secondMem.1 secondMem.2⟩

private theorem unitInterval_uIoc_subset_Icc :
    Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
  intro parameter parameterMem
  have actual := uIoc_subset_uIcc parameterMem
  simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual

private theorem fixedInnerAverage_hasFDerivAt
    {targetRadius bound : ℝ}
    (targetRadiusPositive : 0 < targetRadius)
    (boundNonnegative : 0 ≤ bound)
    (profileRegular :
      ∀ point ∈ Metric.ball (0 : BasePoint) targetRadius,
        ContDiffAt ℝ 1 FixedScalarAcceleration point ∧
          ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound)
    {point : BasePoint}
    (pointMem :
      point ∈ Metric.ball (0 : BasePoint)
        (targetRadius / normalizedTimeSliceBound))
    {outerParameter : ℝ}
    (outerMem : outerParameter ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt
      (fun candidate => FixedInnerAverage candidate outerParameter)
      (FixedInnerAverageDerivative point outerParameter)
      point := by
  let domain : Set BasePoint :=
    Metric.ball (0 : BasePoint)
      (targetRadius / normalizedTimeSliceBound)
  have domainOpen : IsOpen domain := Metric.isOpen_ball
  have profileContinuousOn :
      ContinuousOn FixedScalarAcceleration
        (Metric.ball (0 : BasePoint) targetRadius) := by
    intro candidate candidateMem
    exact (profileRegular candidate candidateMem).1.continuousAt
      |>.continuousWithinAt
  have profileDerivativeContinuousOn :
      ContinuousOn (fderiv ℝ FixedScalarAcceleration)
        (Metric.ball (0 : BasePoint) targetRadius) := by
    intro candidate candidateMem
    exact (profileRegular candidate candidateMem).1.continuousAt_fderiv
      (by norm_num) |>.continuousWithinAt
  unfold FixedInnerAverage FixedInnerAverageDerivative
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := domain)
    (F := fun candidate innerParameter =>
      FixedScalarAcceleration
        (normalizedTimeSliceCLM
          (outerParameter * innerParameter) candidate))
    (F' := fun candidate innerParameter =>
      (fderiv ℝ FixedScalarAcceleration
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter) candidate)).comp
        (normalizedTimeSliceCLM
          (outerParameter * innerParameter)))
    (x₀ := point) (a := (0 : ℝ)) (b := (1 : ℝ))
    (μ := MeasureTheory.volume)
    (bound := fun _ => bound * normalizedTimeSliceBound)
  · exact domainOpen.mem_nhds pointMem
  · filter_upwards [domainOpen.mem_nhds pointMem] with candidate candidateMem
    have pathContinuous :
        Continuous fun innerParameter =>
          normalizedTimeSliceCLM
            (outerParameter * innerParameter) candidate := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have integrandContinuous :
        ContinuousOn
          (fun innerParameter =>
            FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (outerParameter * innerParameter) candidate))
          (Icc (0 : ℝ) 1) := by
      apply profileContinuousOn.comp pathContinuous.continuousOn
      intro innerParameter innerMem
      exact normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem
        (unitInterval_mul_mem outerMem innerMem)
    exact
      (integrandContinuous.mono unitInterval_uIoc_subset_Icc
        ).aestronglyMeasurable measurableSet_uIoc
  · have pathContinuous :
        Continuous fun innerParameter =>
          normalizedTimeSliceCLM
            (outerParameter * innerParameter) point := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have integrandContinuous :
        ContinuousOn
          (fun innerParameter =>
            FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (outerParameter * innerParameter) point))
          (Icc (0 : ℝ) 1) := by
      apply profileContinuousOn.comp pathContinuous.continuousOn
      intro innerParameter innerMem
      exact normalizedTimeSlice_mem_ball targetRadiusPositive pointMem
        (unitInterval_mul_mem outerMem innerMem)
    exact integrandContinuous.intervalIntegrable_of_Icc (by norm_num)
  · have pointPathContinuous :
        Continuous fun innerParameter =>
          normalizedTimeSliceCLM
            (outerParameter * innerParameter) point := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have operatorPathContinuous :
        Continuous fun innerParameter =>
          normalizedTimeSliceCLM
            (outerParameter * innerParameter) := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have derivativeContinuous :
        ContinuousOn
          (fun innerParameter =>
            fderiv ℝ FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (outerParameter * innerParameter) point))
          (Icc (0 : ℝ) 1) := by
      apply profileDerivativeContinuousOn.comp
        pointPathContinuous.continuousOn
      intro innerParameter innerMem
      exact normalizedTimeSlice_mem_ball targetRadiusPositive pointMem
        (unitInterval_mul_mem outerMem innerMem)
    exact
      ((derivativeContinuous.clm_comp operatorPathContinuous.continuousOn
        ).mono unitInterval_uIoc_subset_Icc).aestronglyMeasurable
          measurableSet_uIoc
  · filter_upwards [] with innerParameter innerMem candidate candidateMem
    have innerMem' : innerParameter ∈ Icc (0 : ℝ) 1 :=
      unitInterval_uIoc_subset_Icc innerMem
    have productMem :=
      unitInterval_mul_mem outerMem innerMem'
    have mappedMem :=
      normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem productMem
    calc
      ‖(fderiv ℝ FixedScalarAcceleration
            (normalizedTimeSliceCLM
              (outerParameter * innerParameter) candidate)).comp
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter))‖
          ≤ ‖fderiv ℝ FixedScalarAcceleration
                (normalizedTimeSliceCLM
                  (outerParameter * innerParameter) candidate)‖ *
              ‖normalizedTimeSliceCLM
                (outerParameter * innerParameter)‖ :=
        (fderiv ℝ FixedScalarAcceleration
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter) candidate)).opNorm_comp_le _
      _ ≤ bound * normalizedTimeSliceBound := by
        exact mul_le_mul
          (profileRegular _ mappedMem).2
          (normalizedTimeSliceCLM_norm_lt_bound productMem).le
          (norm_nonneg _) boundNonnegative
  · exact intervalIntegrable_const
  · filter_upwards [] with innerParameter innerMem candidate candidateMem
    have innerMem' : innerParameter ∈ Icc (0 : ℝ) 1 :=
      unitInterval_uIoc_subset_Icc innerMem
    have productMem :=
      unitInterval_mul_mem outerMem innerMem'
    have mappedMem :=
      normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem productMem
    exact
      ((profileRegular _ mappedMem).1.differentiableAt (by norm_num)
        ).hasFDerivAt.comp candidate
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter)).hasFDerivAt

private theorem fixedInnerAverageDerivative_norm_le
    {targetRadius bound : ℝ}
    (targetRadiusPositive : 0 < targetRadius)
    (boundNonnegative : 0 ≤ bound)
    (profileRegular :
      ∀ point ∈ Metric.ball (0 : BasePoint) targetRadius,
        ContDiffAt ℝ 1 FixedScalarAcceleration point ∧
          ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound)
    {candidate : BasePoint}
    (candidateMem :
      candidate ∈ Metric.ball (0 : BasePoint)
        (targetRadius / normalizedTimeSliceBound))
    {outerParameter : ℝ}
    (outerMem : outerParameter ∈ Icc (0 : ℝ) 1) :
    ‖FixedInnerAverageDerivative candidate outerParameter‖ ≤
      bound * normalizedTimeSliceBound := by
  unfold FixedInnerAverageDerivative
  have estimate :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun innerParameter =>
        (fderiv ℝ FixedScalarAcceleration
            (normalizedTimeSliceCLM
              (outerParameter * innerParameter) candidate)).comp
          (normalizedTimeSliceCLM
            (outerParameter * innerParameter)))
      (C := bound * normalizedTimeSliceBound)
      (fun innerParameter innerMem => by
        have innerMem' := unitInterval_uIoc_subset_Icc innerMem
        have productMem := unitInterval_mul_mem outerMem innerMem'
        have mappedMem :=
          normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem
            productMem
        exact
          (fderiv ℝ FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (outerParameter * innerParameter) candidate)
            ).opNorm_comp_le _
            |>.trans
              (mul_le_mul
                (profileRegular _ mappedMem).2
                (normalizedTimeSliceCLM_norm_lt_bound productMem).le
                (norm_nonneg _) boundNonnegative))
  simpa using estimate

private theorem intervalIntegral_right_continuousOn_of_joint_continuousOn
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {joint : ℝ × ℝ → E}
    (jointContinuous :
      ContinuousOn joint
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :
    ContinuousOn
      (fun outerParameter =>
        ∫ innerParameter in (0 : ℝ)..1,
          joint (outerParameter, innerParameter))
      (Icc (0 : ℝ) 1) := by
  obtain ⟨bound, boundProperty⟩ :
      ∃ bound : ℝ,
        ∀ parameters ∈
            (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
          ‖joint parameters‖ ≤ bound :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      jointContinuous
  intro outerParameter outerMem
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
  · filter_upwards [self_mem_nhdsWithin] with candidate candidateMem
    have sectionContinuous :
        ContinuousOn
          (fun innerParameter => joint (candidate, innerParameter))
          (Icc (0 : ℝ) 1) := by
      apply jointContinuous.comp
        ((continuous_const.prodMk continuous_id).continuousOn)
      intro innerParameter innerMem
      exact ⟨candidateMem, innerMem⟩
    exact
      (sectionContinuous.mono unitInterval_uIoc_subset_Icc
        ).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with candidate candidateMem
    filter_upwards [] with innerParameter innerMem
    exact boundProperty (candidate, innerParameter)
      ⟨candidateMem, unitInterval_uIoc_subset_Icc innerMem⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with innerParameter innerMem
    have innerMem' := unitInterval_uIoc_subset_Icc innerMem
    have pairContinuous :
        ContinuousWithinAt
          (fun candidate : ℝ => (candidate, innerParameter))
          (Icc (0 : ℝ) 1) outerParameter :=
      (continuousAt_id.prodMk
        (continuousAt_const : ContinuousAt
          (fun _ : ℝ => innerParameter) outerParameter)).continuousWithinAt
    have composed :=
      ContinuousWithinAt.comp
        (f := fun candidate : ℝ => (candidate, innerParameter))
        (g := joint)
        (s := Icc (0 : ℝ) 1)
        (t := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
        (jointContinuous (outerParameter, innerParameter)
          ⟨outerMem, innerMem'⟩)
        pairContinuous
        (fun candidate candidateMem => ⟨candidateMem, innerMem'⟩)
    simpa [Function.comp_def] using composed

private theorem fixedNormalizedSecondAverage_hasFDerivAt
    {targetRadius bound : ℝ}
    (targetRadiusPositive : 0 < targetRadius)
    (boundNonnegative : 0 ≤ bound)
    (profileRegular :
      ∀ point ∈ Metric.ball (0 : BasePoint) targetRadius,
        ContDiffAt ℝ 1 FixedScalarAcceleration point ∧
          ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound)
    {point : BasePoint}
    (pointMem :
      point ∈ Metric.ball (0 : BasePoint)
        (targetRadius / normalizedTimeSliceBound)) :
    HasFDerivAt FixedNormalizedSecondAverage
      (FixedNormalizedSecondAverageDerivative point) point := by
  let domain : Set BasePoint :=
    Metric.ball (0 : BasePoint)
      (targetRadius / normalizedTimeSliceBound)
  have domainOpen : IsOpen domain := Metric.isOpen_ball
  have profileContinuousOn :
      ContinuousOn FixedScalarAcceleration
        (Metric.ball (0 : BasePoint) targetRadius) := by
    intro candidate candidateMem
    exact (profileRegular candidate candidateMem).1.continuousAt
      |>.continuousWithinAt
  have profileDerivativeContinuousOn :
      ContinuousOn (fderiv ℝ FixedScalarAcceleration)
        (Metric.ball (0 : BasePoint) targetRadius) := by
    intro candidate candidateMem
    exact (profileRegular candidate candidateMem).1.continuousAt_fderiv
      (by norm_num) |>.continuousWithinAt
  have profileJointContinuous
      {candidate : BasePoint} (candidateMem : candidate ∈ domain) :
      ContinuousOn
        (fun parameters : ℝ × ℝ =>
          FixedScalarAcceleration
            (normalizedTimeSliceCLM
              (parameters.1 * parameters.2) candidate))
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    apply profileContinuousOn.comp
      (by
        unfold normalizedTimeSliceCLM
        fun_prop : Continuous
          (fun parameters : ℝ × ℝ =>
            normalizedTimeSliceCLM
              (parameters.1 * parameters.2) candidate)).continuousOn
    intro parameters parametersMem
    exact normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem
      (unitInterval_mul_mem parametersMem.1 parametersMem.2)
  have derivativeJointContinuous
      {candidate : BasePoint} (candidateMem : candidate ∈ domain) :
      ContinuousOn
        (fun parameters : ℝ × ℝ =>
          (fderiv ℝ FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (parameters.1 * parameters.2) candidate)).comp
            (normalizedTimeSliceCLM
              (parameters.1 * parameters.2)))
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    have pointPath :
        Continuous fun parameters : ℝ × ℝ =>
          normalizedTimeSliceCLM
            (parameters.1 * parameters.2) candidate := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have operatorPath :
        Continuous fun parameters : ℝ × ℝ =>
          normalizedTimeSliceCLM
            (parameters.1 * parameters.2) := by
      unfold normalizedTimeSliceCLM
      fun_prop
    have first :
        ContinuousOn
          (fun parameters : ℝ × ℝ =>
            fderiv ℝ FixedScalarAcceleration
              (normalizedTimeSliceCLM
                (parameters.1 * parameters.2) candidate))
          (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
      apply profileDerivativeContinuousOn.comp pointPath.continuousOn
      intro parameters parametersMem
      exact normalizedTimeSlice_mem_ball targetRadiusPositive candidateMem
        (unitInterval_mul_mem parametersMem.1 parametersMem.2)
    exact first.clm_comp operatorPath.continuousOn
  have innerContinuous
      {candidate : BasePoint} (candidateMem : candidate ∈ domain) :
      ContinuousOn (FixedInnerAverage candidate) (Icc (0 : ℝ) 1) := by
    exact
      intervalIntegral_right_continuousOn_of_joint_continuousOn
        (E := ScalarCoordinateCarrier)
        (profileJointContinuous candidateMem)
  have innerDerivativeContinuous
      {candidate : BasePoint} (candidateMem : candidate ∈ domain) :
      ContinuousOn (FixedInnerAverageDerivative candidate)
        (Icc (0 : ℝ) 1) := by
    exact
      intervalIntegral_right_continuousOn_of_joint_continuousOn
        (E := BasePoint →L[ℝ] ScalarCoordinateCarrier)
        (derivativeJointContinuous candidateMem)
  unfold FixedNormalizedSecondAverage FixedNormalizedSecondAverageDerivative
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := domain)
    (F := fun candidate outerParameter =>
      outerParameter • FixedInnerAverage candidate outerParameter)
    (F' := fun candidate outerParameter =>
      outerParameter • FixedInnerAverageDerivative candidate outerParameter)
    (x₀ := point) (a := (0 : ℝ)) (b := (1 : ℝ))
    (μ := MeasureTheory.volume)
    (bound := fun _ => bound * normalizedTimeSliceBound)
  · exact domainOpen.mem_nhds pointMem
  · filter_upwards [domainOpen.mem_nhds pointMem] with candidate candidateMem
    exact
      ((continuousOn_id.smul (innerContinuous candidateMem)
        ).mono unitInterval_uIoc_subset_Icc
        ).aestronglyMeasurable measurableSet_uIoc
  · exact
      (continuousOn_id.smul (innerContinuous pointMem)
        ).intervalIntegrable_of_Icc (by norm_num)
  · exact
      ((continuousOn_id.smul (innerDerivativeContinuous pointMem)
        ).mono unitInterval_uIoc_subset_Icc
        ).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [] with outerParameter outerMem candidate candidateMem
    have outerMem' := unitInterval_uIoc_subset_Icc outerMem
    calc
      ‖outerParameter • FixedInnerAverageDerivative candidate outerParameter‖
          = |outerParameter| *
              ‖FixedInnerAverageDerivative candidate outerParameter‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (bound * normalizedTimeSliceBound) := by
        apply mul_le_mul
        · simpa [abs_of_nonneg outerMem'.1] using outerMem'.2
        · exact
            fixedInnerAverageDerivative_norm_le targetRadiusPositive
              boundNonnegative profileRegular candidateMem outerMem'
        · exact norm_nonneg _
        · norm_num
      _ = bound * normalizedTimeSliceBound := one_mul _
  · exact intervalIntegrable_const
  · filter_upwards [] with outerParameter outerMem candidate candidateMem
    exact
      (fixedInnerAverage_hasFDerivAt targetRadiusPositive boundNonnegative
        profileRegular candidateMem
        (unitInterval_uIoc_subset_Icc outerMem)).const_smul outerParameter

private theorem fixedNormalizedSecondAverageDerivative_norm_le
    {targetRadius bound : ℝ}
    (targetRadiusPositive : 0 < targetRadius)
    (boundNonnegative : 0 ≤ bound)
    (profileRegular :
      ∀ point ∈ Metric.ball (0 : BasePoint) targetRadius,
        ContDiffAt ℝ 1 FixedScalarAcceleration point ∧
          ‖fderiv ℝ FixedScalarAcceleration point‖ ≤ bound)
    {point : BasePoint}
    (pointMem :
      point ∈ Metric.ball (0 : BasePoint)
        (targetRadius / normalizedTimeSliceBound)) :
    ‖FixedNormalizedSecondAverageDerivative point‖ ≤
      bound * normalizedTimeSliceBound := by
  unfold FixedNormalizedSecondAverageDerivative
  have estimate :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun outerParameter =>
        outerParameter •
          FixedInnerAverageDerivative point outerParameter)
      (C := bound * normalizedTimeSliceBound)
      (fun outerParameter outerMem => by
        have outerMem' := unitInterval_uIoc_subset_Icc outerMem
        calc
          ‖outerParameter •
              FixedInnerAverageDerivative point outerParameter‖
              = |outerParameter| *
                  ‖FixedInnerAverageDerivative point outerParameter‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * (bound * normalizedTimeSliceBound) := by
            apply mul_le_mul
            · simpa [abs_of_nonneg outerMem'.1] using outerMem'.2
            · exact
                fixedInnerAverageDerivative_norm_le targetRadiusPositive
                  boundNonnegative profileRegular pointMem outerMem'
            · exact norm_nonneg _
            · norm_num
          _ = bound * normalizedTimeSliceBound := one_mul _)
  simpa using estimate

private theorem
    fixedNormalizedSecondAverage_exists_local_fderiv_bounded :
    ∃ radius : ℝ, 0 < radius ∧
      ∃ bound : ℝ, 0 < bound ∧
        ∀ point ∈ Metric.ball (0 : BasePoint) radius,
          HasFDerivAt FixedNormalizedSecondAverage
              (FixedNormalizedSecondAverageDerivative point) point ∧
            ‖FixedNormalizedSecondAverageDerivative point‖ ≤ bound := by
  obtain ⟨targetRadius, targetRadiusPositive, profileBound,
      profileBoundPositive, profileRegular⟩ :=
    fixedScalarAcceleration_exists_local_c1_bounded
  let radius := targetRadius / normalizedTimeSliceBound
  have radiusPositive : 0 < radius :=
    div_pos targetRadiusPositive normalizedTimeSliceBound_pos
  let derivativeBound :=
    profileBound * normalizedTimeSliceBound
  have derivativeBoundPositive : 0 < derivativeBound :=
    mul_pos profileBoundPositive normalizedTimeSliceBound_pos
  exact
    ⟨radius, radiusPositive, derivativeBound, derivativeBoundPositive,
      fun point pointMem =>
        ⟨fixedNormalizedSecondAverage_hasFDerivAt targetRadiusPositive
            profileBoundPositive.le profileRegular pointMem,
          fixedNormalizedSecondAverageDerivative_norm_le
            targetRadiusPositive profileBoundPositive.le profileRegular
            pointMem⟩⟩

private theorem fixedNormalizedSecondAverage_zero :
    FixedNormalizedSecondAverage 0 =
      (2 : ℝ)⁻¹ • FixedScalarAcceleration 0 := by
  unfold FixedNormalizedSecondAverage normalizedTimeSliceCLM
  simp only [map_zero]
  rw [intervalIntegral.integral_const]
  simp only [one_smul, sub_zero]
  rw [intervalIntegral.integral_smul_const]
  norm_num

private def FixedScalarSecondPrimitiveFDeriv
    (point : BasePoint) :
    BasePoint →L[ℝ] ScalarCoordinateCarrier :=
  canonicalTimeProjection point ^ 2 •
      FixedNormalizedSecondAverageDerivative point +
    ((2 • canonicalTimeProjection point ^ (2 - 1)) •
        canonicalTimeProjection).smulRight
      (FixedNormalizedSecondAverage point)

private def FixedScalarSecondPrimitiveSecondDerivative :
    BasePoint →L[ℝ]
      (BasePoint →L[ℝ] ScalarCoordinateCarrier) :=
  canonicalTimeProjection.smulRight
    (canonicalTimeProjection.smulRight
      (FixedScalarAcceleration 0))

private theorem fixedScalarSecondPrimitive_fderiv_eq
    {point : BasePoint}
    (averageDerivative :
      HasFDerivAt FixedNormalizedSecondAverage
        (FixedNormalizedSecondAverageDerivative point) point) :
    fderiv ℝ FixedScalarSecondPrimitive point =
      FixedScalarSecondPrimitiveFDeriv point := by
  have primitiveEq :
      FixedScalarSecondPrimitive =
        fun candidate =>
          canonicalTimeProjection candidate ^ 2 •
            FixedNormalizedSecondAverage candidate := by
    funext candidate
    exact fixedScalarSecondPrimitive_scaleIdentity candidate
  rw [primitiveEq]
  exact
    ((canonicalTimeProjection.hasFDerivAt.pow 2).smul
      averageDerivative).fderiv

private theorem fixedScalarSecondPrimitiveFDeriv_sub_secondDerivative
    (point : BasePoint) :
    FixedScalarSecondPrimitiveFDeriv point -
        FixedScalarSecondPrimitiveSecondDerivative point =
      canonicalTimeProjection point ^ 2 •
          FixedNormalizedSecondAverageDerivative point +
        (2 * canonicalTimeProjection point) •
          canonicalTimeProjection.smulRight
            (FixedNormalizedSecondAverage point -
              FixedNormalizedSecondAverage 0) := by
  unfold FixedScalarSecondPrimitiveFDeriv
    FixedScalarSecondPrimitiveSecondDerivative
  rw [fixedNormalizedSecondAverage_zero]
  ext direction
  simp only [sub_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply,
    Nat.reduceSub, pow_one]
  norm_num [smul_sub, smul_smul]
  ring

private theorem
    fixedScalarSecondPrimitive_hasFDerivAt_fderiv_origin :
    HasFDerivAt
      (fderiv ℝ FixedScalarSecondPrimitive)
      FixedScalarSecondPrimitiveSecondDerivative
      0 := by
  obtain ⟨radius, radiusPositive, bound, boundPositive, localDerivative⟩ :=
    fixedNormalizedSecondAverage_exists_local_fderiv_bounded
  have zeroMem :
      (0 : BasePoint) ∈ Metric.ball (0 : BasePoint) radius :=
    Metric.mem_ball_self radiusPositive
  have averageDerivativeZero :=
    (localDerivative 0 zeroMem).1
  have averageContinuous :
      ContinuousAt FixedNormalizedSecondAverage 0 :=
    averageDerivativeZero.continuousAt
  have localEventually :
      ∀ᶠ point in 𝓝 (0 : BasePoint),
        HasFDerivAt FixedNormalizedSecondAverage
            (FixedNormalizedSecondAverageDerivative point) point ∧
          ‖FixedNormalizedSecondAverageDerivative point‖ ≤ bound :=
    by
      filter_upwards [Metric.ball_mem_nhds
        (0 : BasePoint) radiusPositive] with point pointMem
      exact localDerivative point pointMem
  have fderivEventually :
      fderiv ℝ FixedScalarSecondPrimitive =ᶠ[𝓝 (0 : BasePoint)]
        FixedScalarSecondPrimitiveFDeriv :=
    localEventually.mono fun point pointProperty =>
      fixedScalarSecondPrimitive_fderiv_eq pointProperty.1
  have linearBound :
      (fun point : BasePoint => canonicalTimeProjection point) =O[𝓝 0]
        (fun point : BasePoint => ‖point‖) :=
    (canonicalTimeProjection.isBigO_id (𝓝 0)).norm_right
  have linearLittleOne :
      (fun point : BasePoint => canonicalTimeProjection point) =o[𝓝 0]
        (fun _ : BasePoint => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    change Tendsto
      (fun point : BasePoint => canonicalTimeProjection point)
      (𝓝 0) (𝓝 (0 : ℝ))
    have generated :
        ContinuousAt
          (fun point : BasePoint => canonicalTimeProjection point) 0 :=
      canonicalTimeProjection.continuous.continuousAt
    change Tendsto
      (fun point : BasePoint => canonicalTimeProjection point)
      (𝓝 0) (𝓝 (canonicalTimeProjection (0 : BasePoint))) at generated
    rw [map_zero] at generated
    exact generated
  have squareLittle :
      (fun point : BasePoint => canonicalTimeProjection point ^ 2) =o[𝓝 0]
        (fun point : BasePoint => ‖point‖) := by
    simpa [pow_two] using linearBound.mul_isLittleO linearLittleOne
  have averageDerivativeNormBound :
      (fun point : BasePoint =>
        ‖FixedNormalizedSecondAverageDerivative point‖) =O[𝓝 0]
        (fun _ : BasePoint => (1 : ℝ)) := by
    apply IsBigO.of_bound bound
    filter_upwards [localEventually] with point pointProperty
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      pointProperty.2
  have quadraticTermNormLittle :
      (fun point : BasePoint =>
        ‖canonicalTimeProjection point ^ 2 •
          FixedNormalizedSecondAverageDerivative point‖) =o[𝓝 0]
        (fun point : BasePoint => ‖point‖) := by
    have generated :=
      squareLittle.mul_isBigO averageDerivativeNormBound
    simpa [norm_smul, Real.norm_eq_abs, abs_sq] using generated
  have quadraticTermLittle :
      (fun point : BasePoint =>
        canonicalTimeProjection point ^ 2 •
          FixedNormalizedSecondAverageDerivative point) =o[𝓝 0]
        (fun point : BasePoint => point) :=
    quadraticTermNormLittle.of_norm_left.of_norm_right
  have averageRemainderLittleOne :
      (fun point : BasePoint =>
        canonicalTimeProjection.smulRight
          (FixedNormalizedSecondAverage point -
            FixedNormalizedSecondAverage 0)) =o[𝓝 0]
        (fun _ : BasePoint => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    let lift :
        ScalarCoordinateCarrier →L[ℝ]
          (BasePoint →L[ℝ] ScalarCoordinateCarrier) :=
      ContinuousLinearMap.smulRightL ℝ BasePoint
        ScalarCoordinateCarrier canonicalTimeProjection
    have liftedContinuous :
        ContinuousAt
          (fun point : BasePoint =>
            lift
              (FixedNormalizedSecondAverage point -
                FixedNormalizedSecondAverage 0))
          0 := by
      exact lift.continuous.continuousAt.comp
        (averageContinuous.sub continuousAt_const)
    change Tendsto
      (fun point : BasePoint =>
        canonicalTimeProjection.smulRight
          (FixedNormalizedSecondAverage point -
            FixedNormalizedSecondAverage 0))
      (𝓝 0)
      (𝓝 (canonicalTimeProjection.smulRight
        (FixedNormalizedSecondAverage 0 -
          FixedNormalizedSecondAverage 0))) at liftedContinuous
    simp only [sub_self, ContinuousLinearMap.smulRight_zero] at liftedContinuous
    change Tendsto
      (fun point : BasePoint =>
        canonicalTimeProjection.smulRight
          (FixedNormalizedSecondAverage point -
            FixedNormalizedSecondAverage 0))
      (𝓝 0) (𝓝 0)
    exact liftedContinuous
  have doubledLinearBound :
      (fun point : BasePoint =>
        2 * canonicalTimeProjection point) =O[𝓝 0]
        (fun point : BasePoint => ‖point‖) :=
    linearBound.const_mul_left 2
  have linearRemainderLittle :
      (fun point : BasePoint =>
        (2 * canonicalTimeProjection point) •
          canonicalTimeProjection.smulRight
            (FixedNormalizedSecondAverage point -
              FixedNormalizedSecondAverage 0)) =o[𝓝 0]
        (fun point : BasePoint => point) := by
    have generated :=
      doubledLinearBound.smul_isLittleO averageRemainderLittleOne
    have normRight :
        (fun point : BasePoint =>
          (2 * canonicalTimeProjection point) •
            canonicalTimeProjection.smulRight
              (FixedNormalizedSecondAverage point -
                FixedNormalizedSecondAverage 0)) =o[𝓝 0]
          (fun point : BasePoint => ‖point‖) := by
      simpa [smul_eq_mul] using generated
    exact normRight.of_norm_right
  have explicitRemainder :
      (fun point : BasePoint =>
        FixedScalarSecondPrimitiveFDeriv point -
          FixedScalarSecondPrimitiveSecondDerivative point) =o[𝓝 0]
        (fun point : BasePoint => point) := by
    apply (quadraticTermLittle.add linearRemainderLittle).congr_left
    intro point
    exact
      (fixedScalarSecondPrimitiveFDeriv_sub_secondDerivative point).symm
  have actualRemainder :
      (fun point : BasePoint =>
        fderiv ℝ FixedScalarSecondPrimitive point -
          FixedScalarSecondPrimitiveSecondDerivative point) =o[𝓝 0]
        (fun point : BasePoint => point) := by
    apply explicitRemainder.congr' _ (EventuallyEq.rfl)
    exact fderivEventually.mono fun point equality => by
      exact congrArg
        (fun derivative =>
          derivative - FixedScalarSecondPrimitiveSecondDerivative point)
        equality.symm
  have fderivZero :
      fderiv ℝ FixedScalarSecondPrimitive 0 =
        (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier) := by
    exact
      fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin.fderiv
  apply HasFDerivAt.of_isLittleO
  simpa [fderivZero] using actualRemainder

private theorem canonicalTimeProjection_coordinateDirection_local
    (direction : LorentzianIndex) :
    canonicalTimeProjection (coordinateDirection direction) =
      if direction = canonicalLorentzianTimeDirection then 1 else 0 := by
  fin_cases direction <;>
    simp [canonicalTimeProjection, coordinateDirection,
      canonicalLorentzianTimeDirection]

private theorem
    fixedScalarSecondPrimitive_diagonalSecondDerivative_origin
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun point =>
          fieldDirectionalDerivative FixedScalarSecondPrimitive
            point direction)
        0 direction =
      if direction = canonicalLorentzianTimeDirection then
        FixedScalarAcceleration 0
      else 0 := by
  let evaluate :
      (BasePoint →L[ℝ] ScalarCoordinateCarrier) →L[ℝ]
        ScalarCoordinateCarrier :=
    ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
      (coordinateDirection direction)
  have evaluatedDerivative :
      HasFDerivAt
        (fun point =>
          evaluate (fderiv ℝ FixedScalarSecondPrimitive point))
        (evaluate.comp FixedScalarSecondPrimitiveSecondDerivative)
        0 :=
    evaluate.hasFDerivAt.comp 0
      fixedScalarSecondPrimitive_hasFDerivAt_fderiv_origin
  unfold fieldDirectionalDerivative
  change
    (fderiv ℝ
      (fun point =>
        evaluate (fderiv ℝ FixedScalarSecondPrimitive point)) 0)
        (coordinateDirection direction) =
      _
  rw [evaluatedDerivative.fderiv]
  unfold evaluate FixedScalarSecondPrimitiveSecondDerivative
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [canonicalTimeProjection_coordinateDirection_local]
  split_ifs <;>
    simp_all [canonicalTimeProjection_coordinateDirection_local]

private theorem fixedScalarAcceleration_origin_eq_recentered :
    FixedScalarAcceleration 0 =
      recenteredContactDiracDualScalarAcceleration 0 := by
  unfold FixedScalarAcceleration completeJointScalarAccelerationProfile
  rw [sourceActionGeneratedDiracDualCompleteJointProfiles_scalarAcceleration]
  have restartEq :
      completeJointGeneratedProfileRestartCurrent positiveSmoothUnifiedSource
          FixedInput 0 =
        fixedP506L0CartanRestartActual 0 := by
    unfold completeJointGeneratedProfileRestartCurrent
      fixedP506L0CartanRestartActual fixedP506L0RecenteredInput
    rw [fullyRecenterHolonomicConfiguration_zero,
      spatiallyRecenterHolonomicConfiguration_zero]
  change
    genericDiracDualScalarGeneratedAcceleration positiveSmoothUnifiedSource
        (completeJointRepairedConstitutiveCurrent positiveSmoothUnifiedSource
          (completeJointGeneratedProfileRestartCurrent
            positiveSmoothUnifiedSource FixedInput 0)) =
      recenteredContactDiracDualScalarAcceleration 0
  rw [restartEq]
  unfold completeJointRepairedConstitutiveCurrent
  rw [← recenteredCartanRepairedConstitutiveCurrent_eq_repairedCartan]
  have coordinateEq :
      genericDiracDualScalarTemporalDemandCoordinate
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent 0) =
        scalarActionRealDual
          (recenteredContactDiracDualScalarTemporalDemandDual 0) := by
    rfl
  have dualEq :
      genericDiracDualScalarTemporalDemandDual
          positiveSmoothUnifiedSource
          (recenteredCartanRepairedConstitutiveCurrent 0) =
        recenteredContactDiracDualScalarTemporalDemandDual 0 := by
    apply LinearMap.ext
    intro direction
    change
      scalarCoordinatePairingRe direction
          (genericDiracDualScalarTemporalDemandCoordinate
            positiveSmoothUnifiedSource
            (recenteredCartanRepairedConstitutiveCurrent 0)) =
        recenteredContactDiracDualScalarTemporalDemandDual 0 direction
    rw [coordinateEq, scalarCoordinatePairingRe_actionRealDual]
  unfold genericDiracDualScalarGeneratedAcceleration
    recenteredContactDiracDualScalarAcceleration
  rw [dualEq]

private theorem existing_coframe_eq_canonical :
    ExistingActual.coframe = FixedCanonicalActual.coframe := by
  calc
    ExistingActual.coframe = FixedAlgebraicActual.coframe := rfl
    _ = FixedCanonicalActual.coframe :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_coframe_eq_canonical

private theorem existing_gaugeConnection_eq_canonical :
    ExistingActual.gaugeConnection =
      FixedCanonicalActual.gaugeConnection := by
  calc
    ExistingActual.gaugeConnection =
        FixedAlgebraicActual.gaugeConnection := rfl
    _ = FixedCanonicalActual.gaugeConnection :=
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_gaugeConnection_eq_canonical

private theorem existing_scalar_normalForm :
    ExistingActual.scalar =
      fun point =>
        FixedInput.scalar point + FixedScalarSecondPrimitive point := by
  rfl

private theorem fixedScalarBase_scalar_eq_input :
    FixedScalarBase.scalar = FixedInput.scalar := by
  unfold FixedScalarBase recenteredCartanRepairedConstitutiveCurrent
  rw [diracDualFormNativeRepairedConstitutiveWrittenCurrent_scalar,
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_scalar,
    spatiallyRecenterHolonomicConfiguration_zero]

private theorem canonical_scalar_normalForm :
    FixedCanonicalActual.scalar =
      fun point =>
        FixedInput.scalar point +
          scalarQuadraticTimeCorrection
            (recenteredContactDiracDualScalarAcceleration 0) point := by
  rw [canonicalGeneratedActual_scalar]
  change
    (fixedP506L0FinalCommonActionActual 0).scalar =
      _
  rw [fixedP506L0FinalCommonActionActual_scalar]
  unfold recenteredCartanRepairedScalarSecondJetActual
    installScalarQuadraticTimeCorrection
  rw [fixedScalarBase_scalar_eq_input]

private theorem fixedInput_scalar_contDiff :
    ContDiff ℝ ∞ FixedInput.scalar :=
  fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1

private theorem scalarQuadraticTimeCorrection_contDiff_local
    (acceleration : ScalarCoordinateCarrier) :
    ContDiff ℝ ∞ (scalarQuadraticTimeCorrection acceleration) := by
  unfold scalarQuadraticTimeCorrection scalarQuadraticTimeCoefficient
  fun_prop

private theorem scalarQuadraticTimeCorrection_fderiv_eq_local
    (acceleration : ScalarCoordinateCarrier) (point : BasePoint) :
    fderiv ℝ (scalarQuadraticTimeCorrection acceleration) point =
      canonicalTimeProjection.smulRight
        (canonicalTimeProjection point • acceleration) := by
  have derivative :=
    (scalarQuadraticTimeCoefficient_hasFDerivAt point).smul_const acceleration
  unfold scalarQuadraticTimeCorrection
  rw [derivative.fderiv]
  apply ContinuousLinearMap.ext
  intro direction
  simp only [ContinuousLinearMap.smulRight_apply, add_apply, smul_apply,
    smul_smul]
  unfold canonicalTimeProjection
  module

private theorem
    scalarQuadraticTimeCorrection_hasFDerivAt_fderiv_origin_local
    (acceleration : ScalarCoordinateCarrier) :
    HasFDerivAt
      (fderiv ℝ (scalarQuadraticTimeCorrection acceleration))
      (canonicalTimeProjection.smulRight
        (canonicalTimeProjection.smulRight acceleration))
      0 := by
  have functionEquality :
      fderiv ℝ (scalarQuadraticTimeCorrection acceleration) =
        fun point =>
          canonicalTimeProjection.smulRight
            (canonicalTimeProjection point • acceleration) := by
    funext point
    exact scalarQuadraticTimeCorrection_fderiv_eq_local acceleration point
  rw [functionEquality]
  have linearEquality :
      (fun point : BasePoint =>
        canonicalTimeProjection.smulRight
          (canonicalTimeProjection point • acceleration)) =
        canonicalTimeProjection.smulRight
          (canonicalTimeProjection.smulRight acceleration) := by
    funext point
    apply ContinuousLinearMap.ext
    intro direction
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_smul]
    module
  rw [linearEquality]
  exact
    (canonicalTimeProjection.smulRight
      (canonicalTimeProjection.smulRight acceleration)).hasFDerivAt

private theorem scalarQuadraticTimeCorrection_hasFDerivAt_origin_zero_local
    (acceleration : ScalarCoordinateCarrier) :
    HasFDerivAt
      (scalarQuadraticTimeCorrection acceleration)
      (0 : BasePoint →L[ℝ] ScalarCoordinateCarrier)
      0 := by
  have generated :
      HasFDerivAt
        (scalarQuadraticTimeCorrection acceleration)
        (fderiv ℝ (scalarQuadraticTimeCorrection acceleration) 0)
        0 :=
    ((scalarQuadraticTimeCorrection_contDiff_local acceleration).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  rw [scalarQuadraticTimeCorrection_fderiv_eq_local] at generated
  simpa using generated

private theorem fixedScalarSecondPrimitive_eventually_differentiable :
    ∀ᶠ point in 𝓝 (0 : BasePoint),
      DifferentiableAt ℝ FixedScalarSecondPrimitive point := by
  obtain ⟨radius, radiusPositive, bound, boundPositive, localDerivative⟩ :=
    fixedNormalizedSecondAverage_exists_local_fderiv_bounded
  filter_upwards [Metric.ball_mem_nhds
    (0 : BasePoint) radiusPositive] with point pointMem
  have averageDerivative := (localDerivative point pointMem).1
  rw [show
    FixedScalarSecondPrimitive =
      fun candidate =>
        canonicalTimeProjection candidate ^ 2 •
          FixedNormalizedSecondAverage candidate by
    funext candidate
    exact fixedScalarSecondPrimitive_scaleIdentity candidate]
  exact
    ((canonicalTimeProjection.hasFDerivAt.pow 2).smul
      averageDerivative).differentiableAt

private def FixedCommonScalarSecondDerivative :
    BasePoint →L[ℝ] (BasePoint →L[ℝ] ScalarCoordinateCarrier) :=
  fderiv ℝ (fderiv ℝ FixedInput.scalar) 0 +
    FixedScalarSecondPrimitiveSecondDerivative

private theorem existing_scalar_hasFDerivAt_origin_common :
    HasFDerivAt ExistingActual.scalar
      (fderiv ℝ FixedInput.scalar 0) 0 := by
  rw [existing_scalar_normalForm]
  change HasFDerivAt
    (FixedInput.scalar + FixedScalarSecondPrimitive)
    (fderiv ℝ FixedInput.scalar 0) 0
  simpa using
    (((fixedInput_scalar_contDiff.differentiable (by simp)).differentiableAt
      |>.hasFDerivAt).add
      fixedP506L0CompleteJointScalarSecondPrimitive_hasFDerivAt_origin)

private theorem canonical_scalar_hasFDerivAt_origin_common :
    HasFDerivAt FixedCanonicalActual.scalar
      (fderiv ℝ FixedInput.scalar 0) 0 := by
  rw [canonical_scalar_normalForm]
  change HasFDerivAt
    (FixedInput.scalar +
      scalarQuadraticTimeCorrection
        (recenteredContactDiracDualScalarAcceleration 0))
    (fderiv ℝ FixedInput.scalar 0) 0
  simpa using
    (((fixedInput_scalar_contDiff.differentiable (by simp)).differentiableAt
      |>.hasFDerivAt).add
      (scalarQuadraticTimeCorrection_hasFDerivAt_origin_zero_local
        (recenteredContactDiracDualScalarAcceleration 0)))

private theorem existing_scalar_fderiv_hasFDerivAt_origin_common :
    HasFDerivAt (fderiv ℝ ExistingActual.scalar)
      FixedCommonScalarSecondDerivative 0 := by
  have baseDerivativeSmooth :
      ContDiff ℝ ∞ (fderiv ℝ FixedInput.scalar) :=
    fixedInput_scalar_contDiff.fderiv_right (m := ∞) (by simp)
  have generated :
      HasFDerivAt
        (fun point =>
          fderiv ℝ FixedInput.scalar point +
            fderiv ℝ FixedScalarSecondPrimitive point)
        FixedCommonScalarSecondDerivative 0 := by
    exact
      ((baseDerivativeSmooth.differentiable (by simp)).differentiableAt
        |>.hasFDerivAt.add
          fixedScalarSecondPrimitive_hasFDerivAt_fderiv_origin)
  apply generated.congr_of_eventuallyEq
  filter_upwards [fixedScalarSecondPrimitive_eventually_differentiable]
    with point primitiveDifferentiable
  rw [existing_scalar_normalForm]
  exact
    fderiv_add
      ((fixedInput_scalar_contDiff.differentiable
        (by simp)).differentiableAt)
      primitiveDifferentiable

private theorem canonical_scalar_fderiv_hasFDerivAt_origin_common :
    HasFDerivAt (fderiv ℝ FixedCanonicalActual.scalar)
      FixedCommonScalarSecondDerivative 0 := by
  have baseDerivativeSmooth :
      ContDiff ℝ ∞ (fderiv ℝ FixedInput.scalar) :=
    fixedInput_scalar_contDiff.fderiv_right (m := ∞) (by simp)
  have correctionDerivative :=
    scalarQuadraticTimeCorrection_hasFDerivAt_fderiv_origin_local
      (recenteredContactDiracDualScalarAcceleration 0)
  have correctionDerivative' :
      HasFDerivAt
        (fderiv ℝ
          (scalarQuadraticTimeCorrection
            (recenteredContactDiracDualScalarAcceleration 0)))
        FixedScalarSecondPrimitiveSecondDerivative 0 := by
    convert correctionDerivative using 1
    unfold FixedScalarSecondPrimitiveSecondDerivative
    rw [fixedScalarAcceleration_origin_eq_recentered]
  have generated :
      HasFDerivAt
        (fun point =>
          fderiv ℝ FixedInput.scalar point +
            fderiv ℝ
              (scalarQuadraticTimeCorrection
                (recenteredContactDiracDualScalarAcceleration 0))
              point)
        FixedCommonScalarSecondDerivative 0 := by
    exact
      ((baseDerivativeSmooth.differentiable (by simp)).differentiableAt
        |>.hasFDerivAt.add correctionDerivative')
  apply generated.congr_of_eventuallyEq
  filter_upwards [] with point
  rw [canonical_scalar_normalForm]
  exact
    fderiv_add
      ((fixedInput_scalar_contDiff.differentiable
        (by simp)).differentiableAt)
      (((scalarQuadraticTimeCorrection_contDiff_local
          (recenteredContactDiracDualScalarAcceleration 0)).differentiable
        (by simp)).differentiableAt)

private theorem existing_scalar_origin_eq_input :
    ExistingActual.scalar 0 = FixedInput.scalar 0 := by
  rw [existing_scalar_normalForm]
  have primitiveZero :
      FixedScalarSecondPrimitive 0 = 0 := by
    simpa only [FixedScalarSecondPrimitive,
      canonicalCauchySlicePoint_zero_zero_local] using
      (canonicalTimeSecondPrimitive_zeroSlice FixedScalarAcceleration
        (0 : StageNineSpatialPoint))
  change FixedInput.scalar 0 + FixedScalarSecondPrimitive 0 =
    FixedInput.scalar 0
  rw [primitiveZero, add_zero]

private theorem canonical_scalar_origin_eq_input :
    FixedCanonicalActual.scalar 0 = FixedInput.scalar 0 := by
  rw [canonical_scalar_normalForm]
  simp

private theorem existing_scalar_origin_eq_canonical :
    ExistingActual.scalar 0 = FixedCanonicalActual.scalar 0 :=
  existing_scalar_origin_eq_input.trans canonical_scalar_origin_eq_input.symm

private theorem existing_scalar_fderiv_origin_eq_canonical :
    fderiv ℝ ExistingActual.scalar 0 =
      fderiv ℝ FixedCanonicalActual.scalar 0 := by
  rw [existing_scalar_hasFDerivAt_origin_common.fderiv,
    canonical_scalar_hasFDerivAt_origin_common.fderiv]

private theorem existing_scalar_fderivDerivative_origin_eq_canonical :
    fderiv ℝ (fderiv ℝ ExistingActual.scalar) 0 =
      fderiv ℝ (fderiv ℝ FixedCanonicalActual.scalar) 0 := by
  rw [existing_scalar_fderiv_hasFDerivAt_origin_common.fderiv,
    canonical_scalar_fderiv_hasFDerivAt_origin_common.fderiv]

private theorem fixedCanonicalActual_coframe_contDiff_local :
    ContDiff ℝ ∞ FixedCanonicalActual.coframe := by
  rw [canonicalGeneratedActual_coframe]
  exact fixedP506L0FinalCommonActionActual_coframe_contDiff 0

private theorem fixedCanonicalActual_coframe_origin :
    FixedCanonicalActual.coframe 0 = 1 := by
  rw [canonicalGeneratedActual_coframe,
    fixedP506L0FinalCommonActionActual_coframe_origin]

private def FixedCanonicalGaugeCoordinates
    (formDirection : LorentzianIndex) :
    BasePoint → P286CoordinateCarrier :=
  fun point =>
    p286CoordinateEquiv
      (FixedCanonicalActual.gaugeConnection point formDirection)

private theorem fixedCanonicalGaugeCoordinates_contDiff
    (formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ (FixedCanonicalGaugeCoordinates formDirection) := by
  have candidateSmooth :=
    installP286HolonomicConnectionSecondJet_smooth
      (fixedP506L0FinalCommonActionActual 0)
      (fixedP506L0FinalCommonActionActual_smooth 0)
      (p286CanonicalDiagonalResponseSecondJet
        fixedP506L0P286CanonicalGeneratedWrite)
      1
  change ContDiff ℝ ∞ fun point =>
    p286CoordinateEquiv
      ((fixedP506L0P286CanonicalConnectionCandidate
        fixedP506L0P286CanonicalGeneratedWrite).gaugeConnection point
          formDirection)
  exact candidateSmooth.2.2.2.2.1 formDirection

private theorem scalarP286ActionBilinear_coordinate
    (connection : P286LieBlockData)
    (scalar : ScalarCoordinateCarrier) :
    scalarP286ActionBilinear (p286CoordinateEquiv connection) scalar =
      scalarMotherLieAction (p286LieBlockEmbed connection) scalar := by
  change
    scalarMotherLieAction
        (p286LieBlockEmbed
          (p286CoordinateEquiv.symm (p286CoordinateEquiv connection)))
        scalar =
      _
  rw [p286CoordinateEquiv.symm_apply_apply]

private theorem existing_scalarCovariant_component_normalForm
    (formDirection : LorentzianIndex) :
    (fun point =>
      holonomicScalarCovariantDerivative ExistingActual point
        formDirection) =
      fun point =>
        (ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
          (coordinateDirection formDirection))
            (fderiv ℝ ExistingActual.scalar point) +
          scalarP286ActionBilinear
            (FixedCanonicalGaugeCoordinates formDirection point)
            (ExistingActual.scalar point) := by
  funext point
  unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
  rw [existing_gaugeConnection_eq_canonical]
  change
    fderiv ℝ ExistingActual.scalar point
          (coordinateDirection formDirection) +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (FixedCanonicalActual.gaugeConnection point formDirection))
          (ExistingActual.scalar point) =
      fderiv ℝ ExistingActual.scalar point
          (coordinateDirection formDirection) +
        scalarP286ActionBilinear
          (p286CoordinateEquiv
            (FixedCanonicalActual.gaugeConnection point formDirection))
          (ExistingActual.scalar point)
  rw [scalarP286ActionBilinear_coordinate]

private theorem canonical_scalarCovariant_component_normalForm
    (formDirection : LorentzianIndex) :
    (fun point =>
      holonomicScalarCovariantDerivative FixedCanonicalActual point
        formDirection) =
      fun point =>
        (ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
          (coordinateDirection formDirection))
            (fderiv ℝ FixedCanonicalActual.scalar point) +
          scalarP286ActionBilinear
            (FixedCanonicalGaugeCoordinates formDirection point)
            (FixedCanonicalActual.scalar point) := by
  funext point
  unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
  change
    fderiv ℝ FixedCanonicalActual.scalar point
          (coordinateDirection formDirection) +
        scalarMotherLieAction
          (p286LieBlockEmbed
            (FixedCanonicalActual.gaugeConnection point formDirection))
          (FixedCanonicalActual.scalar point) =
      fderiv ℝ FixedCanonicalActual.scalar point
          (coordinateDirection formDirection) +
        scalarP286ActionBilinear
          (p286CoordinateEquiv
            (FixedCanonicalActual.gaugeConnection point formDirection))
          (FixedCanonicalActual.scalar point)
  rw [scalarP286ActionBilinear_coordinate]

private theorem existing_scalarCovariant_component_differentiableAt
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        holonomicScalarCovariantDerivative ExistingActual point
          formDirection)
      0 := by
  let evaluate :
      (BasePoint →L[ℝ] ScalarCoordinateCarrier) →L[ℝ]
        ScalarCoordinateCarrier :=
    ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
      (coordinateDirection formDirection)
  let action :=
    scalarP286ActionBilinear.toContinuousBilinearMap
  have evaluatedDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          evaluate (fderiv ℝ ExistingActual.scalar point))
        0 :=
    (evaluate.hasFDerivAt.comp 0
      existing_scalar_fderiv_hasFDerivAt_origin_common).differentiableAt
  have gaugeDerivative :
      HasFDerivAt
        (FixedCanonicalGaugeCoordinates formDirection)
        (fderiv ℝ (FixedCanonicalGaugeCoordinates formDirection) 0)
        0 :=
    ((fixedCanonicalGaugeCoordinates_contDiff formDirection).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have actionDifferentiable :=
    action.hasFDerivAt_of_bilinear gaugeDerivative
      existing_scalar_hasFDerivAt_origin_common
      |>.differentiableAt
  rw [existing_scalarCovariant_component_normalForm]
  exact evaluatedDifferentiable.add actionDifferentiable

private theorem canonical_scalarCovariant_component_differentiableAt
    (formDirection : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point =>
        holonomicScalarCovariantDerivative FixedCanonicalActual point
          formDirection)
      0 := by
  let evaluate :
      (BasePoint →L[ℝ] ScalarCoordinateCarrier) →L[ℝ]
        ScalarCoordinateCarrier :=
    ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
      (coordinateDirection formDirection)
  let action :=
    scalarP286ActionBilinear.toContinuousBilinearMap
  have evaluatedDifferentiable :
      DifferentiableAt ℝ
        (fun point =>
          evaluate (fderiv ℝ FixedCanonicalActual.scalar point))
        0 :=
    (evaluate.hasFDerivAt.comp 0
      canonical_scalar_fderiv_hasFDerivAt_origin_common).differentiableAt
  have gaugeDerivative :
      HasFDerivAt
        (FixedCanonicalGaugeCoordinates formDirection)
        (fderiv ℝ (FixedCanonicalGaugeCoordinates formDirection) 0)
        0 :=
    ((fixedCanonicalGaugeCoordinates_contDiff formDirection).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have actionDifferentiable :=
    action.hasFDerivAt_of_bilinear gaugeDerivative
      canonical_scalar_hasFDerivAt_origin_common
      |>.differentiableAt
  rw [canonical_scalarCovariant_component_normalForm]
  exact evaluatedDifferentiable.add actionDifferentiable

private theorem existing_scalarCovariant_component_fderiv_origin_eq_canonical
    (formDirection : LorentzianIndex) :
    fderiv ℝ
        (fun point =>
          holonomicScalarCovariantDerivative ExistingActual point
            formDirection)
        0 =
      fderiv ℝ
        (fun point =>
          holonomicScalarCovariantDerivative FixedCanonicalActual point
            formDirection)
        0 := by
  let evaluate :
      (BasePoint →L[ℝ] ScalarCoordinateCarrier) →L[ℝ]
        ScalarCoordinateCarrier :=
    ContinuousLinearMap.apply ℝ ScalarCoordinateCarrier
      (coordinateDirection formDirection)
  let action :=
    scalarP286ActionBilinear.toContinuousBilinearMap
  have existingEvaluated :=
    evaluate.hasFDerivAt.comp 0
      existing_scalar_fderiv_hasFDerivAt_origin_common
  have canonicalEvaluated :=
    evaluate.hasFDerivAt.comp 0
      canonical_scalar_fderiv_hasFDerivAt_origin_common
  have existingEvaluated' :
      HasFDerivAt
        (fun point =>
          evaluate (fderiv ℝ ExistingActual.scalar point))
        (evaluate.comp FixedCommonScalarSecondDerivative) 0 := by
    convert existingEvaluated using 1 <;> rfl
  have canonicalEvaluated' :
      HasFDerivAt
        (fun point =>
          evaluate (fderiv ℝ FixedCanonicalActual.scalar point))
        (evaluate.comp FixedCommonScalarSecondDerivative) 0 := by
    convert canonicalEvaluated using 1 <;> rfl
  have gaugeDerivative :
      HasFDerivAt
        (FixedCanonicalGaugeCoordinates formDirection)
        (fderiv ℝ (FixedCanonicalGaugeCoordinates formDirection) 0)
        0 :=
    ((fixedCanonicalGaugeCoordinates_contDiff formDirection).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have existingAction :=
    action.hasFDerivAt_of_bilinear gaugeDerivative
      existing_scalar_hasFDerivAt_origin_common
  have canonicalAction :=
    action.hasFDerivAt_of_bilinear gaugeDerivative
      canonical_scalar_hasFDerivAt_origin_common
  rw [existing_scalarCovariant_component_normalForm,
    canonical_scalarCovariant_component_normalForm]
  change
    fderiv ℝ
        ((fun point =>
          evaluate (fderiv ℝ ExistingActual.scalar point)) +
          fun point =>
            action (FixedCanonicalGaugeCoordinates formDirection point)
              (ExistingActual.scalar point))
        0 =
      fderiv ℝ
        ((fun point =>
          evaluate (fderiv ℝ FixedCanonicalActual.scalar point)) +
          fun point =>
            action (FixedCanonicalGaugeCoordinates formDirection point)
              (FixedCanonicalActual.scalar point))
        0
  rw [
    fderiv_add existingEvaluated'.differentiableAt
      existingAction.differentiableAt,
    fderiv_add canonicalEvaluated'.differentiableAt
      canonicalAction.differentiableAt,
    existingEvaluated'.fderiv, canonicalEvaluated'.fderiv,
    existingAction.fderiv, canonicalAction.fderiv,
    existing_scalar_origin_eq_canonical]

private theorem existing_scalarCovariant_differentiableAt :
    DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative ExistingActual) 0 := by
  rw [differentiableAt_pi]
  exact existing_scalarCovariant_component_differentiableAt

private theorem canonical_scalarCovariant_differentiableAt :
    DifferentiableAt ℝ
      (holonomicScalarCovariantDerivative FixedCanonicalActual) 0 := by
  rw [differentiableAt_pi]
  exact canonical_scalarCovariant_component_differentiableAt

private theorem existing_scalarCovariant_fderiv_origin_eq_canonical :
    fderiv ℝ (holonomicScalarCovariantDerivative ExistingActual) 0 =
      fderiv ℝ
        (holonomicScalarCovariantDerivative FixedCanonicalActual) 0 := by
  change
    fderiv ℝ
        (fun point formDirection =>
          holonomicScalarCovariantDerivative ExistingActual point
            formDirection)
        0 =
      fderiv ℝ
        (fun point formDirection =>
          holonomicScalarCovariantDerivative FixedCanonicalActual point
            formDirection)
        0
  rw [fderiv_pi existing_scalarCovariant_component_differentiableAt,
    fderiv_pi canonical_scalarCovariant_component_differentiableAt]
  apply ContinuousLinearMap.ext
  intro pointDirection
  funext formDirection
  simp only [ContinuousLinearMap.pi_apply]
  exact congrArg (fun derivative => derivative pointDirection)
    (existing_scalarCovariant_component_fderiv_origin_eq_canonical
      formDirection)

private theorem existing_scalarCovariant_origin_eq_canonical :
    holonomicScalarCovariantDerivative ExistingActual 0 =
      holonomicScalarCovariantDerivative FixedCanonicalActual 0 := by
  funext formDirection
  unfold holonomicScalarCovariantDerivative fieldDirectionalDerivative
  rw [existing_gaugeConnection_eq_canonical,
    existing_scalar_origin_eq_canonical,
    existing_scalar_fderiv_origin_eq_canonical]

/-! ## Public fixed-lineage scalar first-germ seam -/

/-- The complete-joint global development and the established canonical
actual have the same scalar value and complete scalar first derivative at the
fixed occurrence.  This is the fixed-lineage core consumed by action readers;
it does not assert equality of the two scalar fields away from the origin. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalarFirstGerm_origin_eq_canonical :
    fixedP506L0CompleteJointGlobalDevelopmentActual.scalar 0 =
        fixedP506L0P286CanonicalGeneratedActual.scalar 0 ∧
      fderiv ℝ fixedP506L0CompleteJointGlobalDevelopmentActual.scalar 0 =
        fderiv ℝ fixedP506L0P286CanonicalGeneratedActual.scalar 0 := by
  exact ⟨existing_scalar_origin_eq_canonical,
    existing_scalar_fderiv_origin_eq_canonical⟩

/-- The scalar covariant derivative itself has the same value and complete
first derivative on the two fixed actuals.  In particular this includes the
action-generated scalar acceleration entering the temporal charged current. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalarCovariantFirstGerm_origin_eq_canonical :
    holonomicScalarCovariantDerivative
          fixedP506L0CompleteJointGlobalDevelopmentActual 0 =
        holonomicScalarCovariantDerivative
          fixedP506L0P286CanonicalGeneratedActual 0 ∧
      fderiv ℝ
          (holonomicScalarCovariantDerivative
            fixedP506L0CompleteJointGlobalDevelopmentActual) 0 =
        fderiv ℝ
          (holonomicScalarCovariantDerivative
            fixedP506L0P286CanonicalGeneratedActual) 0 := by
  exact ⟨existing_scalarCovariant_origin_eq_canonical,
    existing_scalarCovariant_fderiv_origin_eq_canonical⟩

/-- Differentiable fixed-germ mouth for the generated scalar field, with the
canonical derivative chosen as the common derivative. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalar_hasFDerivAt_origin_canonical :
    HasFDerivAt
      fixedP506L0CompleteJointGlobalDevelopmentActual.scalar
      (fderiv ℝ fixedP506L0P286CanonicalGeneratedActual.scalar 0) 0 := by
  simpa only [← canonical_scalar_hasFDerivAt_origin_common.fderiv] using
    existing_scalar_hasFDerivAt_origin_common

/-- Differentiable fixed-germ mouth for the canonical comparison scalar. -/
theorem
    fixedP506L0P286CanonicalGeneratedActual_scalar_hasFDerivAt_origin :
    HasFDerivAt
      fixedP506L0P286CanonicalGeneratedActual.scalar
      (fderiv ℝ fixedP506L0P286CanonicalGeneratedActual.scalar 0) 0 :=
  canonical_scalar_hasFDerivAt_origin_common.differentiableAt.hasFDerivAt

/-- Differentiable fixed-germ mouth for the complete scalar covariant
derivative, including its action-generated temporal acceleration. -/
theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalarCovariant_hasFDerivAt_origin_canonical :
    HasFDerivAt
      (holonomicScalarCovariantDerivative
        fixedP506L0CompleteJointGlobalDevelopmentActual)
      (fderiv ℝ
        (holonomicScalarCovariantDerivative
          fixedP506L0P286CanonicalGeneratedActual) 0) 0 := by
  simpa only [existing_scalarCovariant_fderiv_origin_eq_canonical] using
    existing_scalarCovariant_differentiableAt.hasFDerivAt

/-- Differentiable fixed-germ mouth for the canonical scalar covariant
derivative used on the comparison side of charged-current readers. -/
theorem
    fixedP506L0P286CanonicalGeneratedActual_scalarCovariant_hasFDerivAt_origin :
    HasFDerivAt
      (holonomicScalarCovariantDerivative
        fixedP506L0P286CanonicalGeneratedActual)
      (fderiv ℝ
        (holonomicScalarCovariantDerivative
          fixedP506L0P286CanonicalGeneratedActual) 0) 0 :=
  canonical_scalarCovariant_differentiableAt.hasFDerivAt

private theorem
    existing_scalarMomentum_diagonalDerivative_origin_eq_canonical
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          ExistingActual direction derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (scalarDifferentialMomentum positiveSmoothUnifiedSource
          FixedCanonicalActual direction derivativeDirection)
        0 derivativeDirection := by
  let outer :=
    scalarMomentumCoframeCovariantReadout direction derivativeDirection
  let existingInner := fun point : BasePoint =>
    (ExistingActual.coframe point,
      holonomicScalarCovariantDerivative ExistingActual point)
  let canonicalInner := fun point : BasePoint =>
    (FixedCanonicalActual.coframe point,
      holonomicScalarCovariantDerivative FixedCanonicalActual point)
  let commonInnerDerivative :=
    (fderiv ℝ FixedCanonicalActual.coframe 0).prod
      (fderiv ℝ
        (holonomicScalarCovariantDerivative FixedCanonicalActual) 0)
  have canonicalCoframeDerivative :
      HasFDerivAt FixedCanonicalActual.coframe
        (fderiv ℝ FixedCanonicalActual.coframe 0) 0 :=
    ((fixedCanonicalActual_coframe_contDiff_local.differentiable
      (by simp)).differentiableAt).hasFDerivAt
  have existingCoframeDerivative :
      HasFDerivAt ExistingActual.coframe
        (fderiv ℝ FixedCanonicalActual.coframe 0) 0 := by
    rw [existing_coframe_eq_canonical]
    exact canonicalCoframeDerivative
  have existingInnerDerivative :
      HasFDerivAt existingInner commonInnerDerivative 0 :=
    HasFDerivAt.prodMk existingCoframeDerivative
      (by
        rw [← existing_scalarCovariant_fderiv_origin_eq_canonical]
        exact existing_scalarCovariant_differentiableAt.hasFDerivAt)
  have canonicalInnerDerivative :
      HasFDerivAt canonicalInner commonInnerDerivative 0 :=
    HasFDerivAt.prodMk canonicalCoframeDerivative
      canonical_scalarCovariant_differentiableAt.hasFDerivAt
  have canonicalInnerOrigin :
      canonicalInner 0 =
        ((1 : LorentzianCoframe),
          holonomicScalarCovariantDerivative FixedCanonicalActual 0) := by
    unfold canonicalInner
    rw [fixedCanonicalActual_coframe_origin]
  have existingInnerOrigin :
      existingInner 0 =
        ((1 : LorentzianCoframe),
          holonomicScalarCovariantDerivative FixedCanonicalActual 0) := by
    unfold existingInner
    apply Prod.ext
    · rw [existing_coframe_eq_canonical,
        fixedCanonicalActual_coframe_origin]
    · exact existing_scalarCovariant_origin_eq_canonical
  have outerDifferentiable : DifferentiableAt ℝ outer
      ((1 : LorentzianCoframe),
        holonomicScalarCovariantDerivative FixedCanonicalActual 0) :=
    (scalarMomentumCoframeCovariantReadout_contDiffAt_one
      direction derivativeDirection
      (holonomicScalarCovariantDerivative FixedCanonicalActual 0)
      ).differentiableAt (by simp)
  have outerAtExisting : DifferentiableAt ℝ outer (existingInner 0) := by
    rw [existingInnerOrigin]
    exact outerDifferentiable
  have outerAtCanonical : DifferentiableAt ℝ outer (canonicalInner 0) := by
    rw [canonicalInnerOrigin]
    exact outerDifferentiable
  have existingInnerDirectional :
      (fderiv ℝ existingInner 0)
          (coordinateDirection derivativeDirection) =
        commonInnerDerivative (coordinateDirection derivativeDirection) :=
    congrArg
      (fun derivative =>
        derivative (coordinateDirection derivativeDirection))
      existingInnerDerivative.fderiv
  have canonicalInnerDirectional :
      (fderiv ℝ canonicalInner 0)
          (coordinateDirection derivativeDirection) =
        commonInnerDerivative (coordinateDirection derivativeDirection) :=
    congrArg
      (fun derivative =>
        derivative (coordinateDirection derivativeDirection))
      canonicalInnerDerivative.fderiv
  unfold fieldDirectionalDerivative
  rw [scalarDifferentialMomentum_eq_readout,
    scalarDifferentialMomentum_eq_readout]
  change
    (fderiv ℝ (outer ∘ existingInner) 0)
        (coordinateDirection derivativeDirection) =
      (fderiv ℝ (outer ∘ canonicalInner) 0)
        (coordinateDirection derivativeDirection)
  rw [fderiv_comp 0 outerAtExisting existingInnerDerivative.differentiableAt,
    fderiv_comp 0 outerAtCanonical canonicalInnerDerivative.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply]
  rw [existingInnerOrigin, canonicalInnerOrigin]
  apply congrArg
  exact existingInnerDirectional.trans canonicalInnerDirectional.symm

private theorem
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalarMomentumDivergence_origin_eq_accepted
    (direction : ScalarCoordinateCarrier) :
    scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ExistingActual direction 0 =
      scalarDifferentialMomentumDivergence positiveSmoothUnifiedSource
        AcceptedActual direction 0 := by
  rw [← congrFun
    canonicalGeneratedActual_scalarDifferentialMomentumDivergence_origin_eq
    direction]
  unfold scalarDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    existing_scalarMomentum_diagonalDerivative_origin_eq_canonical
      direction derivativeDirection

/-- The source/current-generated live-electric global development closes the
scalar Euler--Lagrange channel at the fixed P506/L0 occurrence.  The writer is
the pre-existing integrated scalar acceleration operator; this theorem only
reads its resulting common second jet through the action equation. -/
theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_origin_zero :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      LiveActual 0).scalar =
      0 := by
  apply
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_origin_zero_of_momentumDivergence
  exact
    fixedP506L0CompleteJointGlobalDevelopmentActual_scalarMomentumDivergence_origin_eq_accepted

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginScalarClosure
