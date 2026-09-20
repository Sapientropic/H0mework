import Mathlib.Analysis.Calculus.ContDiff.RCLike
import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity
import H0mework.Physics.JointVariation.TemporalDevelopmentOperator

/-!
# Canonical second-primitive ambient first-jet regularity

The canonical second time primitive factors as a quadratic time coordinate
times a fixed-interval average.  A local `C¹` profile is locally Lipschitz, so
the average is uniformly Lipschitz near the common occurrence.  On a ball of
radius `O (‖point‖)`, the whole quadratic primitive therefore has Lipschitz
constant `O (‖point‖)`.  The generic `fderiv` norm estimate then makes its
ambient first jet converge to zero, including at nondifferentiable points
where `fderiv` is definitionally zero.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity

open Asymptotics Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator

open scoped Interval NNReal Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private theorem canonical_time_single
    (time : ℝ) :
    EuclideanSpace.single canonicalLorentzianTimeDirection time =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

private def normalizedCanonicalTimeSliceCLM
    (parameter : ℝ) : BasePoint →L[ℝ] BasePoint :=
  parameter •
      canonicalTimeProjection.smulRight
        (coordinateDirection canonicalLorentzianTimeDirection) +
    canonicalSpatialInclusion.comp canonicalSpatialProjection

private theorem normalizedCanonicalTimeSliceCLM_apply
    (parameter : ℝ) (point : BasePoint) :
    normalizedCanonicalTimeSliceCLM parameter point =
      canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point) := by
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion,
    canonical_time_single]
  simp only [normalizedCanonicalTimeSliceCLM,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    smul_smul]
  rw [mul_comm parameter]

private def normalizedCanonicalTimeSliceBound : ℝ :=
  ‖canonicalTimeProjection.smulRight
      (coordinateDirection canonicalLorentzianTimeDirection)‖ +
    ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ + 1

private theorem normalizedCanonicalTimeSliceBound_pos :
    0 < normalizedCanonicalTimeSliceBound := by
  unfold normalizedCanonicalTimeSliceBound
  positivity

private theorem normalizedCanonicalTimeSliceCLM_norm_lt_bound
    {parameter : ℝ} (parameter_mem : parameter ∈ Icc (0 : ℝ) 1) :
    ‖normalizedCanonicalTimeSliceCLM parameter‖ <
      normalizedCanonicalTimeSliceBound := by
  unfold normalizedCanonicalTimeSliceCLM
    normalizedCanonicalTimeSliceBound
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
      have parameter_abs : |parameter| ≤ 1 := by
        rw [abs_of_nonneg parameter_mem.1]
        exact parameter_mem.2
      exact add_le_add
        (mul_le_of_le_one_left
          (norm_nonneg
            (canonicalTimeProjection.smulRight
              (coordinateDirection canonicalLorentzianTimeDirection)))
          parameter_abs)
        le_rfl
    _ < _ := by linarith

private def normalizedSecondAverage
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) : E :=
  ∫ outerParameter in (0 : ℝ)..1,
    outerParameter •
      ∫ innerParameter in (0 : ℝ)..1,
        profile
          (normalizedCanonicalTimeSliceCLM
            (outerParameter * innerParameter) point)

private theorem canonicalTimeSecondPrimitive_scaleIdentity
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) :
    canonicalTimeSecondPrimitive profile point =
      canonicalTimeProjection point ^ 2 •
        normalizedSecondAverage profile point := by
  unfold canonicalTimeSecondPrimitive normalizedSecondAverage
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  let innerPrimitive : ℝ → E := fun outerTime =>
    ∫ innerTime in (0 : ℝ)..outerTime,
      profile (canonicalCauchySlicePoint innerTime space)
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
            profile
              (canonicalCauchySlicePoint
                (time * outerParameter * innerParameter) space) := by
    simpa [innerPrimitive] using
      (intervalIntegral.smul_integral_comp_mul_left
        (f := fun innerTime =>
          profile (canonicalCauchySlicePoint innerTime space))
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
      profile
          (canonicalCauchySlicePoint
            (canonicalTimeProjection point *
              (outerParameter * innerParameter))
            (canonicalSpatialProjection point)) =
        profile
          (normalizedCanonicalTimeSliceCLM
            (outerParameter * innerParameter) point)
    rw [normalizedCanonicalTimeSliceCLM_apply]

/-- Canonical second temporal integration commutes with recentering at a
fixed occurrence on the distinguished zero slice.  This is a chart
transporter for an already generated profile; it does not select the profile
or its action response. -/
theorem
    canonicalTimeSecondPrimitive_comp_canonicalSpacetimeContactTranslation_zeroSlice
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (space : StageNineSpatialPoint) :
    canonicalTimeSecondPrimitive profile ∘
        canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space) =
      canonicalTimeSecondPrimitive
        (profile ∘ canonicalSpacetimeContactTranslation
          (canonicalCauchySlicePoint 0 space)) := by
  funext point
  unfold canonicalTimeSecondPrimitive Function.comp
  simp only
  have timeProjectionTranslation :
      canonicalTimeProjection
          (canonicalSpacetimeContactTranslation
            (canonicalCauchySlicePoint 0 space) point) =
        canonicalTimeProjection point := by
    simp [canonicalSpacetimeContactTranslation,
      canonicalTimeProjection, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]
  rw [timeProjectionTranslation]
  apply intervalIntegral.integral_congr
  intro outerTime _
  apply intervalIntegral.integral_congr
  intro innerTime _
  apply congrArg profile
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalSpacetimeContactTranslation,
      canonicalSpatialProjection, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, Fin.sum_univ_three]

/-- The canonical second primitive is the canonical first primitive applied
twice.  This identifies the action-owned double integration with the existing
first-primitive regularity mechanism; it does not change the generated
profile or choose a target jet. -/
theorem canonicalTimeSecondPrimitive_eq_iterated
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E) :
    canonicalTimeSecondPrimitive profile =
      canonicalTimePrimitive (canonicalTimePrimitive profile) := by
  funext point
  unfold canonicalTimeSecondPrimitive canonicalTimePrimitive
  apply intervalIntegral.integral_congr
  intro outerTime _
  simp

/-- A locally `C¹` action profile generates a locally `C¹` canonical second
primitive.  The proof reuses the first-primitive producer twice through the
exact iterated normal form above. -/
theorem canonicalTimeSecondPrimitive_contDiffAt_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ContDiffAt ℝ 1 (canonicalTimeSecondPrimitive profile) 0 := by
  rw [canonicalTimeSecondPrimitive_eq_iterated]
  exact canonicalTimePrimitive_contDiffAt_of_contDiffAt _
    (canonicalTimePrimitive_contDiffAt_of_contDiffAt profile regular)

private theorem normalizedCanonicalTimeSliceCLM_joint_continuous
    (point : BasePoint) :
    Continuous fun parameters : ℝ × ℝ =>
      normalizedCanonicalTimeSliceCLM
        (parameters.1 * parameters.2) point := by
  unfold normalizedCanonicalTimeSliceCLM
  fun_prop

private theorem normalized_profile_joint_continuousOn
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {profile : BasePoint → E}
    {target : Set BasePoint}
    {domain : Set BasePoint}
    {point : BasePoint}
    (profileLipschitz : ∃ K, LipschitzOnWith K profile target)
    (point_mem : point ∈ domain)
    (mapsTo :
      ∀ point ∈ domain,
        ∀ outerParameter ∈ Icc (0 : ℝ) 1,
          ∀ innerParameter ∈ Icc (0 : ℝ) 1,
            normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point ∈
              target) :
    ContinuousOn
      (fun parameters : ℝ × ℝ =>
        profile
          (normalizedCanonicalTimeSliceCLM
            (parameters.1 * parameters.2) point))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨K, profileLipschitz⟩ := profileLipschitz
  apply profileLipschitz.continuousOn.comp
    (normalizedCanonicalTimeSliceCLM_joint_continuous point).continuousOn
  intro parameters parameters_mem
  exact mapsTo point point_mem parameters.1 parameters_mem.1
    parameters.2 parameters_mem.2

private theorem normalized_inner_integral_continuousOn
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {profile : BasePoint → E}
    {target : Set BasePoint}
    {domain : Set BasePoint}
    {point : BasePoint}
    (profileLipschitz : ∃ K, LipschitzOnWith K profile target)
    (point_mem : point ∈ domain)
    (mapsTo :
      ∀ point ∈ domain,
        ∀ outerParameter ∈ Icc (0 : ℝ) 1,
          ∀ innerParameter ∈ Icc (0 : ℝ) 1,
            normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point ∈
              target) :
    ContinuousOn
      (fun outerParameter =>
        ∫ innerParameter in (0 : ℝ)..1,
          profile
            (normalizedCanonicalTimeSliceCLM
              (outerParameter * innerParameter) point))
      (Icc (0 : ℝ) 1) := by
  let joint : ℝ × ℝ → E := fun parameters =>
    profile
      (normalizedCanonicalTimeSliceCLM
        (parameters.1 * parameters.2) point)
  have jointContinuous :
      ContinuousOn joint
        (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    normalized_profile_joint_continuousOn profileLipschitz point_mem mapsTo
  obtain ⟨bound, bound_nonnegative⟩ :
      ∃ bound : ℝ,
        ∀ parameters ∈
            (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
          ‖joint parameters‖ ≤ bound :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      jointContinuous
  intro outerParameter outer_mem
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
  · filter_upwards [self_mem_nhdsWithin] with candidate candidate_mem
    have sectionContinuous :
        ContinuousOn (fun innerParameter => joint (candidate, innerParameter))
          (Icc (0 : ℝ) 1) := by
      apply jointContinuous.comp
        ((continuous_const.prodMk continuous_id).continuousOn)
      intro innerParameter inner_mem
      exact ⟨candidate_mem, inner_mem⟩
    have intervalSubset :
        Ι (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
      intro innerParameter inner_mem
      have actual := uIoc_subset_uIcc inner_mem
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    exact
      (sectionContinuous.mono intervalSubset).aestronglyMeasurable
        measurableSet_uIoc
  · filter_upwards [self_mem_nhdsWithin] with candidate candidate_mem
    filter_upwards [] with innerParameter
    intro inner_mem
    have inner_mem' : innerParameter ∈ Icc (0 : ℝ) 1 := by
      have actual := uIoc_subset_uIcc inner_mem
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    exact bound_nonnegative (candidate, innerParameter)
      ⟨candidate_mem, inner_mem'⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with innerParameter
    intro inner_mem
    have inner_mem' : innerParameter ∈ Icc (0 : ℝ) 1 := by
      have actual := uIoc_subset_uIcc inner_mem
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
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
          ⟨outer_mem, inner_mem'⟩)
        pairContinuous
        (fun candidate candidate_mem => ⟨candidate_mem, inner_mem'⟩)
    simpa [Function.comp_def] using composed

private theorem normalized_outer_integrand_intervalIntegrable
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {profile : BasePoint → E}
    {target : Set BasePoint}
    {domain : Set BasePoint}
    {point : BasePoint}
    (profileLipschitz : ∃ K, LipschitzOnWith K profile target)
    (point_mem : point ∈ domain)
    (mapsTo :
      ∀ point ∈ domain,
        ∀ outerParameter ∈ Icc (0 : ℝ) 1,
          ∀ innerParameter ∈ Icc (0 : ℝ) 1,
            normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point ∈
              target) :
    IntervalIntegrable
      (fun outerParameter =>
        outerParameter •
          ∫ innerParameter in (0 : ℝ)..1,
            profile
              (normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point))
      MeasureTheory.volume 0 1 := by
  have innerContinuous :=
    normalized_inner_integral_continuousOn
      profileLipschitz point_mem mapsTo
  exact
    (continuousOn_id.smul innerContinuous).intervalIntegrable_of_Icc
      (by norm_num)

private theorem normalizedSecondAverage_lipschitzOnWith
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    {profile : BasePoint → E}
    {target domain : Set BasePoint}
    {K : ℝ≥0}
    (profileLipschitz : LipschitzOnWith K profile target)
    (mapsTo :
      ∀ point ∈ domain,
        ∀ outerParameter ∈ Icc (0 : ℝ) 1,
          ∀ innerParameter ∈ Icc (0 : ℝ) 1,
            normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point ∈
              target) :
    LipschitzOnWith
      (K * ⟨normalizedCanonicalTimeSliceBound,
        normalizedCanonicalTimeSliceBound_pos.le⟩)
      (normalizedSecondAverage profile) domain := by
  have innerIntervalIntegrable
      {point : BasePoint} (point_mem : point ∈ domain)
      {outerParameter : ℝ}
      (outer_mem : outerParameter ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable
        (fun innerParameter =>
          profile
            (normalizedCanonicalTimeSliceCLM
              (outerParameter * innerParameter) point))
        MeasureTheory.volume 0 1 := by
    have jointContinuous :=
      normalized_profile_joint_continuousOn
        (show ∃ K, LipschitzOnWith K profile target from
          ⟨K, profileLipschitz⟩)
        point_mem mapsTo
    have sectionContinuous :
        ContinuousOn
          (fun innerParameter =>
            profile
              (normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point))
          (Icc (0 : ℝ) 1) := by
      apply jointContinuous.comp
        ((continuous_const.prodMk continuous_id).continuousOn)
      intro innerParameter inner_mem
      exact ⟨outer_mem, inner_mem⟩
    exact sectionContinuous.intervalIntegrable_of_Icc (by norm_num)
  have outerIntervalIntegrable
      {point : BasePoint} (point_mem : point ∈ domain) :
      IntervalIntegrable
        (fun outerParameter =>
          outerParameter •
            ∫ innerParameter in (0 : ℝ)..1,
              profile
                (normalizedCanonicalTimeSliceCLM
                  (outerParameter * innerParameter) point))
        MeasureTheory.volume 0 1 :=
    normalized_outer_integrand_intervalIntegrable
      (show ∃ K, LipschitzOnWith K profile target from
        ⟨K, profileLipschitz⟩)
      point_mem mapsTo
  apply LipschitzOnWith.of_dist_le_mul
  intro first first_mem second second_mem
  rw [dist_eq_norm]
  unfold normalizedSecondAverage
  rw [← intervalIntegral.integral_sub
    (outerIntervalIntegrable first_mem)
    (outerIntervalIntegrable second_mem)]
  have outerBound :
      ‖∫ outerParameter in (0 : ℝ)..1,
          (outerParameter •
              ∫ innerParameter in (0 : ℝ)..1,
                profile
                  (normalizedCanonicalTimeSliceCLM
                    (outerParameter * innerParameter) first)) -
            outerParameter •
              ∫ innerParameter in (0 : ℝ)..1,
                profile
                  (normalizedCanonicalTimeSliceCLM
                    (outerParameter * innerParameter) second)‖
        ≤ ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
            ‖first - second‖ := by
    have estimate :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun outerParameter =>
          (outerParameter •
              ∫ innerParameter in (0 : ℝ)..1,
                profile
                  (normalizedCanonicalTimeSliceCLM
                    (outerParameter * innerParameter) first)) -
            outerParameter •
              ∫ innerParameter in (0 : ℝ)..1,
                profile
                  (normalizedCanonicalTimeSliceCLM
                    (outerParameter * innerParameter) second))
        (C := ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
          ‖first - second‖)
        (fun outerParameter outer_mem => by
          have outer_mem' : outerParameter ∈ Icc (0 : ℝ) 1 := by
            have actual := uIoc_subset_uIcc outer_mem
            simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
          rw [← smul_sub]
          rw [← intervalIntegral.integral_sub
            (innerIntervalIntegrable first_mem outer_mem')
            (innerIntervalIntegrable second_mem outer_mem')]
          have innerBound :
              ‖∫ innerParameter in (0 : ℝ)..1,
                  profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) first) -
                    profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) second)‖
                ≤ ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                    ‖first - second‖ := by
            have estimateInner :=
              intervalIntegral.norm_integral_le_of_norm_le_const
                (a := (0 : ℝ)) (b := (1 : ℝ))
                (f := fun innerParameter =>
                  profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) first) -
                    profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) second))
                (C := ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                  ‖first - second‖)
                (fun innerParameter inner_mem => by
                  have inner_mem' : innerParameter ∈ Icc (0 : ℝ) 1 := by
                    have actual := uIoc_subset_uIcc inner_mem
                    simpa [uIcc_of_le
                      (by norm_num : (0 : ℝ) ≤ 1)] using actual
                  have product_mem :
                      outerParameter * innerParameter ∈ Icc (0 : ℝ) 1 := by
                    constructor
                    · exact mul_nonneg outer_mem'.1 inner_mem'.1
                    · exact mul_le_one₀ outer_mem'.2 inner_mem'.1
                        inner_mem'.2
                  calc
                    ‖profile
                          (normalizedCanonicalTimeSliceCLM
                            (outerParameter * innerParameter) first) -
                        profile
                          (normalizedCanonicalTimeSliceCLM
                            (outerParameter * innerParameter) second)‖
                        ≤ (K : ℝ) *
                            ‖normalizedCanonicalTimeSliceCLM
                                (outerParameter * innerParameter) first -
                              normalizedCanonicalTimeSliceCLM
                                (outerParameter * innerParameter) second‖ :=
                      profileLipschitz.norm_sub_le
                        (mapsTo first first_mem outerParameter outer_mem'
                          innerParameter inner_mem')
                        (mapsTo second second_mem outerParameter outer_mem'
                          innerParameter inner_mem')
                    _ = (K : ℝ) *
                          ‖normalizedCanonicalTimeSliceCLM
                              (outerParameter * innerParameter)
                              (first - second)‖ := by
                      rw [map_sub]
                    _ ≤ (K : ℝ) *
                          (normalizedCanonicalTimeSliceBound *
                            ‖first - second‖) := by
                      apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
                      exact
                        (normalizedCanonicalTimeSliceCLM
                            (outerParameter * innerParameter)).le_opNorm
                              (first - second)
                          |>.trans
                            (mul_le_mul_of_nonneg_right
                              (normalizedCanonicalTimeSliceCLM_norm_lt_bound
                                product_mem).le
                              (norm_nonneg _))
                    _ = ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                          ‖first - second‖ := by ring)
            simpa using estimateInner
          calc
            ‖outerParameter •
                (∫ innerParameter in (0 : ℝ)..1,
                  profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) first) -
                    profile
                      (normalizedCanonicalTimeSliceCLM
                        (outerParameter * innerParameter) second))‖
                = |outerParameter| *
                    ‖∫ innerParameter in (0 : ℝ)..1,
                      profile
                          (normalizedCanonicalTimeSliceCLM
                            (outerParameter * innerParameter) first) -
                        profile
                          (normalizedCanonicalTimeSliceCLM
                            (outerParameter * innerParameter) second)‖ := by
                  rw [norm_smul, Real.norm_eq_abs]
            _ ≤ 1 * (((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                    ‖first - second‖) := by
              apply mul_le_mul (by
                simpa [abs_of_nonneg outer_mem'.1] using outer_mem'.2)
                innerBound (norm_nonneg _) (by norm_num)
            _ = ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
                    ‖first - second‖ := one_mul _)
    simpa using estimate
  change
    ‖∫ outerParameter in (0 : ℝ)..1,
        (outerParameter •
            ∫ innerParameter in (0 : ℝ)..1,
              profile
                (normalizedCanonicalTimeSliceCLM
                  (outerParameter * innerParameter) first)) -
          outerParameter •
            ∫ innerParameter in (0 : ℝ)..1,
              profile
                (normalizedCanonicalTimeSliceCLM
                  (outerParameter * innerParameter) second)‖
      ≤ ((K : ℝ) * normalizedCanonicalTimeSliceBound) *
          ‖first - second‖
  exact outerBound

private theorem clm_smul_continuousAt_hasFDerivAt_zero
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    (continuousAt : ContinuousAt field 0) :
    HasFDerivAt (fun point => L point • field point)
      (L.smulRight (field 0)) 0 := by
  have linearBound :
      (fun point : X => L point) =O[𝓝 0]
        (fun point : X => ‖point‖) :=
    (L.isBigO_id (𝓝 0)).norm_right
  have fieldRemainder :
      (fun point : X => field point - field 0) =o[𝓝 0]
        (fun _ : X => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    exact tendsto_sub_nhds_zero_iff.mpr continuousAt
  have productNormRemainder :
      (fun point : X => L point • (field point - field 0)) =o[𝓝 0]
        (fun point : X => ‖point‖) := by
    simpa only [smul_eq_mul, mul_one] using
      linearBound.smul_isLittleO fieldRemainder
  have productRemainder :
      (fun point : X => L point • (field point - field 0)) =o[𝓝 0]
        (fun point : X => point) :=
    productNormRemainder.of_norm_right
  have derivativeRemainder :
      (fun point : X =>
        (L point • field point) - (L 0 • field 0) -
          (L.smulRight (field 0)) (point - 0)) =o[𝓝 0]
        (fun point : X => point) := by
    apply productRemainder.congr_left
    intro point
    simp only [map_zero, zero_smul, sub_zero,
      ContinuousLinearMap.smulRight_apply, smul_sub]
  apply HasFDerivAt.of_isLittleO
  simpa only [sub_zero] using derivativeRemainder

private theorem quadratic_smul_hasFDerivAt_zero
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    (continuousAt : ContinuousAt field 0) :
    HasFDerivAt (fun point => (L point) ^ 2 • field point)
      (0 : X →L[ℝ] E) 0 := by
  have innerContinuous :
      ContinuousAt (fun point => L point • field point) 0 :=
    L.continuous.continuousAt.smul continuousAt
  have outer :=
    clm_smul_continuousAt_hasFDerivAt_zero L
      (fun point => L point • field point) innerContinuous
  simpa only [pow_two, smul_smul, map_zero, zero_smul,
    ContinuousLinearMap.smulRight_zero] using outer

private theorem quadratic_smul_continuousAt_fderiv_zero
    {X E : Type*}
    [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (L : X →L[ℝ] ℝ)
    (field : X → E)
    {domain : Set X}
    {A : ℝ≥0}
    (domainOpen : IsOpen domain)
    (zero_mem : (0 : X) ∈ domain)
    (fieldLipschitz : LipschitzOnWith A field domain) :
    ContinuousAt
      (fderiv ℝ (fun point => (L point) ^ 2 • field point))
      0 := by
  have domain_nhd : domain ∈ 𝓝 (0 : X) :=
    domainOpen.mem_nhds zero_mem
  have fieldContinuous : ContinuousAt field 0 :=
    fieldLipschitz.continuousOn.continuousAt domain_nhd
  have derivativeZero :
      fderiv ℝ (fun point => (L point) ^ 2 • field point) 0 =
        (0 : X →L[ℝ] E) :=
    (quadratic_smul_hasFDerivAt_zero L field fieldContinuous).fderiv
  let bound : ℝ := ‖field 0‖ + 1
  have bound_pos : 0 < bound := by
    dsimp [bound]
    positivity
  have fieldEventuallyBounded :
      ∀ᶠ point in 𝓝 (0 : X), ‖field point‖ < bound := by
    exact fieldContinuous.norm
      (Iio_mem_nhds (by simp [bound]))
  let control : X → ℝ := fun point =>
    4 * ‖L‖ ^ 2 * (A : ℝ) * ‖point‖ ^ 2 +
      3 * ‖L‖ ^ 2 * bound * ‖point‖
  have controlTends : Tendsto control (𝓝 (0 : X)) (𝓝 0) := by
    have normTends :
        Tendsto (fun point : X => ‖point‖) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, id_eq, norm_zero] using
        (continuousAt_id.norm :
          ContinuousAt (fun point : X => ‖point‖) 0)
    simpa [control] using
      (((tendsto_const_nhds.mul tendsto_const_nhds).mul
        tendsto_const_nhds).mul (normTends.pow 2)).add
        (((tendsto_const_nhds.mul tendsto_const_nhds).mul
          tendsto_const_nhds).mul normTends)
  have derivativeBound :
      ∀ᶠ point in 𝓝 (0 : X),
        ‖fderiv ℝ (fun candidate => (L candidate) ^ 2 • field candidate)
            point‖ ≤
          control point := by
    filter_upwards [domain_nhd, fieldEventuallyBounded] with
        point point_mem fieldPointBound
    by_cases pointZero : point = 0
    · subst point
      rw [derivativeZero]
      simp [control]
    · have pointNormPos : 0 < ‖point‖ := norm_pos_iff.mpr pointZero
      have normEventually :
          ∀ᶠ candidate in 𝓝 point,
            ‖candidate‖ < 2 * ‖point‖ := by
        filter_upwards [Metric.ball_mem_nhds point pointNormPos] with
            candidate candidate_mem
        rw [Metric.mem_ball, dist_eq_norm] at candidate_mem
        calc
          ‖candidate‖ =
              ‖(candidate - point) + point‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖candidate - point‖ + ‖point‖ :=
            norm_add_le _ _
          _ < ‖point‖ + ‖point‖ :=
            add_lt_add_left candidate_mem ‖point‖
          _ = 2 * ‖point‖ := by ring
      have pointDomainNhd : domain ∈ 𝓝 point :=
        domainOpen.mem_nhds point_mem
      apply norm_fderiv_le_of_lip' ℝ
      · dsimp [control]
        positivity
      · filter_upwards [normEventually, pointDomainNhd] with
          candidate candidateNorm candidate_mem
        have timeCandidate :
            |L candidate| ≤ ‖L‖ * (2 * ‖point‖) := by
          calc
            |L candidate| = ‖L candidate‖ := by
              rw [Real.norm_eq_abs]
            _ ≤ ‖L‖ * ‖candidate‖ := L.le_opNorm candidate
            _ ≤ ‖L‖ * (2 * ‖point‖) :=
              mul_le_mul_of_nonneg_left candidateNorm.le (norm_nonneg _)
        have timePoint :
            |L point| ≤ ‖L‖ * ‖point‖ := by
          calc
            |L point| = ‖L point‖ := by rw [Real.norm_eq_abs]
            _ ≤ ‖L‖ * ‖point‖ := L.le_opNorm point
        have timeDifference :
            |L candidate - L point| ≤
              ‖L‖ * ‖candidate - point‖ := by
          rw [← map_sub, ← Real.norm_eq_abs]
          exact L.le_opNorm (candidate - point)
        have fieldDifference :
            ‖field candidate - field point‖ ≤
              (A : ℝ) * ‖candidate - point‖ :=
          fieldLipschitz.norm_sub_le candidate_mem point_mem
        have fieldPointNorm : ‖field point‖ ≤ bound :=
          fieldPointBound.le
        have squareCandidate :
            |(L candidate) ^ 2| ≤
              4 * ‖L‖ ^ 2 * ‖point‖ ^ 2 := by
          rw [abs_pow]
          calc
            |L candidate| ^ 2 ≤
                (‖L‖ * (2 * ‖point‖)) ^ 2 := by
              gcongr
            _ = 4 * ‖L‖ ^ 2 * ‖point‖ ^ 2 := by ring
        have timeSum :
            |L candidate + L point| ≤
              3 * ‖L‖ * ‖point‖ := by
          calc
            |L candidate + L point| ≤
                |L candidate| + |L point| := by
              simpa only [Real.norm_eq_abs] using
                norm_add_le (L candidate) (L point)
            _ ≤ ‖L‖ * (2 * ‖point‖) +
                ‖L‖ * ‖point‖ :=
              add_le_add timeCandidate timePoint
            _ = 3 * ‖L‖ * ‖point‖ := by ring
        have squareDifference :
            |(L candidate) ^ 2 - (L point) ^ 2| ≤
              (‖L‖ * ‖candidate - point‖) *
                (3 * ‖L‖ * ‖point‖) := by
          rw [show
            (L candidate) ^ 2 - (L point) ^ 2 =
              (L candidate - L point) *
                (L candidate + L point) by ring, abs_mul]
          exact mul_le_mul timeDifference timeSum
            (abs_nonneg _) (by positivity)
        have decomposition :
            (L candidate) ^ 2 • field candidate -
                (L point) ^ 2 • field point =
              (L candidate) ^ 2 • (field candidate - field point) +
                ((L candidate) ^ 2 - (L point) ^ 2) • field point := by
          module
        rw [decomposition]
        calc
          ‖(L candidate) ^ 2 • (field candidate - field point) +
              ((L candidate) ^ 2 - (L point) ^ 2) • field point‖
              ≤ ‖(L candidate) ^ 2 •
                    (field candidate - field point)‖ +
                ‖((L candidate) ^ 2 - (L point) ^ 2) •
                    field point‖ :=
            norm_add_le _ _
          _ = |(L candidate) ^ 2| *
                  ‖field candidate - field point‖ +
                |(L candidate) ^ 2 - (L point) ^ 2| *
                  ‖field point‖ := by
            simp only [norm_smul, Real.norm_eq_abs]
          _ ≤ (4 * ‖L‖ ^ 2 * ‖point‖ ^ 2) *
                  ((A : ℝ) * ‖candidate - point‖) +
                ((‖L‖ * ‖candidate - point‖) *
                  (3 * ‖L‖ * ‖point‖)) * bound := by
            gcongr
          _ = control point * ‖candidate - point‖ := by
            dsimp [control]
            ring
  rw [ContinuousAt, derivativeZero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero'
    (Eventually.of_forall fun point => norm_nonneg _)
    derivativeBound controlTends

private theorem normalizedSecondAverage_exists_local_lipschitzOnWith
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ∃ A : ℝ≥0, ∃ domain : Set BasePoint,
      IsOpen domain ∧
        (0 : BasePoint) ∈ domain ∧
          LipschitzOnWith A
            (normalizedSecondAverage profile) domain := by
  obtain ⟨K, target, targetNhd, profileLipschitz⟩ :=
    regular.exists_lipschitzOnWith
  obtain ⟨epsilon, epsilon_pos, ballSubset⟩ :=
    Metric.mem_nhds_iff.mp targetNhd
  let radius : ℝ :=
    epsilon / normalizedCanonicalTimeSliceBound
  have radius_pos : 0 < radius := by
    exact div_pos epsilon_pos normalizedCanonicalTimeSliceBound_pos
  let domain : Set BasePoint := Metric.ball 0 radius
  have domainOpen : IsOpen domain := Metric.isOpen_ball
  have zero_mem : (0 : BasePoint) ∈ domain := by
    exact Metric.mem_ball_self radius_pos
  have mapsTo :
      ∀ point ∈ domain,
        ∀ outerParameter ∈ Icc (0 : ℝ) 1,
          ∀ innerParameter ∈ Icc (0 : ℝ) 1,
            normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter) point ∈
              target := by
    intro point point_mem outerParameter outer_mem
      innerParameter inner_mem
    have product_mem :
        outerParameter * innerParameter ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact mul_nonneg outer_mem.1 inner_mem.1
      · exact mul_le_one₀ outer_mem.2 inner_mem.1 inner_mem.2
    have point_norm_lt : ‖point‖ < radius := by
      simpa [domain, Metric.mem_ball, dist_eq_norm] using point_mem
    apply ballSubset
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    calc
      ‖normalizedCanonicalTimeSliceCLM
          (outerParameter * innerParameter) point‖
          ≤ ‖normalizedCanonicalTimeSliceCLM
                (outerParameter * innerParameter)‖ * ‖point‖ :=
        (normalizedCanonicalTimeSliceCLM
          (outerParameter * innerParameter)).le_opNorm point
      _ ≤ normalizedCanonicalTimeSliceBound * ‖point‖ :=
        mul_le_mul_of_nonneg_right
          (normalizedCanonicalTimeSliceCLM_norm_lt_bound product_mem).le
          (norm_nonneg _)
      _ < normalizedCanonicalTimeSliceBound * radius :=
        mul_lt_mul_of_pos_left point_norm_lt
          normalizedCanonicalTimeSliceBound_pos
      _ = epsilon := by
        dsimp [radius]
        field_simp [normalizedCanonicalTimeSliceBound_pos.ne']
  refine
    ⟨K * ⟨normalizedCanonicalTimeSliceBound,
        normalizedCanonicalTimeSliceBound_pos.le⟩,
      domain, domainOpen, zero_mem, ?_⟩
  exact normalizedSecondAverage_lipschitzOnWith
    profileLipschitz mapsTo

/-- Local `C¹` regularity makes the full ambient first jet of the canonical
second primitive continuous at the common occurrence.  In particular, every
spatial as well as temporal derivative tends to zero there.

This theorem analyzes the already generated source-free time primitive.  Its
only premise is regularity of the supplied action profile; no target jet,
residual, branch, or regularity receipt is fed into the producer. -/
theorem canonicalTimeSecondPrimitive_continuousAt_fderiv_zero_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    ContinuousAt
      (fderiv ℝ (canonicalTimeSecondPrimitive profile))
      0 := by
  obtain ⟨A, domain, domainOpen, zero_mem, averageLipschitz⟩ :=
    normalizedSecondAverage_exists_local_lipschitzOnWith profile regular
  have generated :=
    quadratic_smul_continuousAt_fderiv_zero
      canonicalTimeProjection
      (normalizedSecondAverage profile)
      domainOpen zero_mem averageLipschitz
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point ^ 2 •
          normalizedSecondAverage profile point) =
        canonicalTimeSecondPrimitive profile := by
    funext point
    exact (canonicalTimeSecondPrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

/-- The same local `C¹` hypothesis gives the zero ambient first derivative
itself, not merely its continuity readout. -/
theorem canonicalTimeSecondPrimitive_hasFDerivAt_zero_of_contDiffAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (regular : ContDiffAt ℝ 1 profile 0) :
    HasFDerivAt (canonicalTimeSecondPrimitive profile)
      (0 : BasePoint →L[ℝ] E) 0 := by
  obtain ⟨A, domain, domainOpen, zero_mem, averageLipschitz⟩ :=
    normalizedSecondAverage_exists_local_lipschitzOnWith profile regular
  have averageContinuous :
      ContinuousAt (normalizedSecondAverage profile) 0 :=
    averageLipschitz.continuousOn.continuousAt
      (domainOpen.mem_nhds zero_mem)
  have generated :=
    quadratic_smul_hasFDerivAt_zero canonicalTimeProjection
      (normalizedSecondAverage profile) averageContinuous
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point ^ 2 •
          normalizedSecondAverage profile point) =
        canonicalTimeSecondPrimitive profile := by
    funext point
    exact (canonicalTimeSecondPrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCanonicalTimeSecondPrimitiveAmbientFirstJetRegularity
