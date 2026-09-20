import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.MetricSpace.Thickening
import H0mework.Physics.TimePrimitive.FirstAmbientJetRegularity

/-!
# Canonical time primitive regularity on a generated segment

This module differentiates the canonical temporal primitive at an arbitrary
spacetime occurrence.  The profile is required to be `C¹` only on an open
corridor containing the actual source-to-occurrence time segment.  Compactness
of that segment generates the common neighborhood and the uniform derivative
bound used for differentiation under the interval integral.

The public mouth accepts no derivative, dominator, bound, target jet, or
regularity receipt.  It is a finite-dimensional calculus producer for an
already generated action profile.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCanonicalTimePrimitiveSegmentRegularity

open Filter MeasureTheory Metric Set
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCanonicalTimePrimitiveAmbientFirstJetRegularity
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual

open scoped ContDiff Interval NNReal Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- The fixed-parameter linear map from a spacetime point to the point on its
canonical source-to-occurrence time segment. -/
def canonicalNormalizedTimeSlice
    (parameter : ℝ) : BasePoint →L[ℝ] BasePoint :=
  parameter •
      canonicalTimeProjection.smulRight
        (coordinateDirection canonicalLorentzianTimeDirection) +
    canonicalSpatialInclusion.comp canonicalSpatialProjection

private theorem canonical_time_single
    (time : ℝ) :
    EuclideanSpace.single canonicalLorentzianTimeDirection time =
      time • coordinateDirection canonicalLorentzianTimeDirection := by
  ext direction
  fin_cases direction <;>
    simp [coordinateDirection, canonicalLorentzianTimeDirection]

theorem canonicalNormalizedTimeSlice_apply
    (parameter : ℝ) (point : BasePoint) :
    canonicalNormalizedTimeSlice parameter point =
      canonicalCauchySlicePoint
        (canonicalTimeProjection point * parameter)
        (canonicalSpatialProjection point) := by
  rw [canonicalCauchySlicePoint_eq_const_add_inclusion,
    canonical_time_single]
  simp only [canonicalNormalizedTimeSlice, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    smul_smul]
  rw [mul_comm parameter]

private def canonicalNormalizedTimeSliceBound : ℝ :=
  ‖canonicalTimeProjection.smulRight
      (coordinateDirection canonicalLorentzianTimeDirection)‖ +
    ‖canonicalSpatialInclusion.comp canonicalSpatialProjection‖ + 1

private theorem canonicalNormalizedTimeSliceBound_pos :
    0 < canonicalNormalizedTimeSliceBound := by
  unfold canonicalNormalizedTimeSliceBound
  positivity

private theorem canonicalNormalizedTimeSlice_norm_lt_bound
    {parameter : ℝ} (parameter_mem : parameter ∈ Icc (0 : ℝ) 1) :
    ‖canonicalNormalizedTimeSlice parameter‖ <
      canonicalNormalizedTimeSliceBound := by
  unfold canonicalNormalizedTimeSlice canonicalNormalizedTimeSliceBound
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

/-- The compact canonical segment from the distinguished zero slice to an
arbitrary occurrence. -/
def canonicalTimeSegment (contact : BasePoint) : Set BasePoint :=
  (fun parameter => canonicalNormalizedTimeSlice parameter contact) ''
    Icc (0 : ℝ) 1

theorem canonicalTimeSegment_isCompact
    (contact : BasePoint) :
    IsCompact (canonicalTimeSegment contact) := by
  have sliceContinuous : Continuous fun parameter : ℝ =>
      canonicalNormalizedTimeSlice parameter contact := by
    unfold canonicalNormalizedTimeSlice
    fun_prop
  exact isCompact_Icc.image sliceContinuous

/-! ## Fixed-interval parameter calculus -/

def fixedIntervalParameterIntegral
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (family : BasePoint × ℝ → E)
    (point : BasePoint) : E :=
  ∫ parameter in (0 : ℝ)..1, family (point, parameter)

def fixedIntervalParameterFDeriv
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (family : BasePoint × ℝ → E)
    (pair : BasePoint × ℝ) : BasePoint →L[ℝ] E :=
  (fderiv ℝ family pair).comp
    (ContinuousLinearMap.inl ℝ BasePoint ℝ)

private theorem
    fixedIntervalParameterIntegral_eventually_hasFDerivAt_of_contDiffOn_graph
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (family : BasePoint × ℝ → E)
    (corridor : Set (BasePoint × ℝ))
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ 1 family corridor)
    (contact : BasePoint)
    (graphSubset :
      ({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1 ⊆ corridor) :
    ∀ᶠ point in 𝓝 contact,
      HasFDerivAt (fixedIntervalParameterIntegral family)
        (∫ parameter in (0 : ℝ)..1,
          fixedIntervalParameterFDeriv family (point, parameter)) point := by
  let fullDerivative :
      BasePoint × ℝ → (BasePoint × ℝ →L[ℝ] E) := fderiv ℝ family
  have derivativeContinuous : ContinuousOn fullDerivative corridor := by
    simpa [fullDerivative] using
      regular.continuousOn_fderiv_of_isOpen corridorOpen (by norm_num)
  have graphCompact : IsCompact
      (({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_singleton.prod isCompact_Icc
  obtain ⟨ambientNeighborhood, graphAmbientNeighborhood,
      ambientNeighborhoodOpen, derivativeImageBounded⟩ :=
    exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn
      graphCompact graphSubset derivativeContinuous
  let neighborhood := ambientNeighborhood ∩ corridor
  have graphNeighborhood :
      ({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1 ⊆ neighborhood := by
    intro pair pairMem
    exact ⟨graphAmbientNeighborhood pairMem, graphSubset pairMem⟩
  have neighborhoodOpen : IsOpen neighborhood :=
    ambientNeighborhoodOpen.inter corridorOpen
  obtain ⟨epsilon, epsilon_pos, thickeningSubset⟩ :
      ∃ epsilon : ℝ, 0 < epsilon ∧
        thickening epsilon
            (({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1) ⊆
          neighborhood :=
    graphCompact.exists_thickening_subset_open neighborhoodOpen
      graphNeighborhood
  let domain : Set BasePoint := ball contact epsilon
  have domainOpen : IsOpen domain := isOpen_ball
  have contactMem : contact ∈ domain := mem_ball_self epsilon_pos
  have mapsToNeighborhood :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          (point, parameter) ∈ neighborhood := by
    intro point pointMem parameter parameterMem
    apply thickeningSubset
    apply mem_thickening_iff.mpr
    refine ⟨(contact, parameter), ?_, ?_⟩
    · exact ⟨rfl, parameterMem⟩
    · rw [Prod.dist_eq]
      simpa [domain] using pointMem
  have mapsToCorridor :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          (point, parameter) ∈ corridor := by
    intro point pointMem parameter parameterMem
    exact (mapsToNeighborhood point pointMem parameter parameterMem).2
  obtain ⟨derivativeBound, derivativeBound_pos, derivativeImageSubset⟩ :
      ∃ derivativeBound : ℝ, 0 < derivativeBound ∧
        fullDerivative '' neighborhood ⊆
          closedBall (0 : BasePoint × ℝ →L[ℝ] E) derivativeBound :=
    derivativeImageBounded.subset_closedBall_lt 0 0
  let parameterAxis : BasePoint →L[ℝ] BasePoint × ℝ :=
    ContinuousLinearMap.inl ℝ BasePoint ℝ
  let bound : ℝ := derivativeBound * ‖parameterAxis‖
  have functionIntervalIntegrable
      (point : BasePoint) (pointMem : point ∈ domain) :
      IntervalIntegrable (fun parameter : ℝ => family (point, parameter))
        volume 0 1 := by
    have sectionContinuous : ContinuousOn
        (fun parameter : ℝ => family (point, parameter))
        (Icc (0 : ℝ) 1) :=
      regular.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (mapsToCorridor point pointMem)
    exact sectionContinuous.intervalIntegrable_of_Icc (by norm_num)
  have derivativeIntervalIntegrable
      (point : BasePoint) (pointMem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter : ℝ =>
          fixedIntervalParameterFDeriv family (point, parameter))
        volume 0 1 := by
    have sectionContinuous : ContinuousOn
        (fun parameter : ℝ => fullDerivative (point, parameter))
        (Icc (0 : ℝ) 1) :=
      derivativeContinuous.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (mapsToCorridor point pointMem)
    have restrictedContinuous : ContinuousOn
        (fun parameter : ℝ =>
          (fullDerivative (point, parameter)).comp parameterAxis)
        (Icc (0 : ℝ) 1) :=
      sectionContinuous.clm_comp continuousOn_const
    simpa [fixedIntervalParameterFDeriv, fullDerivative, parameterAxis] using
      restrictedContinuous.intervalIntegrable_of_Icc (by norm_num)
  have derivativeNormBound
      (point : BasePoint) (pointMem : point ∈ domain)
      (parameter : ℝ) (parameterMem : parameter ∈ Icc (0 : ℝ) 1) :
      ‖fixedIntervalParameterFDeriv family (point, parameter)‖ ≤ bound := by
    have derivativeMem : fullDerivative (point, parameter) ∈
        closedBall (0 : BasePoint × ℝ →L[ℝ] E) derivativeBound :=
      derivativeImageSubset
        (mem_image_of_mem fullDerivative
          (mapsToNeighborhood point pointMem parameter parameterMem))
    have derivativeNorm : ‖fullDerivative (point, parameter)‖ ≤
        derivativeBound := by
      simpa only [mem_closedBall_zero_iff] using derivativeMem
    calc
      ‖fixedIntervalParameterFDeriv family (point, parameter)‖ =
          ‖(fullDerivative (point, parameter)).comp parameterAxis‖ := rfl
      _ ≤ ‖fullDerivative (point, parameter)‖ * ‖parameterAxis‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ derivativeBound * ‖parameterAxis‖ :=
        mul_le_mul_of_nonneg_right derivativeNorm (norm_nonneg _)
      _ = bound := rfl
  filter_upwards [domainOpen.mem_nhds contactMem] with point pointMem
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume)
    (s := domain)
    (F := fun candidate parameter => family (candidate, parameter))
    (F' := fun candidate parameter =>
      fixedIntervalParameterFDeriv family (candidate, parameter))
    (bound := fun _ => bound)
  · exact domainOpen.mem_nhds pointMem
  · filter_upwards [domainOpen.mem_nhds pointMem] with candidate candidateMem
    exact (functionIntervalIntegrable candidate candidateMem).def'
      |>.aestronglyMeasurable
  · exact functionIntervalIntegrable point pointMem
  · exact (derivativeIntervalIntegrable point pointMem).def'
      |>.aestronglyMeasurable
  · filter_upwards [] with parameter parameterMem
    intro candidate candidateMem
    have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
      have actual := uIoc_subset_uIcc parameterMem
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    exact derivativeNormBound candidate candidateMem parameter parameterMem'
  · exact intervalIntegrable_const
  · filter_upwards [] with parameter parameterMem
    intro candidate candidateMem
    have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
      have actual := uIoc_subset_uIcc parameterMem
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
    have familyDerivative :=
      ((regular.differentiableOn (by norm_num)).differentiableAt
        (corridorOpen.mem_nhds
          (mapsToCorridor candidate candidateMem parameter parameterMem'))
        ).hasFDerivAt
    have parameterSection : HasFDerivAt
        (fun candidate : BasePoint => family (candidate, parameter))
        ((fderiv ℝ family (candidate, parameter)).comp parameterAxis)
        candidate :=
      familyDerivative.comp candidate
        (HasFDerivAt.prodMk
          (hasFDerivAt_id (x := candidate))
          (hasFDerivAt_const (x := candidate) (c := parameter)))
    simpa [fixedIntervalParameterFDeriv, parameterAxis] using
      parameterSection

/-- Fixed finite-order differentiation under the canonical parameter
integral.  One additional derivative on the jointly regular integrand pays
for the internally generated dominated-convergence bound; no derivative or
bound is accepted at the theorem mouth. -/
theorem fixedIntervalParameterIntegral_contDiffAt_of_contDiffOn_graph
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (order : ℕ)
    (family : BasePoint × ℝ → E)
    (corridor : Set (BasePoint × ℝ))
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ (order + 1) family corridor)
    (contact : BasePoint)
    (graphSubset :
      ({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1 ⊆ corridor) :
    ContDiffAt ℝ order (fixedIntervalParameterIntegral family) contact := by
  induction order generalizing E family corridor contact with
  | zero =>
      have eventuallyDerivative :=
        fixedIntervalParameterIntegral_eventually_hasFDerivAt_of_contDiffOn_graph
          family corridor corridorOpen (by simpa using regular) contact
            graphSubset
      obtain ⟨domain, domainMem, derivativeOnDomain⟩ :=
        Filter.eventually_iff_exists_mem.mp eventuallyDerivative
      change ContDiffAt ℝ 0 (fixedIntervalParameterIntegral family) contact
      rw [contDiffAt_zero]
      refine ⟨domain, domainMem, ?_⟩
      intro point pointMem
      exact (derivativeOnDomain point pointMem).continuousAt.continuousWithinAt
  | succ order inductionHypothesis =>
      have regularOne : ContDiffOn ℝ 1 family corridor :=
        regular.one_of_succ
      have eventuallyDerivative :=
        fixedIntervalParameterIntegral_eventually_hasFDerivAt_of_contDiffOn_graph
          family corridor corridorOpen regularOne contact graphSubset
      let parameterAxis : BasePoint →L[ℝ] BasePoint × ℝ :=
        ContinuousLinearMap.inl ℝ BasePoint ℝ
      let restrictDerivative :
          (BasePoint × ℝ →L[ℝ] E) →L[ℝ] (BasePoint →L[ℝ] E) :=
        (ContinuousLinearMap.compL ℝ BasePoint (BasePoint × ℝ) E).flip
          parameterAxis
      have fullDerivativeRegular : ContDiffOn ℝ (order + 1)
          (fderiv ℝ family) corridor := by
        apply regular.fderiv_of_isOpen corridorOpen
        exact le_rfl
      have partialDerivativeRegular : ContDiffOn ℝ (order + 1)
          (fixedIntervalParameterFDeriv family) corridor := by
        have generated :=
          restrictDerivative.contDiff.comp_contDiffOn fullDerivativeRegular
        change ContDiffOn ℝ (order + 1)
          (fun point =>
            (fderiv ℝ family point).comp
              (ContinuousLinearMap.inl ℝ BasePoint ℝ)) corridor
        simpa [restrictDerivative, parameterAxis, Function.comp_def] using
          generated
      have integratedDerivativeRegular : ContDiffAt ℝ order
          (fixedIntervalParameterIntegral
            (fixedIntervalParameterFDeriv family)) contact :=
        inductionHypothesis
          (family := fixedIntervalParameterFDeriv family)
          (corridor := corridor)
          corridorOpen partialDerivativeRegular contact graphSubset
      rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
      refine ⟨fixedIntervalParameterIntegral
        (fixedIntervalParameterFDeriv family), ?_,
          integratedDerivativeRegular⟩
      exact Filter.eventually_iff_exists_mem.mp (by
        simpa [fixedIntervalParameterIntegral] using eventuallyDerivative)

private def normalizedFirstAverage
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) : E :=
  ∫ parameter in (0 : ℝ)..1,
    profile (canonicalNormalizedTimeSlice parameter point)

private theorem canonicalTimePrimitive_scaleIdentity
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (point : BasePoint) :
    canonicalTimePrimitive profile point =
      canonicalTimeProjection point • normalizedFirstAverage profile point := by
  unfold canonicalTimePrimitive normalizedFirstAverage
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  have scaled :=
    intervalIntegral.smul_integral_comp_mul_left
      (f := fun candidateTime =>
        profile (canonicalCauchySlicePoint candidateTime space))
      (a := (0 : ℝ)) (b := (1 : ℝ)) time
  simpa only [mul_zero, mul_one, time, space,
    canonicalNormalizedTimeSlice_apply] using scaled.symm

private theorem canonicalNormalizedTimeSlice_joint_contDiff :
    ContDiff ℝ ∞ fun pair : BasePoint × ℝ =>
      canonicalNormalizedTimeSlice pair.2 pair.1 := by
  unfold canonicalNormalizedTimeSlice
  fun_prop

private theorem canonicalNormalizedTimeSlice_joint_continuous :
    Continuous fun pair : BasePoint × ℝ =>
      canonicalNormalizedTimeSlice pair.2 pair.1 := by
  exact canonicalNormalizedTimeSlice_joint_contDiff.continuous

/-- Points whose complete canonical source segment lies in a given corridor.
For an open corridor this is itself open; compactness of the parameter
interval generates the uniform tube. -/
def canonicalTimeSegmentDomain (corridor : Set BasePoint) : Set BasePoint :=
  { point | canonicalTimeSegment point ⊆ corridor }

theorem canonicalTimeSegmentDomain_isOpen
    {corridor : Set BasePoint}
    (corridorOpen : IsOpen corridor) :
    IsOpen (canonicalTimeSegmentDomain corridor) := by
  rw [isOpen_iff_mem_nhds]
  intro contact contactMem
  have segmentCompact := canonicalTimeSegment_isCompact contact
  obtain ⟨epsilon, epsilon_pos, thickeningSubset⟩ :
      ∃ epsilon : ℝ, 0 < epsilon ∧
        thickening epsilon (canonicalTimeSegment contact) ⊆ corridor :=
    segmentCompact.exists_thickening_subset_open corridorOpen contactMem
  let radius := epsilon / canonicalNormalizedTimeSliceBound
  have radius_pos : 0 < radius :=
    div_pos epsilon_pos canonicalNormalizedTimeSliceBound_pos
  refine mem_of_superset (ball_mem_nhds contact radius_pos) ?_
  intro point pointMem
  intro segmentPoint segmentPointMem
  rcases segmentPointMem with ⟨parameter, parameterMem, rfl⟩
  apply thickeningSubset
  apply mem_thickening_iff.mpr
  refine ⟨canonicalNormalizedTimeSlice parameter contact, ?_, ?_⟩
  · exact ⟨parameter, parameterMem, rfl⟩
  · have pointDistance : dist point contact < radius := pointMem
    have differenceEq :
        canonicalNormalizedTimeSlice parameter point -
            canonicalNormalizedTimeSlice parameter contact =
          canonicalNormalizedTimeSlice parameter (point - contact) := by
      rw [map_sub]
    rw [dist_eq_norm, differenceEq]
    calc
      ‖canonicalNormalizedTimeSlice parameter (point - contact)‖
          ≤ ‖canonicalNormalizedTimeSlice parameter‖ * ‖point - contact‖ :=
        (canonicalNormalizedTimeSlice parameter).le_opNorm (point - contact)
      _ ≤ canonicalNormalizedTimeSliceBound * ‖point - contact‖ :=
        mul_le_mul_of_nonneg_right
          (canonicalNormalizedTimeSlice_norm_lt_bound parameterMem).le
          (norm_nonneg _)
      _ < canonicalNormalizedTimeSliceBound * radius :=
        mul_lt_mul_of_pos_left
          (by simpa [dist_eq_norm] using pointDistance)
          canonicalNormalizedTimeSliceBound_pos
      _ = epsilon := by
        dsimp [radius]
        field_simp [canonicalNormalizedTimeSliceBound_pos.ne']

theorem canonicalTimeSegment_subset_of_mem_segment
    {contact point : BasePoint}
    (pointMem : point ∈ canonicalTimeSegment contact) :
    canonicalTimeSegment point ⊆ canonicalTimeSegment contact := by
  rcases pointMem with ⟨outer, outerMem, rfl⟩
  rintro segmentPoint ⟨inner, innerMem, rfl⟩
  refine ⟨outer * inner, ?_, ?_⟩
  · exact ⟨mul_nonneg outerMem.1 innerMem.1,
      mul_le_one₀ outerMem.2 innerMem.1 innerMem.2⟩
  · change
      canonicalNormalizedTimeSlice (outer * inner) contact =
        canonicalNormalizedTimeSlice inner
          (canonicalNormalizedTimeSlice outer contact)
    rw [canonicalNormalizedTimeSlice_apply (outer * inner) contact,
      canonicalNormalizedTimeSlice_apply inner
        (canonicalNormalizedTimeSlice outer contact),
      canonicalNormalizedTimeSlice_apply outer contact]
    simp only [canonicalTimeProjection_slice,
      canonicalSpatialProjection_slice]
    apply congrArg₂ canonicalCauchySlicePoint
    · ring
    · rfl

private theorem normalizedFirstAverage_eq_fixedIntervalParameterIntegral
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E) :
    normalizedFirstAverage profile =
      fixedIntervalParameterIntegral
        (fun pair : BasePoint × ℝ =>
          profile (canonicalNormalizedTimeSlice pair.2 pair.1)) := by
  rfl

/-- Finite-order segment-local regularity for the normalized canonical
average.  The single derivative loss is explicit and fixed; it pays for the
internally generated parameter-integral bound. -/
theorem normalizedFirstAverage_contDiffAt_of_contDiffOn_segment_finite
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (order : ℕ)
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ (order + 1) profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ order (normalizedFirstAverage profile) contact := by
  let jointSlice : BasePoint × ℝ → BasePoint := fun pair =>
    canonicalNormalizedTimeSlice pair.2 pair.1
  let parameterCorridor : Set (BasePoint × ℝ) := jointSlice ⁻¹' corridor
  have parameterCorridorOpen : IsOpen parameterCorridor :=
    canonicalNormalizedTimeSlice_joint_continuous.isOpen_preimage
      corridor corridorOpen
  have jointSliceRegular : ContDiff ℝ (order + 1) jointSlice := by
    dsimp only [jointSlice]
    unfold canonicalNormalizedTimeSlice
    fun_prop
  have jointRegular : ContDiffOn ℝ (order + 1)
      (fun pair : BasePoint × ℝ => profile (jointSlice pair))
      parameterCorridor := by
    apply regular.comp jointSliceRegular.contDiffOn
    intro pair pairMem
    exact pairMem
  have graphSubset :
      ({contact} : Set BasePoint) ×ˢ Icc (0 : ℝ) 1 ⊆
        parameterCorridor := by
    rintro ⟨point, parameter⟩ ⟨pointEq, parameterMem⟩
    have pointEq' : point = contact := by
      simpa only [mem_singleton_iff] using pointEq
    subst point
    exact segmentSubset ⟨parameter, parameterMem, rfl⟩
  rw [normalizedFirstAverage_eq_fixedIntervalParameterIntegral]
  exact fixedIntervalParameterIntegral_contDiffAt_of_contDiffOn_graph
    order _ parameterCorridor parameterCorridorOpen jointRegular contact
      graphSubset

/-- A finite-order canonical first primitive on an actual open segment
corridor.  The profile supplies exactly one additional finite derivative. -/
theorem canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (order : ℕ)
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ (order + 1) profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ order (canonicalTimePrimitive profile) contact := by
  have generated :=
    (canonicalTimeProjection.contDiff.contDiffAt.of_le le_top).smul
      (normalizedFirstAverage_contDiffAt_of_contDiffOn_segment_finite
        order profile corridor corridorOpen regular contact segmentSubset)
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point • normalizedFirstAverage profile point) =
        canonicalTimePrimitive profile := by
    funext point
    exact (canonicalTimePrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

private theorem canonicalTimeSecondPrimitive_eq_iterated
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
  simp only [canonicalTimeProjection_slice,
    canonicalSpatialProjection_slice]

/-- A finite-order canonical second primitive on the actual source segment.
The nested segment remains inside the original segment, so two applications
of the finite parameter calculus consume exactly two additional profile
derivatives and no supplied jet. -/
theorem canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (order : ℕ)
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ (order + 2) profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ order (canonicalTimeSecondPrimitive profile) contact := by
  let segmentDomain := canonicalTimeSegmentDomain corridor
  have segmentDomainOpen : IsOpen segmentDomain :=
    canonicalTimeSegmentDomain_isOpen corridorOpen
  have firstPrimitiveRegular : ContDiffOn ℝ (order + 1)
      (canonicalTimePrimitive profile) segmentDomain := by
    intro point pointMem
    exact
      (canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
        (order + 1) profile corridor corridorOpen
        (by
          convert regular using 1 <;>
            norm_num [Nat.cast_add, add_assoc]) point pointMem
        ).contDiffWithinAt
  have contactSegmentInDomain : canonicalTimeSegment contact ⊆
      segmentDomain := by
    intro point pointMem
    exact (canonicalTimeSegment_subset_of_mem_segment pointMem).trans
      segmentSubset
  rw [canonicalTimeSecondPrimitive_eq_iterated]
  exact canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment_finite
    order (canonicalTimePrimitive profile) segmentDomain segmentDomainOpen
      firstPrimitiveRegular contact contactSegmentInDomain

/-- The concrete scalar regularity budget used by the fixed P506/L0 action:
a segment-local `C⁵` acceleration generates a `C³` second primitive. -/
theorem canonicalTimeSecondPrimitive_contDiffAt_three_of_contDiffOn_five_segment
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ 5 profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ 3 (canonicalTimeSecondPrimitive profile) contact := by
  exact canonicalTimeSecondPrimitive_contDiffAt_of_contDiffOn_segment_finite
    3 profile corridor corridorOpen (by
      convert regular using 1 <;> norm_num) contact
      segmentSubset

private theorem normalizedFirstAverage_contDiffAt_of_contDiffOn_segment
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ 1 profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ 1 (normalizedFirstAverage profile) contact := by
  let profileDerivative : BasePoint → BasePoint →L[ℝ] E := fderiv ℝ profile
  have derivativeContinuous : ContinuousOn profileDerivative corridor := by
    simpa [profileDerivative] using
      regular.continuousOn_fderiv_of_isOpen corridorOpen (by norm_num)
  have segmentCompact := canonicalTimeSegment_isCompact contact
  obtain ⟨ambientNeighborhood, segmentAmbientNeighborhood,
      ambientNeighborhoodOpen, derivativeImageBounded⟩ :=
    exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn
      segmentCompact segmentSubset derivativeContinuous
  let neighborhood := ambientNeighborhood ∩ corridor
  have segmentNeighborhood : canonicalTimeSegment contact ⊆ neighborhood := by
    intro point pointMem
    exact ⟨segmentAmbientNeighborhood pointMem, segmentSubset pointMem⟩
  have neighborhoodOpen : IsOpen neighborhood :=
    ambientNeighborhoodOpen.inter corridorOpen
  obtain ⟨epsilon, epsilon_pos, thickeningSubset⟩ :
      ∃ epsilon : ℝ, 0 < epsilon ∧
        thickening epsilon (canonicalTimeSegment contact) ⊆ neighborhood :=
    segmentCompact.exists_thickening_subset_open neighborhoodOpen
      segmentNeighborhood
  let radius := epsilon / canonicalNormalizedTimeSliceBound
  have radius_pos : 0 < radius :=
    div_pos epsilon_pos canonicalNormalizedTimeSliceBound_pos
  let domain : Set BasePoint := ball contact radius
  have domainOpen : IsOpen domain := isOpen_ball
  have contactMem : contact ∈ domain := mem_ball_self radius_pos
  have mapsToNeighborhood :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          canonicalNormalizedTimeSlice parameter point ∈ neighborhood := by
    intro point pointMem parameter parameterMem
    apply thickeningSubset
    apply mem_thickening_iff.mpr
    refine ⟨canonicalNormalizedTimeSlice parameter contact, ?_, ?_⟩
    · exact ⟨parameter, parameterMem, rfl⟩
    · have pointDistance : dist point contact < radius := pointMem
      have differenceEq :
          canonicalNormalizedTimeSlice parameter point -
              canonicalNormalizedTimeSlice parameter contact =
            canonicalNormalizedTimeSlice parameter (point - contact) := by
        rw [map_sub]
      rw [dist_eq_norm, differenceEq]
      calc
        ‖canonicalNormalizedTimeSlice parameter (point - contact)‖
            ≤ ‖canonicalNormalizedTimeSlice parameter‖ * ‖point - contact‖ :=
          (canonicalNormalizedTimeSlice parameter).le_opNorm _
        _ ≤ canonicalNormalizedTimeSliceBound * ‖point - contact‖ :=
          mul_le_mul_of_nonneg_right
            (canonicalNormalizedTimeSlice_norm_lt_bound parameterMem).le
            (norm_nonneg _)
        _ < canonicalNormalizedTimeSliceBound * radius :=
          mul_lt_mul_of_pos_left
            (by simpa [dist_eq_norm] using pointDistance)
            canonicalNormalizedTimeSliceBound_pos
        _ = epsilon := by
          dsimp [radius]
          field_simp [canonicalNormalizedTimeSliceBound_pos.ne']
  have mapsToCorridor :
      ∀ point ∈ domain,
        ∀ parameter ∈ Icc (0 : ℝ) 1,
          canonicalNormalizedTimeSlice parameter point ∈ corridor := by
    intro point pointMem parameter parameterMem
    exact (mapsToNeighborhood point pointMem parameter parameterMem).2
  obtain ⟨derivativeBound, derivativeBound_pos, derivativeImageSubset⟩ :
      ∃ derivativeBound : ℝ, 0 < derivativeBound ∧
        profileDerivative '' neighborhood ⊆
          closedBall (0 : BasePoint →L[ℝ] E) derivativeBound :=
    derivativeImageBounded.subset_closedBall_lt 0 0
  let B : ℝ≥0 :=
    ⟨canonicalNormalizedTimeSliceBound,
      canonicalNormalizedTimeSliceBound_pos.le⟩
  let C : ℝ := derivativeBound * B
  let averageDerivative : BasePoint → BasePoint →L[ℝ] E := fun point =>
    ∫ parameter in (0 : ℝ)..1,
      (profileDerivative
          (canonicalNormalizedTimeSlice parameter point)).comp
        (canonicalNormalizedTimeSlice parameter)
  have sliceContinuous (point : BasePoint) :
      Continuous fun parameter : ℝ =>
        canonicalNormalizedTimeSlice parameter point := by
    unfold canonicalNormalizedTimeSlice
    fun_prop
  have sliceCLMContinuous :
      Continuous canonicalNormalizedTimeSlice := by
    unfold canonicalNormalizedTimeSlice
    fun_prop
  have functionIntervalIntegrable
      (point : BasePoint) (pointMem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter : ℝ =>
          profile (canonicalNormalizedTimeSlice parameter point))
        volume 0 1 := by
    have composed : ContinuousOn
        (fun parameter : ℝ =>
          profile (canonicalNormalizedTimeSlice parameter point))
        (Icc (0 : ℝ) 1) :=
      regular.continuousOn.comp
        (sliceContinuous point).continuousOn
        (mapsToCorridor point pointMem)
    exact composed.intervalIntegrable_of_Icc (by norm_num)
  have derivativeIntervalIntegrable
      (point : BasePoint) (pointMem : point ∈ domain) :
      IntervalIntegrable
        (fun parameter : ℝ =>
          (profileDerivative
              (canonicalNormalizedTimeSlice parameter point)).comp
            (canonicalNormalizedTimeSlice parameter))
        volume 0 1 := by
    have alongSlice : ContinuousOn
        (fun parameter : ℝ =>
          profileDerivative
            (canonicalNormalizedTimeSlice parameter point))
        (Icc (0 : ℝ) 1) :=
      derivativeContinuous.comp
        (sliceContinuous point).continuousOn
        (mapsToCorridor point pointMem)
    have composed : ContinuousOn
        (fun parameter : ℝ =>
          (profileDerivative
              (canonicalNormalizedTimeSlice parameter point)).comp
            (canonicalNormalizedTimeSlice parameter))
        (Icc (0 : ℝ) 1) :=
      alongSlice.clm_comp sliceCLMContinuous.continuousOn
    exact composed.intervalIntegrable_of_Icc (by norm_num)
  have derivativeNormBound
      (point : BasePoint) (pointMem : point ∈ domain)
      (parameter : ℝ) (parameterMem : parameter ∈ Icc (0 : ℝ) 1) :
      ‖(profileDerivative
            (canonicalNormalizedTimeSlice parameter point)).comp
          (canonicalNormalizedTimeSlice parameter)‖ ≤ C := by
    have derivativeMem : profileDerivative
        (canonicalNormalizedTimeSlice parameter point) ∈
        closedBall (0 : BasePoint →L[ℝ] E) derivativeBound :=
      derivativeImageSubset
        (mem_image_of_mem profileDerivative
          (mapsToNeighborhood point pointMem parameter parameterMem))
    have derivativeNorm :
        ‖profileDerivative
            (canonicalNormalizedTimeSlice parameter point)‖ ≤
          derivativeBound := by
      simpa only [mem_closedBall_zero_iff] using derivativeMem
    calc
      ‖(profileDerivative
            (canonicalNormalizedTimeSlice parameter point)).comp
          (canonicalNormalizedTimeSlice parameter)‖
          ≤ ‖profileDerivative
              (canonicalNormalizedTimeSlice parameter point)‖ *
              ‖canonicalNormalizedTimeSlice parameter‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ derivativeBound * canonicalNormalizedTimeSliceBound := by
        exact mul_le_mul derivativeNorm
          (canonicalNormalizedTimeSlice_norm_lt_bound parameterMem).le
          (norm_nonneg _) derivativeBound_pos.le
      _ = C := by rfl
  have averageHasFDerivAt :
      ∀ point ∈ domain,
        HasFDerivAt (normalizedFirstAverage profile)
          (averageDerivative point) point := by
    intro point pointMem
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume)
      (s := domain)
      (F := fun candidate parameter =>
        profile (canonicalNormalizedTimeSlice parameter candidate))
      (F' := fun candidate parameter =>
        (profileDerivative
            (canonicalNormalizedTimeSlice parameter candidate)).comp
          (canonicalNormalizedTimeSlice parameter))
      (bound := fun _ => C)
    · exact domainOpen.mem_nhds pointMem
    · filter_upwards [domainOpen.mem_nhds pointMem] with candidate candidateMem
      exact (functionIntervalIntegrable candidate candidateMem).def'
        |>.aestronglyMeasurable
    · exact functionIntervalIntegrable point pointMem
    · exact (derivativeIntervalIntegrable point pointMem).def'
        |>.aestronglyMeasurable
    · filter_upwards [] with parameter parameterMem
      intro candidate candidateMem
      have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameterMem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      exact derivativeNormBound candidate candidateMem parameter parameterMem'
    · exact intervalIntegrable_const
    · filter_upwards [] with parameter parameterMem
      intro candidate candidateMem
      have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameterMem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      exact
        ((regular.differentiableOn (by norm_num)).differentiableAt
          (corridorOpen.mem_nhds
            (mapsToCorridor candidate candidateMem parameter parameterMem'))
          ).hasFDerivAt.comp candidate
            (canonicalNormalizedTimeSlice parameter).hasFDerivAt
  have averageDerivativeContinuous :
      ContinuousOn averageDerivative domain := by
    intro point pointMem
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (μ := volume)
      (bound := fun _ => C)
    · filter_upwards [self_mem_nhdsWithin] with candidate candidateMem
      exact (derivativeIntervalIntegrable candidate candidateMem).def'
        |>.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with candidate candidateMem
      filter_upwards [] with parameter parameterMem
      have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameterMem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      exact derivativeNormBound candidate candidateMem parameter parameterMem'
    · exact intervalIntegrable_const
    · filter_upwards [] with parameter parameterMem
      have parameterMem' : parameter ∈ Icc (0 : ℝ) 1 := by
        have actual := uIoc_subset_uIcc parameterMem
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using actual
      have alongDomain : ContinuousOn
          (fun candidate : BasePoint =>
            profileDerivative
              (canonicalNormalizedTimeSlice parameter candidate))
          domain :=
        derivativeContinuous.comp
          (canonicalNormalizedTimeSlice parameter).continuous.continuousOn
          (fun candidate candidateMem =>
            mapsToCorridor candidate candidateMem parameter parameterMem')
      have composed : ContinuousOn
          (fun candidate : BasePoint =>
            (profileDerivative
                (canonicalNormalizedTimeSlice parameter candidate)).comp
              (canonicalNormalizedTimeSlice parameter))
          domain :=
        alongDomain.clm_comp continuousOn_const
      exact composed point pointMem
  exact contDiffAt_one_iff.mpr
    ⟨averageDerivative, domain, domainOpen.mem_nhds contactMem,
      averageDerivativeContinuous, averageHasFDerivAt⟩

/-- A `C¹` action profile on an open corridor containing the complete
source-to-contact segment generates a `C¹` canonical first primitive at the
contact. -/
theorem canonicalTimePrimitive_contDiffAt_of_contDiffOn_segment
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (profile : BasePoint → E)
    (corridor : Set BasePoint)
    (corridorOpen : IsOpen corridor)
    (regular : ContDiffOn ℝ 1 profile corridor)
    (contact : BasePoint)
    (segmentSubset : canonicalTimeSegment contact ⊆ corridor) :
    ContDiffAt ℝ 1 (canonicalTimePrimitive profile) contact := by
  have generated :=
    canonicalTimeProjection.contDiff.contDiffAt.smul
      (normalizedFirstAverage_contDiffAt_of_contDiffOn_segment
        profile corridor corridorOpen regular contact segmentSubset)
  have primitiveEq :
      (fun point =>
        canonicalTimeProjection point • normalizedFirstAverage profile point) =
        canonicalTimePrimitive profile := by
    funext point
    exact (canonicalTimePrimitive_scaleIdentity profile point).symm
  rw [← primitiveEq]
  exact generated

end

end
  SaturationMonoid.PhysicsCore.StageNineCanonicalTimePrimitiveSegmentRegularity
