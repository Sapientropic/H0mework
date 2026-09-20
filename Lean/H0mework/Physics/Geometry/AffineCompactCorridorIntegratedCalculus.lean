import H0mework.Physics.Geometry.CompactSupportIntegrationByParts

/-!
# Dependency-light affine compact-corridor integral calculus

This module differentiates an arbitrary jointly `C^1` density family along a
compactly supported smooth affine variation.  Background subtraction makes
the increment compactly supported.  The joint Frechet derivative, its
parameter restriction, a uniform compact bound, the indicator dominator, and
the under-integral derivative are all generated internally.

The public theorem accepts only the actual density family, background,
primitive compact variation, background integrability, and an open joint
`C^1` corridor.  It does not accept a derivative, derivative integrability,
dominator, uniform bound, stress, equation, or stationarity receipt.  Both the
historical and residual-linear gravity formulations may wrap this calculus
without sharing an action law.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineAffineCompactCorridorIntegratedCalculus

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open MeasureTheory
open Filter Metric Set
open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-! ## Actual affine family and compact increment -/

def affineVariedDensity
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : BasePoint → Y)
    (parameter : ℝ) (point : BasePoint) : ℝ :=
  family point (background point + parameter • variation point)

def affineDensityIncrement
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : BasePoint → Y)
    (parameter : ℝ) (point : BasePoint) : ℝ :=
  affineVariedDensity family background variation parameter point -
    affineVariedDensity family background variation 0 point

@[simp] theorem affineDensityIncrement_zero
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y)
    (point : BasePoint) :
    affineDensityIncrement family background variation 0 point = 0 := by
  simp [affineDensityIncrement]

theorem affineDensityIncrement_eq_zero_of_variation_zero
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y)
    (parameter : ℝ) (point : BasePoint)
    (variationZero : variation point = 0) :
    affineDensityIncrement family background variation parameter point = 0 := by
  simp [affineDensityIncrement, affineVariedDensity, variationZero]

/-! ## Joint and parameter derivatives -/

def affineDensityIncrementJointFDeriv
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y) :
    ℝ × BasePoint → (ℝ × BasePoint →L[ℝ] ℝ) :=
  fderiv ℝ
    (Function.uncurry
      (affineDensityIncrement family background variation))

def affineDensityIncrementParameterFDeriv
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y)
    (parameter : ℝ) (point : BasePoint) : ℝ →L[ℝ] ℝ :=
  (affineDensityIncrementJointFDeriv family background variation
    (parameter, point)).comp (ContinuousLinearMap.inl ℝ ℝ BasePoint)

theorem affineDensityIncrement_hasFDerivAt
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint) :
    HasFDerivAt
      (fun candidate =>
        affineDensityIncrement family background variation candidate point)
      (affineDensityIncrementParameterFDeriv
        family background variation parameter point) parameter := by
  have pairMem : (parameter, point) ∈
      parameterSet ×ˢ (univ : Set BasePoint) :=
    ⟨parameterMem, mem_univ point⟩
  have pairNeighborhood : parameterSet ×ˢ (univ : Set BasePoint) ∈
      nhds (parameter, point) :=
    (parameterSetOpen.prod isOpen_univ).mem_nhds pairMem
  have jointDerivative : HasFDerivAt
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (affineDensityIncrementJointFDeriv family background variation
        (parameter, point)) (parameter, point) := by
    exact ((jointC1.differentiableOn_one
      (parameter, point) pairMem).differentiableAt
        pairNeighborhood).hasFDerivAt
  exact jointDerivative.comp parameter
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) parameter point)

theorem affineDensityIncrementParameterFDeriv_zero_of_variation_zero
    (family : BasePoint → Y → ℝ)
    (background variation : BasePoint → Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint) (variationZero : variation point = 0) :
    affineDensityIncrementParameterFDeriv
        family background variation parameter point = 0 := by
  have locallyConstant : ∀ᶠ candidate in nhds parameter,
      affineDensityIncrement family background variation candidate point =
        0 := by
    filter_upwards [] with candidate
    exact affineDensityIncrement_eq_zero_of_variation_zero
      family background variation candidate point variationZero
  have zeroDerivative : HasFDerivAt
      (fun candidate : ℝ =>
        affineDensityIncrement family background variation candidate point)
      (0 : ℝ →L[ℝ] ℝ) parameter :=
    hasFDerivAt_zero_of_eventually_const (0 : ℝ) locallyConstant
  exact (affineDensityIncrement_hasFDerivAt family background variation
    parameterSet parameterSetOpen jointC1 parameter parameterMem point).unique
      zeroDerivative

theorem affineDensityIncrementParameterFDeriv_zero_outside_support
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint)
    (pointOutside : point ∉ tsupport (variation : BasePoint → Y)) :
    affineDensityIncrementParameterFDeriv
        family background variation parameter point = 0 := by
  have variationZero : variation point = 0 := by
    apply not_ne_iff.mp
    intro variationNe
    exact pointOutside (subset_closure variationNe)
  exact affineDensityIncrementParameterFDeriv_zero_of_variation_zero
    family background variation parameterSet parameterSetOpen jointC1
      parameter parameterMem point variationZero

/-! ## Internally generated uniform bound -/

theorem exists_affineDensityIncrementParameterFDeriv_uniform_bound
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    ∃ ε C : ℝ,
      0 < ε ∧
        ball 0 ε ⊆ parameterSet ∧
        0 ≤ C ∧
        ∀ parameter point,
          ‖parameter - 0‖ < ε →
          ‖affineDensityIncrementParameterFDeriv
            family background variation parameter point‖ ≤ C := by
  let jointDerivative :=
    affineDensityIncrementJointFDeriv family background variation
  let parameterAxis : ℝ →L[ℝ] ℝ × BasePoint :=
    ContinuousLinearMap.inl ℝ ℝ BasePoint
  let supportSet := tsupport (variation : BasePoint → Y)
  have supportCompact : IsCompact supportSet := variation.compactSupport
  have jointDerivativeContinuous : ContinuousOn jointDerivative
      (parameterSet ×ˢ (univ : Set BasePoint)) := by
    simpa [jointDerivative, affineDensityIncrementJointFDeriv] using
      jointC1.continuousOn_fderiv_of_isOpen
        (parameterSetOpen.prod isOpen_univ) (by simp)
  have compactGraph : IsCompact (({0} : Set ℝ) ×ˢ supportSet) :=
    isCompact_singleton.prod supportCompact
  obtain ⟨neighborhood, graphSubset, neighborhoodOpen, imageBounded⟩ :
      ∃ neighborhood : Set (ℝ × BasePoint),
        ({0} : Set ℝ) ×ˢ supportSet ⊆ neighborhood ∧
          IsOpen neighborhood ∧
          Bornology.IsBounded (jointDerivative '' neighborhood) := by
    apply exists_isOpen_isBounded_image_of_isCompact_of_continuousOn
      compactGraph (parameterSetOpen.prod isOpen_univ)
      _ jointDerivativeContinuous
    rintro ⟨parameter, point⟩ ⟨parameterZero, pointMem⟩
    change parameter = 0 at parameterZero
    subst parameter
    exact ⟨zeroMem, mem_univ point⟩
  obtain ⟨ε₀, ε₀Positive, thickeningSubset⟩ :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        thickening ε₀ (({0} : Set ℝ) ×ˢ supportSet) ⊆ neighborhood :=
    compactGraph.exists_thickening_subset_open neighborhoodOpen graphSubset
  obtain ⟨δ, δPositive, ballSubset⟩ :
      ∃ δ : ℝ, 0 < δ ∧ ball 0 δ ⊆ parameterSet :=
    Metric.isOpen_iff.1 parameterSetOpen 0 zeroMem
  let ε := min ε₀ δ
  have εPositive : 0 < ε := lt_min ε₀Positive δPositive
  have εBallSubset : ball 0 ε ⊆ parameterSet :=
    (ball_subset_ball (min_le_right ε₀ δ)).trans ballSubset
  obtain ⟨derivativeBound, derivativeBoundPositive, imageSubset⟩ :
      ∃ derivativeBound : ℝ, 0 < derivativeBound ∧
        jointDerivative '' neighborhood ⊆
          closedBall (0 : ℝ × BasePoint →L[ℝ] ℝ) derivativeBound :=
    imageBounded.subset_closedBall_lt 0 0
  let C := derivativeBound * ‖parameterAxis‖
  refine ⟨ε, C, εPositive, εBallSubset,
    mul_nonneg derivativeBoundPositive.le (norm_nonneg _), ?_⟩
  intro parameter point parameterNear
  have parameterMem : parameter ∈ parameterSet :=
    εBallSubset (mem_ball_iff_norm.mpr (by simpa using parameterNear))
  by_cases pointMem : point ∈ supportSet
  · have pairInNeighborhood : (parameter, point) ∈ neighborhood := by
      apply thickeningSubset
      refine mem_thickening_iff.mpr ⟨(0, point), ?_, ?_⟩
      · exact ⟨rfl, pointMem⟩
      · rw [Prod.dist_eq]
        have parameterDistance : dist parameter 0 < ε₀ := by
          rw [dist_eq_norm]
          exact parameterNear.trans_le (min_le_left ε₀ δ)
        simpa [Real.dist_eq, ε₀Positive] using parameterDistance
    have fullDerivativeBound :
        ‖jointDerivative (parameter, point)‖ ≤ derivativeBound := by
      have inClosedBall : jointDerivative (parameter, point) ∈
          closedBall (0 : ℝ × BasePoint →L[ℝ] ℝ) derivativeBound :=
        imageSubset (mem_image_of_mem jointDerivative pairInNeighborhood)
      simpa only [mem_closedBall_zero_iff] using inClosedBall
    calc
      ‖affineDensityIncrementParameterFDeriv
          family background variation parameter point‖ =
          ‖(jointDerivative (parameter, point)).comp parameterAxis‖ := rfl
      _ ≤ ‖jointDerivative (parameter, point)‖ * ‖parameterAxis‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ derivativeBound * ‖parameterAxis‖ :=
        mul_le_mul_of_nonneg_right fullDerivativeBound (norm_nonneg _)
      _ = C := rfl
  · rw [affineDensityIncrementParameterFDeriv_zero_outside_support
      family background variation parameterSet parameterSetOpen jointC1
      parameter parameterMem point pointMem, norm_zero]
    exact mul_nonneg derivativeBoundPositive.le (norm_nonneg _)

/-! ## Compactness, integrability, and dominator -/

theorem affineDensityIncrement_continuous_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Continuous
      (affineDensityIncrement family background variation parameter) := by
  have sliceContinuous : Continuous
      (fun point : BasePoint => (parameter, point)) :=
    continuous_const.prodMk continuous_id
  have actual := jointC1.continuousOn.comp_continuous sliceContinuous
    (fun point : BasePoint => ⟨parameterMem, mem_univ point⟩)
  change Continuous
    (Function.uncurry (affineDensityIncrement family background variation) ∘
      fun point : BasePoint => (parameter, point))
  exact actual

theorem affineDensityIncrement_compact
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameter : ℝ) :
    HasCompactSupport
      (affineDensityIncrement family background variation parameter) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  exact affineDensityIncrement_eq_zero_of_variation_zero
    family background variation parameter point variationZero

theorem affineDensityIncrement_integrable_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Integrable
      (affineDensityIncrement family background variation parameter) :=
  (affineDensityIncrement_continuous_of_jointC1 family background variation
    parameterSet jointC1 parameter parameterMem).integrable_of_hasCompactSupport
      (affineDensityIncrement_compact
        family background variation parameter)

theorem affineDensityIncrementParameterFDeriv_continuous_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Continuous fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        family background variation parameter point := by
  have jointDerivativeContinuous : ContinuousOn
      (affineDensityIncrementJointFDeriv family background variation)
      (parameterSet ×ˢ (univ : Set BasePoint)) := by
    simpa [affineDensityIncrementJointFDeriv] using
      jointC1.continuousOn_fderiv_of_isOpen
        (parameterSetOpen.prod isOpen_univ) (by simp)
  have slicedDerivativeContinuous : Continuous fun point : BasePoint =>
      affineDensityIncrementJointFDeriv family background variation
        (parameter, point) := by
    have sliceContinuous : Continuous
        (fun point : BasePoint => (parameter, point)) :=
      continuous_const.prodMk continuous_id
    have actual := jointDerivativeContinuous.comp_continuous sliceContinuous
      (fun point : BasePoint => ⟨parameterMem, mem_univ point⟩)
    change Continuous
      (affineDensityIncrementJointFDeriv family background variation ∘
        fun point : BasePoint => (parameter, point))
    exact actual
  simpa [affineDensityIncrementParameterFDeriv] using
    slicedDerivativeContinuous.clm_comp_const
      (ContinuousLinearMap.inl ℝ ℝ BasePoint)

def affineDensityVariationDominator
    (variation : CompactlySupportedSmoothVariation Y)
    (bound : ℝ) (point : BasePoint) : ℝ :=
  indicator (tsupport (variation : BasePoint → Y))
    (fun _ => bound) point

theorem affineDensityVariationDominator_integrable
    (variation : CompactlySupportedSmoothVariation Y)
    (bound : ℝ) :
    Integrable (affineDensityVariationDominator variation bound) := by
  have supportCompact : IsCompact
      (tsupport (variation : BasePoint → Y)) := variation.compactSupport
  exact (integrableOn_const supportCompact.measure_ne_top).integrable_indicator
    supportCompact.measurableSet

theorem affineDensityIncrementParameterFDeriv_le_dominator
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (ε C : ℝ)
    (ballSubset : ball 0 ε ⊆ parameterSet)
    (uniformBound : ∀ parameter point,
      ‖parameter - 0‖ < ε →
      ‖affineDensityIncrementParameterFDeriv
        family background variation parameter point‖ ≤ C)
    (point : BasePoint) (parameter : ℝ)
    (parameterMem : parameter ∈ ball 0 ε) :
    ‖affineDensityIncrementParameterFDeriv
        family background variation parameter point‖ ≤
      affineDensityVariationDominator variation C point := by
  by_cases pointMem : point ∈ tsupport (variation : BasePoint → Y)
  · rw [affineDensityVariationDominator, indicator_of_mem pointMem]
    apply uniformBound parameter point
    simpa [mem_ball, dist_eq_norm] using parameterMem
  · rw [affineDensityIncrementParameterFDeriv_zero_outside_support
      family background variation parameterSet parameterSetOpen jointC1
      parameter (ballSubset parameterMem) point pointMem]
    simp [affineDensityVariationDominator, pointMem]

/-! ## Differentiation under the integral -/

theorem affineDensityIncrement_integral_hasFDerivAt_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    HasFDerivAt
      (fun parameter => ∫ point : BasePoint,
        affineDensityIncrement family background variation parameter point)
      (∫ point : BasePoint,
        affineDensityIncrementParameterFDeriv
          family background variation 0 point) 0 := by
  obtain ⟨ε, C, εPositive, ballSubset, _CNonnegative, uniformBound⟩ :=
    exists_affineDensityIncrementParameterFDeriv_uniform_bound
      family background variation parameterSet parameterSetOpen zeroMem jointC1
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball 0 ε)
    (F := affineDensityIncrement family background variation)
    (F' := affineDensityIncrementParameterFDeriv
      family background variation)
    (bound := affineDensityVariationDominator variation C)
  · exact ball_mem_nhds 0 εPositive
  · filter_upwards [ball_mem_nhds 0 εPositive] with parameter parameterMem
    exact (affineDensityIncrement_continuous_of_jointC1
      family background variation parameterSet jointC1 parameter
        (ballSubset parameterMem)).aestronglyMeasurable
  · exact affineDensityIncrement_integrable_of_jointC1
      family background variation parameterSet jointC1 0 zeroMem
  · exact (affineDensityIncrementParameterFDeriv_continuous_of_jointC1
      family background variation parameterSet parameterSetOpen jointC1
        0 zeroMem).aestronglyMeasurable
  · filter_upwards with point parameter parameterMem
    exact affineDensityIncrementParameterFDeriv_le_dominator
      family background variation parameterSet parameterSetOpen jointC1
        ε C ballSubset uniformBound point parameter parameterMem
  · exact affineDensityVariationDominator_integrable variation C
  · filter_upwards with point parameter parameterMem
    exact affineDensityIncrement_hasFDerivAt
      family background variation parameterSet parameterSetOpen jointC1
        parameter (ballSubset parameterMem) point

theorem integratedDensityAlongAffine_eventually_eq_background_add_increment
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (backgroundIntegrable : Integrable fun point =>
      family point (background point))
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    (fun parameter => ∫ point : BasePoint,
      affineVariedDensity family background variation parameter point) =ᶠ[
        nhds 0]
      (fun parameter =>
        (∫ point : BasePoint, family point (background point)) +
          ∫ point : BasePoint,
            affineDensityIncrement family background variation parameter
              point) := by
  filter_upwards [parameterSetOpen.mem_nhds zeroMem] with parameter parameterMem
  have incrementIntegrable :=
    affineDensityIncrement_integrable_of_jointC1
      family background variation parameterSet jointC1 parameter parameterMem
  have pointwise : (fun point : BasePoint =>
      affineVariedDensity family background variation parameter point) =
      fun point =>
        family point (background point) +
          affineDensityIncrement family background variation parameter point := by
    funext point
    simp [affineDensityIncrement, affineVariedDensity]
  rw [pointwise, integral_add backgroundIntegrable incrementIntegrable]

/-- Neutral endpoint: the genuine integral of the affine-varied density has
the internally generated derivative. -/
theorem integratedDensityAlongAffine_hasFDerivAt_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (backgroundIntegrable : Integrable fun point =>
      family point (background point))
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    HasFDerivAt
      (fun parameter => ∫ point : BasePoint,
        affineVariedDensity family background variation parameter point)
      (∫ point : BasePoint,
        affineDensityIncrementParameterFDeriv
          family background variation 0 point) 0 := by
  have incrementDerivative :=
    affineDensityIncrement_integral_hasFDerivAt_of_jointC1
      family background variation parameterSet parameterSetOpen zeroMem jointC1
  have backgroundPlusDerivative : HasFDerivAt
      (fun parameter =>
        (∫ point : BasePoint, family point (background point)) +
          ∫ point : BasePoint,
            affineDensityIncrement family background variation parameter point)
      (∫ point : BasePoint,
        affineDensityIncrementParameterFDeriv
          family background variation 0 point) 0 := by
    simpa only using incrementDerivative.const_add
      (∫ point : BasePoint, family point (background point))
  exact backgroundPlusDerivative.congr_of_eventuallyEq
    (integratedDensityAlongAffine_eventually_eq_background_add_increment
      family background variation backgroundIntegrable parameterSet
        parameterSetOpen zeroMem jointC1)

/-- Scalar endpoint of the same neutral under-integral theorem.  Evaluation
of the generated continuous-linear derivative at the canonical parameter
direction `1` is moved through the Bochner integral; no derivative or
integrability receipt is added to the public mouth. -/
theorem integratedDensityAlongAffine_hasDerivAt_of_jointC1
    (family : BasePoint → Y → ℝ)
    (background : BasePoint → Y)
    (variation : CompactlySupportedSmoothVariation Y)
    (backgroundIntegrable : Integrable fun point =>
      family point (background point))
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (affineDensityIncrement family background variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    HasDerivAt
      (fun parameter => ∫ point : BasePoint,
        affineVariedDensity family background variation parameter point)
      (∫ point : BasePoint,
        affineDensityIncrementParameterFDeriv
          family background variation 0 point 1) 0 := by
  have derivativeContinuous : Continuous fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        family background variation 0 point :=
    affineDensityIncrementParameterFDeriv_continuous_of_jointC1
      family background variation parameterSet parameterSetOpen jointC1
        0 zeroMem
  have derivativeCompact : HasCompactSupport fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        family background variation 0 point := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    exact affineDensityIncrementParameterFDeriv_zero_of_variation_zero
      family background variation parameterSet parameterSetOpen jointC1
        0 zeroMem point variationZero
  have derivativeIntegrable : Integrable fun point : BasePoint =>
      affineDensityIncrementParameterFDeriv
        family background variation 0 point :=
    derivativeContinuous.integrable_of_hasCompactSupport derivativeCompact
  have actual :=
    (integratedDensityAlongAffine_hasFDerivAt_of_jointC1 family background
      variation backgroundIntegrable parameterSet parameterSetOpen zeroMem
      jointC1).hasDerivAt
  rw [ContinuousLinearMap.integral_apply derivativeIntegrable] at actual
  exact actual

end

end
  SaturationMonoid.PhysicsCore.StageNineAffineCompactCorridorIntegratedCalculus
