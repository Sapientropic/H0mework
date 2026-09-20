import H0mework.Physics.Coframe.CoframeFirstVariation
import H0mework.Physics.Coframe.CoframeJointCalculus

/-!
# S9-C3e2b: compact-corridor lift to the integrated action

This module lifts the actual pointwise coframe derivative to the integrated
action.  It subtracts the background density, so the parameter-dependent
integrand has the same compact support as the primitive coframe variation.
Joint C¹ regularity on an open parameter corridor then generates the
uniform dominator internally from compactness; no caller-supplied derivative,
stress, dominator, integrability, or equation receipt is used.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeIntegratedVariation

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineCompactSupportIntegrationByParts
open StageNineCoframeVariation
open StageNineCoframeLocalDifferentiability
open StageNineCoframeFirstVariation
open MeasureTheory
open Filter Metric Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

noncomputable section

set_option maxHeartbeats 1200000

/-- The actual parameter-dependent common density along the primitive coframe
variation. -/
def coframeVariedLocalDensity
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) : ℝ :=
  generatedUnifiedLocalDensityAtBoundary source
    (sourceGeneratedUnifiedCouplings source) 0 point
    (toContinuumPointField
      (varyCoframe configuration variation parameter) point)

/-- Subtracting the background makes the parameter family compactly
supported without changing its derivative. -/
def coframeLocalDensityIncrement
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) : ℝ :=
  coframeVariedLocalDensity source configuration variation parameter point -
    coframeVariedLocalDensity source configuration variation 0 point

@[simp] theorem withCoframe_self
    (field : StageNineContinuumPointField) :
    withCoframe field field.coframe = field := by
  cases field
  rfl

@[simp] theorem coframeLocalDensityIncrement_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (point : BasePoint) :
    coframeLocalDensityIncrement source configuration variation 0 point = 0 := by
  simp [coframeLocalDensityIncrement]

theorem coframeLocalDensityIncrement_eq_zero_of_variation_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint)
    (variationZero : variation point = 0) :
    coframeLocalDensityIncrement source configuration variation parameter
      point = 0 := by
  unfold coframeLocalDensityIncrement coframeVariedLocalDensity
  rw [toContinuumPointField_varyCoframe,
    toContinuumPointField_varyCoframe]
  simp [variationZero]

/-- The full joint derivative of the compactly supported increment. -/
def coframeIncrementJointFDeriv
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe) :
    ℝ × BasePoint → (ℝ × BasePoint →L[ℝ] ℝ) :=
  fderiv ℝ
    (Function.uncurry
      (coframeLocalDensityIncrement source configuration variation))

/-- Restrict the joint derivative to the parameter axis. -/
def coframeIncrementParameterFDeriv
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameter : ℝ) (point : BasePoint) : ℝ →L[ℝ] ℝ :=
  (coframeIncrementJointFDeriv source configuration variation
    (parameter, point)).comp (ContinuousLinearMap.inl ℝ ℝ BasePoint)

theorem coframeLocalDensityIncrement_hasFDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint) :
    HasFDerivAt
      (fun candidate =>
        coframeLocalDensityIncrement source configuration variation candidate
          point)
      (coframeIncrementParameterFDeriv source configuration variation
        parameter point) parameter := by
  have pairMem : (parameter, point) ∈
      parameterSet ×ˢ (univ : Set BasePoint) := ⟨parameterMem, mem_univ point⟩
  have pairNeighborhood : parameterSet ×ˢ (univ : Set BasePoint) ∈
      nhds (parameter, point) :=
    (parameterSetOpen.prod isOpen_univ).mem_nhds pairMem
  have jointDerivative : HasFDerivAt
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (coframeIncrementJointFDeriv source configuration variation
        (parameter, point)) (parameter, point) := by
    exact ((jointC1.differentiableOn_one (parameter, point) pairMem).differentiableAt
      pairNeighborhood).hasFDerivAt
  exact jointDerivative.comp parameter
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) parameter point)

theorem coframeIncrementParameterFDeriv_zero_of_variation_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : BasePoint → LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint) (variationZero : variation point = 0) :
    coframeIncrementParameterFDeriv source configuration variation parameter
      point = 0 := by
  have locallyConstant : ∀ᶠ candidate in nhds parameter,
      coframeLocalDensityIncrement source configuration variation candidate
        point = 0 := by
    filter_upwards [] with candidate
    exact coframeLocalDensityIncrement_eq_zero_of_variation_zero source
      configuration variation candidate point variationZero
  have zeroDerivative : HasFDerivAt
      (fun candidate : ℝ =>
        coframeLocalDensityIncrement source configuration variation candidate
          point) (0 : ℝ →L[ℝ] ℝ) parameter :=
    hasFDerivAt_zero_of_eventually_const (0 : ℝ) locallyConstant
  exact (coframeLocalDensityIncrement_hasFDerivAt source configuration variation
    parameterSet parameterSetOpen jointC1 parameter parameterMem point).unique
      zeroDerivative

theorem coframeIncrementParameterFDeriv_zero_outside_support
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet)
    (point : BasePoint)
    (pointOutside : point ∉ tsupport
      (variation : BasePoint → LorentzianCoframe)) :
    coframeIncrementParameterFDeriv source configuration variation parameter
      point = 0 := by
  have variationZero : variation point = 0 := by
    apply not_ne_iff.mp
    intro variationNe
    exact pointOutside (subset_closure variationNe)
  exact coframeIncrementParameterFDeriv_zero_of_variation_zero source
    configuration variation parameterSet parameterSetOpen jointC1 parameter
    parameterMem point variationZero

/-- Joint `C¹` plus the fixed compact support internally produces a uniform
operator-norm bound on the actual parameter derivative. -/
theorem exists_coframeIncrementParameterFDeriv_uniform_bound
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    ∃ ε C : ℝ,
      0 < ε ∧
        ball 0 ε ⊆ parameterSet ∧
        0 ≤ C ∧
        ∀ parameter point,
          ‖parameter - 0‖ < ε →
          ‖coframeIncrementParameterFDeriv source configuration variation
            parameter point‖ ≤ C := by
  let jointDerivative :=
    coframeIncrementJointFDeriv source configuration variation
  let parameterAxis : ℝ →L[ℝ] ℝ × BasePoint :=
    ContinuousLinearMap.inl ℝ ℝ BasePoint
  let supportSet :=
    tsupport (variation : BasePoint → LorentzianCoframe)
  have supportCompact : IsCompact supportSet := variation.compactSupport
  have jointDerivativeContinuous : ContinuousOn jointDerivative
      (parameterSet ×ˢ (univ : Set BasePoint)) := by
    simpa [jointDerivative, coframeIncrementJointFDeriv] using
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
      ∃ δ : ℝ, 0 < δ ∧ ball 0 δ ⊆ parameterSet := by
    exact Metric.isOpen_iff.1 parameterSetOpen 0 zeroMem
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
    have fullDerivativeBound : ‖jointDerivative (parameter, point)‖ ≤
        derivativeBound := by
      have inClosedBall : jointDerivative (parameter, point) ∈
          closedBall (0 : ℝ × BasePoint →L[ℝ] ℝ) derivativeBound :=
        imageSubset (mem_image_of_mem jointDerivative pairInNeighborhood)
      simpa only [mem_closedBall_zero_iff] using inClosedBall
    calc
      ‖coframeIncrementParameterFDeriv source configuration variation
          parameter point‖ =
          ‖(jointDerivative (parameter, point)).comp parameterAxis‖ := rfl
      _ ≤ ‖jointDerivative (parameter, point)‖ * ‖parameterAxis‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ derivativeBound * ‖parameterAxis‖ :=
        mul_le_mul_of_nonneg_right fullDerivativeBound (norm_nonneg _)
      _ = C := rfl
  · rw [coframeIncrementParameterFDeriv_zero_outside_support source
      configuration variation parameterSet parameterSetOpen jointC1 parameter
      parameterMem point pointMem, norm_zero]
    exact mul_nonneg derivativeBoundPositive.le (norm_nonneg _)

theorem coframeLocalDensityIncrement_continuous_of_jointC1
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Continuous
      (coframeLocalDensityIncrement source configuration variation parameter) := by
  have sliceContinuous : Continuous
      (fun point : BasePoint => (parameter, point)) :=
    continuous_const.prodMk continuous_id
  have actual := jointC1.continuousOn.comp_continuous
    sliceContinuous
    (fun point : BasePoint => ⟨parameterMem, mem_univ point⟩)
  change Continuous
    (Function.uncurry
      (coframeLocalDensityIncrement source configuration variation) ∘
        fun point : BasePoint => (parameter, point))
  exact actual

theorem coframeLocalDensityIncrement_compact
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameter : ℝ) :
    HasCompactSupport
      (coframeLocalDensityIncrement source configuration variation parameter) := by
  have variationCompact := variation.compactSupport
  rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
  filter_upwards [variationCompact] with point variationZero
  exact coframeLocalDensityIncrement_eq_zero_of_variation_zero source
    configuration variation parameter point variationZero

theorem coframeLocalDensityIncrement_integrable_of_jointC1
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Integrable
      (coframeLocalDensityIncrement source configuration variation parameter) :=
  (coframeLocalDensityIncrement_continuous_of_jointC1 source configuration
    variation parameterSet jointC1 parameter parameterMem).integrable_of_hasCompactSupport
      (coframeLocalDensityIncrement_compact source configuration variation
        parameter)

theorem coframeIncrementParameterFDeriv_continuous_of_jointC1
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (parameter : ℝ) (parameterMem : parameter ∈ parameterSet) :
    Continuous fun point : BasePoint =>
      coframeIncrementParameterFDeriv source configuration variation parameter
        point := by
  have jointDerivativeContinuous : ContinuousOn
      (coframeIncrementJointFDeriv source configuration variation)
      (parameterSet ×ˢ (univ : Set BasePoint)) := by
    simpa [coframeIncrementJointFDeriv] using
      jointC1.continuousOn_fderiv_of_isOpen
        (parameterSetOpen.prod isOpen_univ) (by simp)
  have slicedDerivativeContinuous : Continuous fun point : BasePoint =>
      coframeIncrementJointFDeriv source configuration variation
        (parameter, point) := by
    have sliceContinuous : Continuous
        (fun point : BasePoint => (parameter, point)) :=
      continuous_const.prodMk continuous_id
    have actual := jointDerivativeContinuous.comp_continuous
      sliceContinuous
      (fun point : BasePoint => ⟨parameterMem, mem_univ point⟩)
    change Continuous
      (coframeIncrementJointFDeriv source configuration variation ∘
        fun point : BasePoint => (parameter, point))
    exact actual
  simpa [coframeIncrementParameterFDeriv] using
    slicedDerivativeContinuous.clm_comp_const
      (ContinuousLinearMap.inl ℝ ℝ BasePoint)

/-- The dominator is generated from the uniform derivative bound and the
actual compact support. -/
def coframeVariationDominator
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (bound : ℝ) (point : BasePoint) : ℝ :=
  indicator (tsupport (variation : BasePoint → LorentzianCoframe))
    (fun _ => bound) point

theorem coframeVariationDominator_integrable
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (bound : ℝ) :
    Integrable (coframeVariationDominator variation bound) := by
  have supportCompact : IsCompact
      (tsupport (variation : BasePoint → LorentzianCoframe)) :=
    variation.compactSupport
  exact (integrableOn_const supportCompact.measure_ne_top).integrable_indicator
    supportCompact.measurableSet

theorem coframeIncrementParameterFDeriv_le_dominator
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (ε C : ℝ)
    (ballSubset : ball 0 ε ⊆ parameterSet)
    (uniformBound : ∀ parameter point,
      ‖parameter - 0‖ < ε →
      ‖coframeIncrementParameterFDeriv source configuration variation
        parameter point‖ ≤ C)
    (point : BasePoint) (parameter : ℝ)
    (parameterMem : parameter ∈ ball 0 ε) :
    ‖coframeIncrementParameterFDeriv source configuration variation parameter
      point‖ ≤ coframeVariationDominator variation C point := by
  by_cases pointMem : point ∈
      tsupport (variation : BasePoint → LorentzianCoframe)
  · rw [coframeVariationDominator, indicator_of_mem pointMem]
    apply uniformBound parameter point
    simpa [mem_ball, dist_eq_norm] using parameterMem
  · rw [coframeIncrementParameterFDeriv_zero_outside_support source
      configuration variation parameterSet parameterSetOpen jointC1 parameter
      (ballSubset parameterMem) point pointMem]
    simp [coframeVariationDominator, pointMem]

/-- Differentiation under the spacetime integral.  The dominator and the
integrability of the actual derivative are consequences, not premises. -/
theorem coframeLocalDensityIncrement_integral_hasFDerivAt_of_jointC1
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    HasFDerivAt
      (fun parameter => ∫ point : BasePoint,
        coframeLocalDensityIncrement source configuration variation parameter
          point)
      (∫ point : BasePoint,
        coframeIncrementParameterFDeriv source configuration variation 0 point)
      0 := by
  obtain ⟨ε, C, εPositive, ballSubset, _CNonnegative, uniformBound⟩ :=
    exists_coframeIncrementParameterFDeriv_uniform_bound source configuration
      variation parameterSet parameterSetOpen zeroMem jointC1
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := ball 0 ε)
    (F := coframeLocalDensityIncrement source configuration variation)
    (F' := coframeIncrementParameterFDeriv source configuration variation)
    (bound := coframeVariationDominator variation C)
  · exact ball_mem_nhds 0 εPositive
  · filter_upwards [ball_mem_nhds 0 εPositive] with parameter parameterMem
    exact (coframeLocalDensityIncrement_continuous_of_jointC1 source
      configuration variation parameterSet jointC1 parameter
      (ballSubset parameterMem)).aestronglyMeasurable
  · exact coframeLocalDensityIncrement_integrable_of_jointC1 source
      configuration variation parameterSet jointC1 0 zeroMem
  · exact (coframeIncrementParameterFDeriv_continuous_of_jointC1 source
      configuration variation parameterSet parameterSetOpen jointC1 0 zeroMem).aestronglyMeasurable
  · filter_upwards with point parameter parameterMem
    exact coframeIncrementParameterFDeriv_le_dominator source configuration
      variation parameterSet parameterSetOpen jointC1 ε C ballSubset
      uniformBound point parameter parameterMem
  · exact coframeVariationDominator_integrable variation C
  · filter_upwards with point parameter parameterMem
    exact coframeLocalDensityIncrement_hasFDerivAt source configuration variation
      parameterSet parameterSetOpen jointC1 parameter
      (ballSubset parameterMem) point

theorem coframeIncrementParameterFDeriv_zero_eq_actual
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (nondegenerate : configuration.Nondegenerate)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint)))
    (point : BasePoint) :
    coframeIncrementParameterFDeriv source configuration variation 0 point =
      (coframeLocalStressCovector source point
        (toContinuumPointField configuration point)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (variation point)) := by
  have generatedDerivative :=
    holonomicLocalDensity_coframe_hasFDerivAt source configuration
      nondegenerate variation point
  have incrementDerivative : HasFDerivAt
      (fun parameter =>
        coframeLocalDensityIncrement source configuration variation parameter
          point)
      ((coframeLocalStressCovector source point
        (toContinuumPointField configuration point)).comp
          (ContinuousLinearMap.toSpanSingleton ℝ (variation point))) 0 := by
    simpa [coframeLocalDensityIncrement, coframeVariedLocalDensity] using
      generatedDerivative.sub_const
        (coframeVariedLocalDensity source configuration variation 0 point)
  exact (coframeLocalDensityIncrement_hasFDerivAt source configuration variation
    parameterSet parameterSetOpen jointC1 0 zeroMem point).unique
      incrementDerivative

theorem coframeIncrementParameterFDeriv_zero_integrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    Integrable fun point : BasePoint =>
      coframeIncrementParameterFDeriv source configuration variation 0 point := by
  have derivativeContinuous :=
    coframeIncrementParameterFDeriv_continuous_of_jointC1 source configuration
      variation parameterSet parameterSetOpen jointC1 0 zeroMem
  have derivativeCompact : HasCompactSupport fun point : BasePoint =>
      coframeIncrementParameterFDeriv source configuration variation 0 point := by
    have variationCompact := variation.compactSupport
    rw [hasCompactSupport_iff_eventuallyEq] at variationCompact ⊢
    filter_upwards [variationCompact] with point variationZero
    exact coframeIncrementParameterFDeriv_zero_of_variation_zero source
      configuration variation parameterSet parameterSetOpen jointC1 0 zeroMem
      point variationZero
  exact derivativeContinuous.integrable_of_hasCompactSupport derivativeCompact

theorem holonomicIntegratedUnifiedAction_eventually_eq_background_add_increment
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    (fun parameter => holonomicIntegratedUnifiedAction source 0
      (varyCoframe configuration variation parameter)) =ᶠ[nhds 0]
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          ∫ point : BasePoint,
            coframeLocalDensityIncrement source configuration variation
              parameter point) := by
  filter_upwards [parameterSetOpen.mem_nhds zeroMem] with parameter parameterMem
  have incrementIntegrable :=
    coframeLocalDensityIncrement_integrable_of_jointC1 source configuration
      variation parameterSet jointC1 parameter parameterMem
  unfold holonomicIntegratedUnifiedAction sourceGeneratedIntegratedUnifiedAction
    integratedUnifiedActionAtBoundary toContinuumFieldSection
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (varyCoframe configuration variation parameter) point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField configuration point) +
        coframeLocalDensityIncrement source configuration variation parameter
          point := by
    funext point
    simp [coframeLocalDensityIncrement, coframeVariedLocalDensity]
  rw [pointwise, integral_add densityIntegrable incrementIntegrable]

/-- Differentiate the actual integrated action from joint regularity on the
open coframe corridor. -/
theorem holonomicIntegratedUnifiedAction_coframe_hasFDerivAt_of_jointC1
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (variation : CompactlySupportedSmoothVariation LorentzianCoframe)
    (parameterSet : Set ℝ)
    (parameterSetOpen : IsOpen parameterSet)
    (zeroMem : 0 ∈ parameterSet)
    (jointC1 : ContDiffOn ℝ 1
      (Function.uncurry
        (coframeLocalDensityIncrement source configuration variation))
      (parameterSet ×ˢ (univ : Set BasePoint))) :
    HasFDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyCoframe configuration variation parameter))
      (∫ point : BasePoint,
        coframeIncrementParameterFDeriv source configuration variation 0 point)
      0 := by
  have incrementDerivative :=
    coframeLocalDensityIncrement_integral_hasFDerivAt_of_jointC1 source
      configuration variation parameterSet parameterSetOpen zeroMem jointC1
  have backgroundPlusDerivative : HasFDerivAt
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          ∫ point : BasePoint,
            coframeLocalDensityIncrement source configuration variation
              parameter point)
      (∫ point : BasePoint,
        coframeIncrementParameterFDeriv source configuration variation 0 point)
      0 := by
    simpa only using incrementDerivative.const_add
      (holonomicIntegratedUnifiedAction source 0 configuration)
  exact backgroundPlusDerivative.congr_of_eventuallyEq
    (holonomicIntegratedUnifiedAction_eventually_eq_background_add_increment
      source configuration densityIntegrable variation parameterSet
      parameterSetOpen zeroMem jointC1)

/-- Stationarity is a predicate on the candidate configuration, never source
data. -/
def CanonicalCoframeActionStationaryF
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    HasFDerivAt
      (fun parameter => holonomicIntegratedUnifiedAction source 0
        (varyCoframe configuration variation parameter))
      (0 : ℝ →L[ℝ] ℝ) (0 : ℝ)

def CanonicalCoframeWeakEquation
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ variation : CompactlySupportedSmoothVariation LorentzianCoframe,
    (∫ point : BasePoint,
      holonomicCoframeFirstVariationDensity source configuration variation
        point) = 0


end

end SaturationMonoid.PhysicsCore.StageNineCoframeIntegratedVariation
