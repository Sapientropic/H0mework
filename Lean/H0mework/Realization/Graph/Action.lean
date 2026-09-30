import Mathlib.Analysis.Normed.Operator.Prod
import H0mework.Realization.Graph.Completion
import H0mework.Realization.Topology.EquivariantDual

/-!
# Source action on a functional graph completion

A source action, its Hilbert covariance, and the actual functional character
law generate a diagonal action on the graph range and hence on its completion.
No isometry or unit-modulus character is assumed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedFunctionalGraphPerfectification

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Same-source covariance data for the two graph coordinates. -/
structure GraphCovariance
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ) where
  sourceAction : C →ₗ[ℂ] C
  hilbertAction : H →L[ℂ] H
  character : ℂ
  feature_covariance :
    hilbertAction.toLinearMap.comp feature = feature.comp sourceAction
  functional_eigenlaw :
    functional.comp sourceAction = character • functional

/-- The diagonal continuous action on the Hilbert `L²` graph target. -/
def graphTargetAction
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    GraphTarget H →L[ℂ] GraphTarget H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    ((covariance.hilbertAction.prodMap
      (covariance.character • ContinuousLinearMap.id ℂ ℂ)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).toContinuousLinearMap)

@[simp]
theorem graphTargetAction_fst
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : GraphTarget H) :
    (graphTargetAction covariance value).fst =
      covariance.hilbertAction value.fst :=
  rfl

@[simp]
theorem graphTargetAction_snd
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : GraphTarget H) :
    (graphTargetAction covariance value).snd =
      covariance.character * value.snd := by
  rfl

theorem graphTargetAction_source
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) (value : C) :
    graphTargetAction covariance (graphFeature feature functional value) =
      graphFeature feature functional (covariance.sourceAction value) := by
  apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
  apply Prod.ext
  · change covariance.hilbertAction (feature value) =
      feature (covariance.sourceAction value)
    exact LinearMap.congr_fun covariance.feature_covariance value
  · change covariance.character * functional value =
      functional (covariance.sourceAction value)
    exact (LinearMap.congr_fun covariance.functional_eigenlaw value).symm

theorem graphTargetAction_maps_range
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : LinearMap.range (graphFeature feature functional)) :
    graphTargetAction covariance value.1 ∈
      LinearMap.range (graphFeature feature functional) := by
  obtain ⟨source, source_eq⟩ := value.2
  refine ⟨covariance.sourceAction source, ?_⟩
  rw [← graphTargetAction_source covariance source, source_eq]

/-- The diagonal action restricted to the actual graph range. -/
def graphRangeAction
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    LinearMap.range (graphFeature feature functional) →L[ℂ]
      LinearMap.range (graphFeature feature functional) :=
  ((graphTargetAction covariance).domRestrict
      (LinearMap.range (graphFeature feature functional))).codRestrict
    (LinearMap.range (graphFeature feature functional))
    (graphTargetAction_maps_range covariance)

@[simp]
theorem graphRangeAction_apply
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : LinearMap.range (graphFeature feature functional)) :
    (graphRangeAction covariance value : GraphTarget H) =
      graphTargetAction covariance value.1 :=
  rfl

/-- The continuous graph action extended uniquely to the completion. -/
def graphHilbertAction
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    GraphHilbertAmbient feature functional →L[ℂ]
      GraphHilbertAmbient feature functional :=
  (graphRangeEmbedding feature functional).comp
      (graphRangeAction covariance) |>.extend
    (graphRangeEmbedding feature functional)

@[simp]
theorem graphHilbertAction_range_readback
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : LinearMap.range (graphFeature feature functional)) :
    graphHilbertAction covariance
        (graphRangeEmbedding feature functional value) =
      graphRangeEmbedding feature functional
        (graphRangeAction covariance value) := by
  rw [graphHilbertAction, ContinuousLinearMap.extend_eq
    ((graphRangeEmbedding feature functional).comp
      (graphRangeAction covariance))
    (graphRangeEmbedding_denseRange feature functional)
    (graphRangeEmbedding_isUniformInducing feature functional)]
  rfl

@[simp]
theorem graphHilbertAction_source
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) (value : C) :
    graphHilbertAction covariance
        (canonicalHilbertMap (graphFeature feature functional) value) =
      canonicalHilbertMap (graphFeature feature functional)
        (covariance.sourceAction value) := by
  change graphHilbertAction covariance
      (graphRangeEmbedding feature functional
        ((graphFeature feature functional).rangeRestrict value)) = _
  rw [graphHilbertAction_range_readback]
  change graphRangeEmbedding feature functional
      (graphRangeAction covariance
        ((graphFeature feature functional).rangeRestrict value)) =
    graphRangeEmbedding feature functional
      ((graphFeature feature functional).rangeRestrict
        (covariance.sourceAction value))
  congr 1
  apply Subtype.ext
  exact graphTargetAction_source covariance value

/-- The completed graph coordinate satisfies the generated character law on
the whole ambient, by density from the source covariance square. -/
theorem graphHilbertFunctional_eigenlaw
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (value : GraphHilbertAmbient feature functional) :
    graphHilbertFunctional feature functional
        (graphHilbertAction covariance value) =
      covariance.character *
        graphHilbertFunctional feature functional value := by
  let left : GraphHilbertAmbient feature functional →L[ℂ] ℂ :=
    (graphHilbertFunctional feature functional).comp
      (graphHilbertAction covariance)
  let right : GraphHilbertAmbient feature functional →L[ℂ] ℂ :=
    covariance.character • graphHilbertFunctional feature functional
  have mapsEqual : left = right := by
    apply ContinuousLinearMap.ext
    intro point
    have functionsEqual :=
      (graphCanonicalHilbertMap_denseRange feature functional).equalizer
        left.continuous right.continuous (by
          funext source
          change graphHilbertFunctional feature functional
              (graphHilbertAction covariance
                (canonicalHilbertMap
                  (graphFeature feature functional) source)) =
            covariance.character *
              graphHilbertFunctional feature functional
                (canonicalHilbertMap
                  (graphFeature feature functional) source)
          rw [graphHilbertAction_source,
            graphHilbertFunctional_source_readback,
            graphHilbertFunctional_source_readback]
          exact LinearMap.congr_fun covariance.functional_eigenlaw source)
    simpa using congrFun functionsEqual point
  exact congrArg (fun map :
    GraphHilbertAmbient feature functional →L[ℂ] ℂ => map value) mapsEqual

/-- The graph coordinate is the canonical equivariant bounded extension on
the generated graph ambient.  This is a positive consumer of the generic
equivariant-residual classifier, not a claim about the old Hilbert feature. -/
def graphEquivariantBoundedExtension
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    EquivariantBoundedExtension
      (canonicalHilbertMap (graphFeature feature functional))
      (graphHilbertAction covariance) covariance.character functional where
  extension := graphHilbertFunctional feature functional
  eigenlaw := graphHilbertFunctional_eigenlaw covariance
  restricts := graphHilbertFunctional_comp_source feature functional

theorem graphEquivariantExtensionResidual_zero
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    canonicalEquivariantExtensionResidual
        (canonicalHilbertMap (graphFeature feature functional))
        (graphHilbertAction covariance) covariance.character functional = 0 :=
  (canonicalEquivariantExtensionResidual_eq_zero_iff
    (canonicalHilbertMap (graphFeature feature functional))
    (graphHilbertAction covariance) covariance.character functional).mpr
      ⟨graphEquivariantBoundedExtension covariance⟩

/-- Explicit norm coordinate for failure of the source action to preserve the
graph norm. -/
def graphActionNormResidual
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) (value : C) : ℝ :=
  ‖graphFeature feature functional (covariance.sourceAction value)‖ -
    ‖graphFeature feature functional value‖

theorem graphHilbertAction_norm_of_source_residual_zero
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (sourceResidualZero : ∀ value : C,
      graphActionNormResidual covariance value = 0)
    (value : GraphHilbertAmbient feature functional) :
    ‖graphHilbertAction covariance value‖ = ‖value‖ := by
  apply DenseRange.induction_on
    (p := fun point : GraphHilbertAmbient feature functional =>
      ‖graphHilbertAction covariance point‖ = ‖point‖)
    (graphCanonicalHilbertMap_denseRange feature functional) value
  · exact isClosed_eq
      (Continuous.norm (graphHilbertAction covariance).continuous)
      continuous_norm
  · intro source
    rw [graphHilbertAction_source]
    simpa [canonicalHilbertMap] using
      sub_eq_zero.mp (sourceResidualZero source)

/-- The positive action branch generated from vanishing of every explicit
source norm residual. -/
def graphHilbertLinearIsometry
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (sourceResidualZero : ∀ value : C,
      graphActionNormResidual covariance value = 0) :
    GraphHilbertAmbient feature functional →ₗᵢ[ℂ]
      GraphHilbertAmbient feature functional where
  toLinearMap := (graphHilbertAction covariance).toLinearMap
  norm_map' := graphHilbertAction_norm_of_source_residual_zero
    covariance sourceResidualZero

@[simp]
theorem graphHilbertLinearIsometry_apply
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
    (sourceResidualZero : ∀ value : C,
      graphActionNormResidual covariance value = 0)
    (value : GraphHilbertAmbient feature functional) :
    graphHilbertLinearIsometry covariance sourceResidualZero value =
      graphHilbertAction covariance value :=
  rfl

inductive GraphActionDisposition
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional)
  | isometric (ambientAction :
      GraphHilbertAmbient feature functional →ₗᵢ[ℂ]
        GraphHilbertAmbient feature functional)
      (ambientAction_eq : ambientAction.toLinearMap =
        (graphHilbertAction covariance).toLinearMap)
  | residual (coordinates : Nonempty {value : C //
      graphActionNormResidual covariance value ≠ 0})

/-- Total isometric-face or explicit source-coordinate residual disposition.
It does not assume unitarity or a critical character. -/
def settleGraphAction
    {feature : C →ₗ[ℂ] H} {functional : C →ₗ[ℂ] ℂ}
    (covariance : GraphCovariance feature functional) :
    GraphActionDisposition covariance := by
  classical
  by_cases preserves : ∀ value : C,
      graphActionNormResidual covariance value = 0
  · exact .isometric (graphHilbertLinearIsometry covariance preserves) rfl
  · have existsResidual : ∃ value : C,
        graphActionNormResidual covariance value ≠ 0 := by
      push Not at preserves
      exact preserves
    have nonemptyResidual : Nonempty {value : C //
        graphActionNormResidual covariance value ≠ 0} :=
      existsResidual.elim fun value residual => ⟨⟨value, residual⟩⟩
    exact .residual nonemptyResidual

end

end SourceGeneratedFunctionalGraphPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
