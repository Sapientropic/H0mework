import H0mework.Realization.Coherent.Covariance

/-!
# Naturality of integral/coherent covariance disposition

A source map and Hilbert isometry preserving the actual feature, integral
transition, and coherent evolution transport both the generated completion
action and the explicit event residual.  The construction introduces no
domain data or bounded finite face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedIntegralCoherentCovariance

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedIntegralCoherentCompletion

noncomputable section

universe l l' h h'

variable {L : Type l} [AddCommGroup L]
variable {L' : Type l'} [AddCommGroup L']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {H' : Type h'} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']

/-- Morphism of two actual covariance systems.  Every commuting law is tied
to the same source and Hilbert maps. -/
structure ActionMorphism
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    (action : ActionData feature) (action' : ActionData feature') where
  sourceMap : L →ₗ[ℤ] L'
  hilbertMap : H →ₗᵢ[ℂ] H'
  feature_commutes :
    (hilbertMap.toLinearMap.restrictScalars ℤ).comp feature =
      feature'.comp sourceMap
  transition_commutes :
    sourceMap.comp action.integralTransition =
      action'.integralTransition.comp sourceMap
  evolution_commutes :
    hilbertMap.toLinearMap.comp action.hilbertEvolution.toLinearMap =
      action'.hilbertEvolution.toLinearMap.comp hilbertMap.toLinearMap

theorem couplingResidual_naturality
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') (event : L) :
    morphism.hilbertMap (couplingResidual action event) =
      couplingResidual action' (morphism.sourceMap event) := by
  have featureSquare := LinearMap.congr_fun morphism.feature_commutes event
  have transitionSquare :=
    LinearMap.congr_fun morphism.transition_commutes event
  have evolutionSquare := LinearMap.congr_fun morphism.evolution_commutes
    (feature event)
  have featureSquare' : morphism.hilbertMap (feature event) =
      feature' (morphism.sourceMap event) := by
    simpa [LinearMap.comp_apply] using featureSquare
  have transitionSquare' :
      morphism.sourceMap (action.integralTransition event) =
        action'.integralTransition (morphism.sourceMap event) := by
    simpa [LinearMap.comp_apply] using transitionSquare
  have evolutionSquare' :
      morphism.hilbertMap (action.hilbertEvolution (feature event)) =
        action'.hilbertEvolution (morphism.hilbertMap (feature event)) := by
    simpa [LinearMap.comp_apply] using evolutionSquare
  change morphism.hilbertMap
      (action.hilbertEvolution (feature event) -
        feature (action.integralTransition event)) =
    action'.hilbertEvolution (feature' (morphism.sourceMap event)) -
      feature' (action'.integralTransition (morphism.sourceMap event))
  rw [map_sub, evolutionSquare', featureSquare']
  have transitionFeatureSquare := LinearMap.congr_fun
    morphism.feature_commutes (action.integralTransition event)
  have transitionFeatureSquare' :
      morphism.hilbertMap (feature (action.integralTransition event)) =
        feature'
          (morphism.sourceMap (action.integralTransition event)) := by
    simpa [LinearMap.comp_apply] using transitionFeatureSquare
  rw [transitionFeatureSquare', transitionSquare']

theorem radialResidual_naturality
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') (event : L) :
    radialResidual action' (morphism.sourceMap event) =
      radialResidual action event := by
  have featureSquare := LinearMap.congr_fun morphism.feature_commutes event
  have featureSquare' : morphism.hilbertMap (feature event) =
      feature' (morphism.sourceMap event) := by
    simpa [LinearMap.comp_apply] using featureSquare
  have evolutionSquare := LinearMap.congr_fun morphism.evolution_commutes
    (feature event)
  have evolutionSquare' :
      morphism.hilbertMap (action.hilbertEvolution (feature event)) =
        action'.hilbertEvolution (morphism.hilbertMap (feature event)) := by
    simpa [LinearMap.comp_apply] using evolutionSquare
  have transitionSquare :=
    LinearMap.congr_fun morphism.transition_commutes event
  have transitionSquare' :
      morphism.sourceMap (action.integralTransition event) =
        action'.integralTransition (morphism.sourceMap event) := by
    simpa [LinearMap.comp_apply] using transitionSquare
  have transitionFeatureSquare := LinearMap.congr_fun
    morphism.feature_commutes (action.integralTransition event)
  have transitionFeatureSquare' :
      morphism.hilbertMap (feature (action.integralTransition event)) =
        feature'
          (morphism.sourceMap (action.integralTransition event)) := by
    simpa [LinearMap.comp_apply] using transitionFeatureSquare
  unfold radialResidual
  rw [← featureSquare', ← evolutionSquare',
    ← transitionSquare', ← transitionFeatureSquare',
    morphism.hilbertMap.norm_map, morphism.hilbertMap.norm_map]

/-- Complex scalar extension of the source map. -/
def complexifiedSourceMap
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') :
    ComplexifiedCarrier L →ₗ[ℂ] ComplexifiedCarrier L' :=
  TensorProduct.AlgebraTensorModule.map LinearMap.id morphism.sourceMap

@[simp] theorem complexifiedSourceMap_tmul
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (coefficient : ℂ) (event : L) :
    complexifiedSourceMap morphism (coefficient ⊗ₜ[ℤ] event) =
      coefficient ⊗ₜ[ℤ] morphism.sourceMap event := by
  rw [complexifiedSourceMap,
    TensorProduct.AlgebraTensorModule.map_tmul]
  rfl

theorem complexifiedFeature_naturality
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') :
    morphism.hilbertMap.toLinearMap.comp
        (complexifiedFeature feature) =
      (complexifiedFeature feature').comp
        (complexifiedSourceMap morphism) := by
  apply LinearMap.ext
  intro value
  induction value using TensorProduct.induction_on with
  | zero => simp
  | add left right left_ih right_ih =>
      simpa only [map_add] using congrArg₂ (· + ·) left_ih right_ih
  | tmul coefficient event =>
      have featureSquare :=
        LinearMap.congr_fun morphism.feature_commutes event
      have featureSquare' : morphism.hilbertMap (feature event) =
          feature' (morphism.sourceMap event) := by
        simpa [LinearMap.comp_apply] using featureSquare
      change morphism.hilbertMap (coefficient • feature event) =
        coefficient • feature' (morphism.sourceMap event)
      rw [map_smul, featureSquare']

theorem hilbertMap_maps_complexified_range
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (value : LinearMap.range (complexifiedFeature feature)) :
    morphism.hilbertMap value.1 ∈
      LinearMap.range (complexifiedFeature feature') := by
  obtain ⟨source, source_eq⟩ := value.2
  refine ⟨complexifiedSourceMap morphism source, ?_⟩
  rw [← source_eq]
  exact (LinearMap.congr_fun
    (complexifiedFeature_naturality morphism) source).symm

/-- Isometric source-morphism map on actual complex feature ranges. -/
def coherentMorphismRangeMap
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') :
    LinearMap.range (complexifiedFeature feature) →ₗᵢ[ℂ]
      LinearMap.range (complexifiedFeature feature') where
  toLinearMap :=
    ((morphism.hilbertMap.toLinearMap.domRestrict
      (LinearMap.range (complexifiedFeature feature))).codRestrict
        (LinearMap.range (complexifiedFeature feature'))
        (hilbertMap_maps_complexified_range morphism))
  norm_map' value := morphism.hilbertMap.norm_map value.1

/-- Continuous extension of the source-morphism map between coherent
completions. -/
def coherentCompletionMapCLM
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') :
    CoherentCompletion feature →L[ℂ] CoherentCompletion feature' :=
  ((coherentRangeEmbedding feature').comp
    (coherentMorphismRangeMap morphism).toContinuousLinearMap).extend
      (coherentRangeEmbedding feature)

@[simp] theorem coherentCompletionMapCLM_range_readback
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (value : LinearMap.range (complexifiedFeature feature)) :
    coherentCompletionMapCLM morphism
        (coherentRangeEmbedding feature value) =
      coherentRangeEmbedding feature'
        (coherentMorphismRangeMap morphism value) := by
  rw [coherentCompletionMapCLM, ContinuousLinearMap.extend_eq
    ((coherentRangeEmbedding feature').comp
      (coherentMorphismRangeMap morphism).toContinuousLinearMap)
    (coherentRangeEmbedding_denseRange feature)
    (coherentRangeEmbedding_isUniformInducing feature)]
  rfl

theorem coherentCompletionMapCLM_norm
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (value : CoherentCompletion feature) :
    ‖coherentCompletionMapCLM morphism value‖ = ‖value‖ := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (continuous_norm.comp
          (coherentCompletionMapCLM morphism).continuous)
        continuous_norm
  | ih rangeValue =>
      change ‖coherentCompletionMapCLM morphism
          (coherentRangeEmbedding feature rangeValue)‖ =
        ‖coherentRangeEmbedding feature rangeValue‖
      rw [coherentCompletionMapCLM_range_readback]
      simp [coherentRangeEmbedding]

/-- Canonical isometric transport between the two generated completions. -/
def coherentCompletionMap
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') :
    CoherentCompletion feature →ₗᵢ[ℂ] CoherentCompletion feature' where
  toLinearMap := (coherentCompletionMapCLM morphism).toLinearMap
  norm_map' := coherentCompletionMapCLM_norm morphism

@[simp] theorem coherentCompletionMap_complexified_source
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (value : ComplexifiedCarrier L) :
    coherentCompletionMap morphism
        (canonicalHilbertMap (complexifiedFeature feature) value) =
      canonicalHilbertMap (complexifiedFeature feature')
        (complexifiedSourceMap morphism value) := by
  change coherentCompletionMapCLM morphism
      (coherentRangeEmbedding feature
        ((complexifiedFeature feature).rangeRestrict value)) = _
  rw [coherentCompletionMapCLM_range_readback]
  change coherentRangeEmbedding feature'
      (coherentMorphismRangeMap morphism
        ((complexifiedFeature feature).rangeRestrict value)) =
    coherentRangeEmbedding feature'
      ((complexifiedFeature feature').rangeRestrict
        (complexifiedSourceMap morphism value))
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (complexifiedFeature_naturality morphism) value

@[simp] theorem coherentCompletionMap_discrete_source
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action') (event : L) :
    coherentCompletionMap morphism
        (discreteToCoherentCompletion feature event) =
      discreteToCoherentCompletion feature' (morphism.sourceMap event) := by
  change coherentCompletionMap morphism
      (canonicalHilbertMap (complexifiedFeature feature)
        (1 ⊗ₜ[ℤ] event)) =
    canonicalHilbertMap (complexifiedFeature feature')
      (1 ⊗ₜ[ℤ] morphism.sourceMap event)
  rw [coherentCompletionMap_complexified_source,
    complexifiedSourceMap_tmul]

theorem coherentCompletionMap_realization
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    [CompleteSpace H] [CompleteSpace H']
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (value : CoherentCompletion feature) :
    coherentCompletionRealization feature'
        (coherentCompletionMap morphism value) =
      morphism.hilbertMap
        (coherentCompletionRealization feature value) := by
  induction value using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((coherentCompletionRealization feature').continuous.comp
          (coherentCompletionMap morphism).continuous)
        (morphism.hilbertMap.continuous.comp
          (coherentCompletionRealization feature).continuous)
  | ih rangeValue =>
      change coherentCompletionRealization feature'
          (coherentCompletionMapCLM morphism
            (coherentRangeEmbedding feature rangeValue)) =
        morphism.hilbertMap
          (coherentCompletionRealization feature
            (coherentRangeEmbedding feature rangeValue))
      rw [coherentCompletionMapCLM_range_readback]
      change hilbertAmbientRealization (complexifiedFeature feature')
          (coherentRangeEmbedding feature'
            (coherentMorphismRangeMap morphism rangeValue)) =
        morphism.hilbertMap
          (hilbertAmbientRealization (complexifiedFeature feature)
            (coherentRangeEmbedding feature rangeValue))
      rw [show coherentRangeEmbedding feature'
            (coherentMorphismRangeMap morphism rangeValue) =
          (coherentMorphismRangeMap morphism rangeValue :
            LinearMap.range (complexifiedFeature feature')) by rfl,
        show coherentRangeEmbedding feature rangeValue =
          (rangeValue : CoherentCompletion feature) by rfl,
        hilbertAmbientRealization_range_readback,
        hilbertAmbientRealization_range_readback]
      rfl

/-- The exact-covariance completion actions commute along every admitted
source morphism. -/
theorem coherentCompletionAction_naturality
    {feature : L →ₗ[ℤ] H} {feature' : L' →ₗ[ℤ] H'}
    [CompleteSpace H] [CompleteSpace H']
    {action : ActionData feature} {action' : ActionData feature'}
    (morphism : ActionMorphism action action')
    (covariant : ∀ event : L, couplingResidual action event = 0)
    (covariant' : ∀ event : L', couplingResidual action' event = 0)
    (value : CoherentCompletion feature) :
    coherentCompletionMap morphism
        (coherentCompletionAction action covariant value) =
      coherentCompletionAction action' covariant'
        (coherentCompletionMap morphism value) := by
  apply coherentCompletionRealization_injective feature'
  rw [coherentCompletionMap_realization,
    coherentCompletionAction_realization,
    coherentCompletionAction_realization,
    coherentCompletionMap_realization]
  exact LinearMap.congr_fun morphism.evolution_commutes
    (coherentCompletionRealization feature value)

end

end SourceGeneratedIntegralCoherentCovariance
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
