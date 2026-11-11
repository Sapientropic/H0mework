import H0mework.Realization.Feature.GramPerfectification

/-!
# Source-morphism naturality for complex feature perfectification

A commuting square of source-owned feature maps induces an injective map of
their radical quotients and strictly preserves the faithful feature, Gram
evaluation, and positive energy.  Identity and composition hold literally.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedComplexFeaturePerfectification

noncomputable section

universe c c' h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {C' : Type c'} [AddCommGroup C'] [Module ℂ C']
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (feature : C →ₗ[ℂ] H) (feature' : C' →ₗ[ℂ] H)

/-- A source map admitted by the actual feature square.  Neither positivity
nor injectivity of the source map is requested. -/
structure FeatureSourceMorphism where
  sourceMap : C →ₗ[ℂ] C'
  feature_commutes : feature'.comp sourceMap = feature

namespace FeatureSourceMorphism

theorem maps_radical
    (morphism : FeatureSourceMorphism feature feature') :
    gramRadical feature ≤
      (gramRadical feature').comap morphism.sourceMap := by
  intro value value_mem
  rw [LinearMap.mem_ker] at value_mem
  change morphism.sourceMap value ∈ gramRadical feature'
  rw [LinearMap.mem_ker]
  have commute := LinearMap.congr_fun morphism.feature_commutes value
  simpa [LinearMap.comp_apply, value_mem] using commute

def inducedMap
    (morphism : FeatureSourceMorphism feature feature') :
    Carrier feature →ₗ[ℂ] Carrier feature' :=
  (gramRadical feature).mapQ (gramRadical feature')
    morphism.sourceMap morphism.maps_radical

@[simp]
theorem inducedMap_comp_canonicalMap
    (morphism : FeatureSourceMorphism feature feature') :
    (inducedMap feature feature' morphism).comp (canonicalMap feature) =
      (canonicalMap feature').comp morphism.sourceMap := by
  apply LinearMap.ext
  intro value
  rfl

theorem faithfulFeature_naturality
    (morphism : FeatureSourceMorphism feature feature') :
    (faithfulFeature feature').comp
        (inducedMap feature feature' morphism) =
      faithfulFeature feature := by
  apply LinearMap.ext
  intro value
  obtain ⟨sourceValue, rfl⟩ :=
    Submodule.mkQ_surjective (gramRadical feature) value
  exact LinearMap.congr_fun morphism.feature_commutes sourceValue

theorem inducedMap_injective
    (morphism : FeatureSourceMorphism feature feature') :
    Function.Injective (inducedMap feature feature' morphism) := by
  intro left right equality
  apply faithfulFeature_injective feature
  have commute := LinearMap.congr_fun
    (faithfulFeature_naturality feature feature' morphism) left
  have commute' := LinearMap.congr_fun
    (faithfulFeature_naturality feature feature' morphism) right
  calc
    faithfulFeature feature left =
        faithfulFeature feature' (inducedMap feature feature' morphism left) := by
      simpa [LinearMap.comp_apply] using commute.symm
    _ = faithfulFeature feature'
          (inducedMap feature feature' morphism right) :=
      congrArg (faithfulFeature feature') equality
    _ = faithfulFeature feature right := by
      simpa [LinearMap.comp_apply] using commute'

theorem gram_naturality
    (morphism : FeatureSourceMorphism feature feature')
    (left right : Carrier feature) :
    quotientGramEvaluation feature'
        (inducedMap feature feature' morphism left)
        (inducedMap feature feature' morphism right) =
      quotientGramEvaluation feature left right := by
  rw [quotientGramEvaluation_apply, quotientGramEvaluation_apply]
  have commute := LinearMap.congr_fun
    (faithfulFeature_naturality feature feature' morphism) left
  have commute' := LinearMap.congr_fun
    (faithfulFeature_naturality feature feature' morphism) right
  have leftPointwise :
      faithfulFeature feature'
          (inducedMap feature feature' morphism left) =
        faithfulFeature feature left := by
    simpa [LinearMap.comp_apply] using commute
  have rightPointwise :
      faithfulFeature feature'
          (inducedMap feature feature' morphism right) =
        faithfulFeature feature right := by
    simpa [LinearMap.comp_apply] using commute'
  rw [leftPointwise, rightPointwise]

theorem energy_naturality
    (morphism : FeatureSourceMorphism feature feature')
    (value : Carrier feature) :
    positiveEnergyReadout feature'
        (inducedMap feature feature' morphism value) =
      positiveEnergyReadout feature value := by
  rw [positiveEnergyReadout, positiveEnergyReadout]
  have commute := LinearMap.congr_fun
    (faithfulFeature_naturality feature feature' morphism) value
  have pointwise :
      faithfulFeature feature'
          (inducedMap feature feature' morphism value) =
        faithfulFeature feature value := by
    simpa [LinearMap.comp_apply] using commute
  rw [pointwise]

def identity (feature : C →ₗ[ℂ] H) :
    FeatureSourceMorphism feature feature where
  sourceMap := LinearMap.id
  feature_commutes := by simp

@[simp]
theorem inducedMap_identity (feature : C →ₗ[ℂ] H) :
    inducedMap feature feature (identity feature) = LinearMap.id := by
  apply LinearMap.ext
  intro value
  obtain ⟨sourceValue, rfl⟩ :=
    Submodule.mkQ_surjective (gramRadical feature) value
  rfl

def comp
    {C'' : Type*} [AddCommGroup C''] [Module ℂ C'']
    {feature'' : C'' →ₗ[ℂ] H}
    (first : FeatureSourceMorphism feature feature')
    (second : FeatureSourceMorphism feature' feature'') :
    FeatureSourceMorphism feature feature'' where
  sourceMap := second.sourceMap.comp first.sourceMap
  feature_commutes := by
    rw [← LinearMap.comp_assoc, second.feature_commutes,
      first.feature_commutes]

theorem inducedMap_comp
    {C'' : Type*} [AddCommGroup C''] [Module ℂ C'']
    {feature'' : C'' →ₗ[ℂ] H}
    (first : FeatureSourceMorphism feature feature')
    (second : FeatureSourceMorphism feature' feature'') :
    inducedMap feature feature'' (comp feature feature' first second) =
      (inducedMap feature' feature'' second).comp
        (inducedMap feature feature' first) := by
  apply LinearMap.ext
  intro value
  obtain ⟨sourceValue, rfl⟩ :=
    Submodule.mkQ_surjective (gramRadical feature) value
  rfl

end FeatureSourceMorphism

end

end SourceGeneratedComplexFeaturePerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
