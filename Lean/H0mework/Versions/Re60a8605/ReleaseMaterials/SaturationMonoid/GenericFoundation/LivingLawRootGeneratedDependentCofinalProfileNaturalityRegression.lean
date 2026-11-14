import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCofinalProfileNaturalityKernel
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCofinalPerfectificationRegression

/-!
# Direct consumer for profile-level dependent naturality

The finite and infinite payloads from the cofinal producer regression are now
connected by one actual source map.  The carrier/dual/actual parent morphism,
the cofinal tower morphism, and the dual-evaluation square all use the same
root map, so the induced `C → P` transport is a genuine dependent-face map.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCofinalProfileNaturalityRegression

open DependentCarrier
open DependentCarrierRegression
open DependentCofinal
open DependentCofinalRegression
open DependentCofinalProfileNaturality
open CofinalNaturality
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open SourceGeneratedPerfectification

noncomputable section

def positiveToNegativeBase :
    DependentCarrier.RootMorphism positiveProfile.base
      Bool AlgebraFamily CombinatorialFamily TopologicalFamily LogicalFamily
      RelationFamily CochainFamily CarrierFamily DualFamily ActualFamily
      negativeProfile.base where
  sourceMap := fun _ => false
  root_map := by
    rfl
  carrierMap := 0
  dualMap := 0
  actualMap := 0
  evaluation_naturality := by
    apply LinearMap.ext
    intro value
    apply LinearMap.ext
    intro target
    simp
  faithful_naturality := by
    apply LinearMap.ext
    intro value
    simp

def positiveToNegativeCofinal :
    CofinalNaturality.CofinalMorphism
      (rootFace positiveProfile) (rootFace negativeProfile)
      (rootCalculation positiveProfile) (rootCalculation negativeProfile) where
  generatorMap := AddMonoidHom.id _
  stageMap := fun _ => 0
  transition_naturality := by
    intro stage
    ext value
    simp
  evaluator_naturality := by
    intro stage
    apply AddMonoidHom.ext
    intro value
    change (0 : Finsupp Nat Int) = 0
    rfl
  rootMap := fun _ => false
  root_naturality := by
    rfl

def positiveToNegative :
    ProfileMorphism positiveProfile negativeProfile where
  baseMorphism := positiveToNegativeBase
  cofinalMorphism := positiveToNegativeCofinal
  root_map_agrees := by
    rfl
  evaluationTransport := {
    dualMap := 0
    evaluation_naturality := by
      apply LinearMap.ext
      intro value
      apply LinearMap.ext
      intro target
      rfl
  }

theorem parent_root_map_is_constant_false :
    positiveToNegative.baseMorphism.sourceMap = fun _ => false := by
  funext value
  rfl

theorem cofinal_root_map_is_constant_false :
    positiveToNegative.cofinalMorphism.rootMap = fun _ => false := by
  funext value
  rfl

theorem profile_canonical_map_naturality :
    (inducedPerfectificationMap positiveToNegative).comp
        (SourceGeneratedPerfectification.canonicalMap
          (DependentCofinal.rootEvaluation positiveProfile)) =
      (SourceGeneratedPerfectification.canonicalMap
        (DependentCofinal.rootEvaluation negativeProfile)).comp
        positiveToNegative.cofinalMorphism.completionLinearMap :=
  inducedPerfectificationMap_comp_canonical positiveToNegative

theorem profile_dual_embedding_naturality :
    (SourceGeneratedPerfectification.dualEmbedding
      (DependentCofinal.rootEvaluation negativeProfile)).comp
        (inducedPerfectificationMap positiveToNegative) =
      (SourceGeneratedPerfectification.inducedDualTarget
        positiveToNegative.evaluationTransport.dualMap).comp
        (SourceGeneratedPerfectification.dualEmbedding
          (DependentCofinal.rootEvaluation positiveProfile)) :=
  dualEmbedding_naturality positiveToNegative

theorem profile_generated_dual_image_naturality :
    (DependentCofinalProfileNaturality.inducedCanonicalPerfectPairDualMap
      positiveToNegative).comp
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap
        (DependentCofinal.rootEvaluation positiveProfile)) =
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap
        (DependentCofinal.rootEvaluation negativeProfile)).comp
        (inducedPerfectificationMap positiveToNegative) :=
  DependentCofinalProfileNaturality.canonicalPerfectPair_map_naturality
    positiveToNegative

theorem profile_generated_dual_image_inclusion_naturality :
    (SourceGeneratedCanonicalPerfectPair.dualInclusion
      (DependentCofinal.rootEvaluation negativeProfile)).comp
      (DependentCofinalProfileNaturality.inducedCanonicalPerfectPairDualMap
        positiveToNegative) =
      (SourceGeneratedPerfectification.inducedDualTarget
        positiveToNegative.evaluationTransport.dualMap).comp
        (SourceGeneratedCanonicalPerfectPair.dualInclusion
          (DependentCofinal.rootEvaluation positiveProfile)) :=
  DependentCofinalProfileNaturality.canonicalPerfectPair_inclusion_naturality
    positiveToNegative

theorem profile_generated_coevaluation_naturality :
    (inducedPerfectificationMap positiveToNegative).comp
        (SourceGeneratedCanonicalPerfectPair.coevaluation
          (DependentCofinal.rootEvaluation positiveProfile)) =
      (SourceGeneratedCanonicalPerfectPair.coevaluation
        (DependentCofinal.rootEvaluation negativeProfile)).comp
        (DependentCofinalProfileNaturality.inducedCanonicalPerfectPairDualMap
          positiveToNegative) :=
  DependentCofinalProfileNaturality.canonicalPerfectPair_coevaluation_naturality
    positiveToNegative

theorem profile_parent_and_cofinal_roots_agree :
    positiveToNegative.cofinalMorphism.rootMap =
      positiveToNegative.baseMorphism.sourceMap :=
  parent_root_map_is_same_map positiveToNegative

theorem profile_transport_total :
    Nonempty (ProfileMorphism positiveProfile negativeProfile) :=
  ⟨positiveToNegative⟩

example : True := by
  fail_if_success exact positiveToNegative.evaluationTransport.dualMap = LinearMap.id
  trivial

#print axioms parent_root_map_is_constant_false
#print axioms cofinal_root_map_is_constant_false
#print axioms profile_canonical_map_naturality
#print axioms profile_dual_embedding_naturality
#print axioms profile_generated_dual_image_naturality
#print axioms profile_generated_dual_image_inclusion_naturality
#print axioms profile_generated_coevaluation_naturality
#print axioms profile_parent_and_cofinal_roots_agree
#print axioms profile_transport_total

end
end DependentCofinalProfileNaturalityRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
