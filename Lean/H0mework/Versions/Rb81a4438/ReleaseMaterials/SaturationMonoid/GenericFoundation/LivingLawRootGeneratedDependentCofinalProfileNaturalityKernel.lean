import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCofinalPerfectificationKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedCofinalNaturalityKernel

/-!
# Natural transport of dependent cofinal profiles

This is the profile-level junction: a dependent-carrier root morphism and an
actual cofinal-system morphism are required to describe one source transport.
The root maps must agree, and a dual-evaluation square then induces the map on
the two canonical perfectifications.  No finite, projective, determinant, or
completed target is admitted as a field.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCofinalProfileNaturality

open DependentCarrier
open DependentCofinal
open CofinalNaturality
open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair

noncomputable section

universe s a c t l r h v d f u

variable {Source₁ : Type s} {Source₂ : Type s}
variable {Algebra₁ : Source₁ → Type a} {Algebra₂ : Source₂ → Type a}
variable {Combinatorial₁ : Source₁ → Type c} {Combinatorial₂ : Source₂ → Type c}
variable {Topological₁ : Source₁ → Type t} {Topological₂ : Source₂ → Type t}
variable {Logical₁ : Source₁ → Type l} {Logical₂ : Source₂ → Type l}
variable {Relation₁ : Source₁ → Type r} {Relation₂ : Source₂ → Type r}
variable {Cochain₁ : Source₁ → Type h} {Cochain₂ : Source₂ → Type h}
variable {Carrier₁ : Source₁ → Type v} {Carrier₂ : Source₂ → Type v}
variable {DualTarget₁ : Source₁ → Type d} {DualTarget₂ : Source₂ → Type d}
variable {ActualTarget₁ : Source₁ → Type f} {ActualTarget₂ : Source₂ → Type f}
variable [∀ source, AddCommGroup (Carrier₁ source)]
variable [∀ source, AddCommGroup (Carrier₂ source)]
variable [∀ source, AddCommGroup (DualTarget₁ source)]
variable [∀ source, AddCommGroup (DualTarget₂ source)]
variable [∀ source, AddCommGroup (ActualTarget₁ source)]
variable [∀ source, AddCommGroup (ActualTarget₂ source)]
variable {Generator₁ : Source₁ → Type u} {Generator₂ : Source₂ → Type u}
variable {StageCarrier₁ : Source₁ → Nat → Type u}
variable {StageCarrier₂ : Source₂ → Nat → Type u}
variable [∀ source, AddCommGroup (Generator₁ source)]
variable [∀ source, AddCommGroup (Generator₂ source)]
variable [∀ source stage, AddCommGroup (StageCarrier₁ source stage)]
variable [∀ source stage, AddCommGroup (StageCarrier₂ source stage)]

abbrev Profile₁
    (Source₁ : Type s)
    (Algebra₁ : Source₁ → Type a) (Combinatorial₁ : Source₁ → Type c)
    (Topological₁ : Source₁ → Type t) (Logical₁ : Source₁ → Type l)
    (Relation₁ : Source₁ → Type r) (Cochain₁ : Source₁ → Type h)
    (Carrier₁ : Source₁ → Type v) (DualTarget₁ : Source₁ → Type d)
    (ActualTarget₁ : Source₁ → Type f)
    [carrierAdd₁ : ∀ source, AddCommGroup (Carrier₁ source)]
    [dualAdd₁ : ∀ source, AddCommGroup (DualTarget₁ source)]
    [actualAdd₁ : ∀ source, AddCommGroup (ActualTarget₁ source)]
    (Generator₁ : Source₁ → Type u) (StageCarrier₁ : Source₁ → Nat → Type u)
    [generatorAdd₁ : ∀ source, AddCommGroup (Generator₁ source)]
    [stageAdd₁ : ∀ source stage, AddCommGroup (StageCarrier₁ source stage)] :
    Type _ :=
  DependentCofinal.ProfileT Source₁ Algebra₁ Combinatorial₁ Topological₁
    Logical₁ Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁
    Generator₁ StageCarrier₁

abbrev Profile₂
    (Source₂ : Type s)
    (Algebra₂ : Source₂ → Type a) (Combinatorial₂ : Source₂ → Type c)
    (Topological₂ : Source₂ → Type t) (Logical₂ : Source₂ → Type l)
    (Relation₂ : Source₂ → Type r) (Cochain₂ : Source₂ → Type h)
    (Carrier₂ : Source₂ → Type v) (DualTarget₂ : Source₂ → Type d)
    (ActualTarget₂ : Source₂ → Type f)
    [carrierAdd₂ : ∀ source, AddCommGroup (Carrier₂ source)]
    [dualAdd₂ : ∀ source, AddCommGroup (DualTarget₂ source)]
    [actualAdd₂ : ∀ source, AddCommGroup (ActualTarget₂ source)]
    (Generator₂ : Source₂ → Type u) (StageCarrier₂ : Source₂ → Nat → Type u)
    [generatorAdd₂ : ∀ source, AddCommGroup (Generator₂ source)]
    [stageAdd₂ : ∀ source stage, AddCommGroup (StageCarrier₂ source stage)] :
    Type _ :=
  DependentCofinal.ProfileT Source₂ Algebra₂ Combinatorial₂ Topological₂
    Logical₂ Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂
    Generator₂ StageCarrier₂

abbrev Profile₁T
    (Source₁ : Type s)
    (Algebra₁ : Source₁ → Type a) (Combinatorial₁ : Source₁ → Type c)
    (Topological₁ : Source₁ → Type t) (Logical₁ : Source₁ → Type l)
    (Relation₁ : Source₁ → Type r) (Cochain₁ : Source₁ → Type h)
    (Carrier₁ : Source₁ → Type v) (DualTarget₁ : Source₁ → Type d)
    (ActualTarget₁ : Source₁ → Type f)
    [carrierAdd₁ : ∀ source, AddCommGroup (Carrier₁ source)]
    [dualAdd₁ : ∀ source, AddCommGroup (DualTarget₁ source)]
    [actualAdd₁ : ∀ source, AddCommGroup (ActualTarget₁ source)]
    (Generator₁ : Source₁ → Type u) (StageCarrier₁ : Source₁ → Nat → Type u)
    [generatorAdd₁ : ∀ source, AddCommGroup (Generator₁ source)]
    [stageAdd₁ : ∀ source stage, AddCommGroup (StageCarrier₁ source stage)] :
    Type _ :=
  Profile₁ Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁ Relation₁ Cochain₁
    Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁

abbrev Profile₂T
    (Source₂ : Type s)
    (Algebra₂ : Source₂ → Type a) (Combinatorial₂ : Source₂ → Type c)
    (Topological₂ : Source₂ → Type t) (Logical₂ : Source₂ → Type l)
    (Relation₂ : Source₂ → Type r) (Cochain₂ : Source₂ → Type h)
    (Carrier₂ : Source₂ → Type v) (DualTarget₂ : Source₂ → Type d)
    (ActualTarget₂ : Source₂ → Type f)
    [carrierAdd₂ : ∀ source, AddCommGroup (Carrier₂ source)]
    [dualAdd₂ : ∀ source, AddCommGroup (DualTarget₂ source)]
    [actualAdd₂ : ∀ source, AddCommGroup (ActualTarget₂ source)]
    (Generator₂ : Source₂ → Type u) (StageCarrier₂ : Source₂ → Nat → Type u)
    [generatorAdd₂ : ∀ source, AddCommGroup (Generator₂ source)]
    [stageAdd₂ : ∀ source stage, AddCommGroup (StageCarrier₂ source stage)] :
    Type _ :=
  Profile₂ Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂ Relation₂ Cochain₂
    Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂

structure ProfileMorphism
    (profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁)
    (profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂) where
  baseMorphism :
    DependentCarrier.RootMorphism profile₁.base
      Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂ Relation₂ Cochain₂
      Carrier₂ DualTarget₂ ActualTarget₂ profile₂.base
  cofinalMorphism :
    CofinalNaturality.CofinalMorphism
      (DependentCofinal.rootFace profile₁)
      (DependentCofinal.rootFace profile₂)
      (DependentCofinal.rootCalculation profile₁)
      (DependentCofinal.rootCalculation profile₂)
  root_map_agrees :
    cofinalMorphism.rootMap = baseMorphism.sourceMap
  evaluationTransport :
    CofinalNaturality.PerfectificationMorphism
      (DualTarget₁ profile₁.base.occurrence.root)
      (DualTarget₂ profile₂.base.occurrence.root)
      cofinalMorphism
      (DependentCofinal.rootEvaluation profile₁)
      (DependentCofinal.rootEvaluation profile₂)

def inducedPerfectificationMap
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    SourceGeneratedPerfectification.PerfectificationCarrier
        (DependentCofinal.rootEvaluation profile₁) →ₗ[ℤ]
      SourceGeneratedPerfectification.PerfectificationCarrier
        (DependentCofinal.rootEvaluation profile₂) :=
  CofinalNaturality.inducedPerfectificationMap
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem inducedPerfectificationMap_comp_canonical
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    (inducedPerfectificationMap morphism).comp
        (SourceGeneratedPerfectification.canonicalMap
          (DependentCofinal.rootEvaluation profile₁)) =
      (SourceGeneratedPerfectification.canonicalMap
        (DependentCofinal.rootEvaluation profile₂)).comp
        morphism.cofinalMorphism.completionLinearMap :=
  CofinalNaturality.inducedPerfectificationMap_comp_canonical
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem dualEmbedding_naturality
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    (SourceGeneratedPerfectification.dualEmbedding
      (DependentCofinal.rootEvaluation profile₂)).comp
        (inducedPerfectificationMap morphism) =
      (SourceGeneratedPerfectification.inducedDualTarget
        morphism.evaluationTransport.dualMap).comp
        (SourceGeneratedPerfectification.dualEmbedding
          (DependentCofinal.rootEvaluation profile₁)) :=
  CofinalNaturality.dualEmbedding_naturality
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

def inducedCanonicalPerfectPairDualMap
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (DependentCofinal.rootEvaluation profile₁) →ₗ[ℤ]
      SourceGeneratedCanonicalPerfectPair.GeneratedDual
        (DependentCofinal.rootEvaluation profile₂) :=
  CofinalNaturality.inducedCanonicalPerfectPairDualMap
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem canonicalPerfectPair_map_naturality
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    (inducedCanonicalPerfectPairDualMap morphism).comp
        (SourceGeneratedCanonicalPerfectPair.generatedDualMap
          (DependentCofinal.rootEvaluation profile₁)) =
      (SourceGeneratedCanonicalPerfectPair.generatedDualMap
        (DependentCofinal.rootEvaluation profile₂)).comp
        (inducedPerfectificationMap morphism) :=
  CofinalNaturality.canonicalPerfectPair_map_naturality
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem canonicalPerfectPair_inclusion_naturality
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    (SourceGeneratedCanonicalPerfectPair.dualInclusion
      (DependentCofinal.rootEvaluation profile₂)).comp
      (inducedCanonicalPerfectPairDualMap morphism) =
      (SourceGeneratedPerfectification.inducedDualTarget
        morphism.evaluationTransport.dualMap).comp
        (SourceGeneratedCanonicalPerfectPair.dualInclusion
          (DependentCofinal.rootEvaluation profile₁)) :=
  CofinalNaturality.canonicalPerfectPair_inclusion_naturality
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem canonicalPerfectPair_coevaluation_naturality
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    (inducedPerfectificationMap morphism).comp
        (SourceGeneratedCanonicalPerfectPair.coevaluation
          (DependentCofinal.rootEvaluation profile₁)) =
      (SourceGeneratedCanonicalPerfectPair.coevaluation
        (DependentCofinal.rootEvaluation profile₂)).comp
        (inducedCanonicalPerfectPairDualMap morphism) :=
  CofinalNaturality.canonicalPerfectPair_coevaluation_naturality
    morphism.cofinalMorphism
    (DependentCofinal.rootEvaluation profile₁)
    (DependentCofinal.rootEvaluation profile₂)
    morphism.evaluationTransport

theorem parent_root_map_is_same_map
    {profile₁ : Profile₁T Source₁ Algebra₁ Combinatorial₁ Topological₁ Logical₁
      Relation₁ Cochain₁ Carrier₁ DualTarget₁ ActualTarget₁ Generator₁ StageCarrier₁}
    {profile₂ : Profile₂T Source₂ Algebra₂ Combinatorial₂ Topological₂ Logical₂
      Relation₂ Cochain₂ Carrier₂ DualTarget₂ ActualTarget₂ Generator₂ StageCarrier₂}
    (morphism : ProfileMorphism profile₁ profile₂) :
    morphism.cofinalMorphism.rootMap = morphism.baseMorphism.sourceMap :=
  morphism.root_map_agrees

end
end DependentCofinalProfileNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
