import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCarrierKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedDependentCofinalAxiomFreeCore
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedUniversalCofinalPerfectificationKernel

/-!
# Dependent cofinal perfectification

This producer combines the source-indexed carrier family with an actual
cofinal evaluator family.  For every source payload, the installed dependent
occurrence projects back to the one base occurrence and carries its own stage
compatibility law.  At the selected root, the same source-generated kernel
quotient tower, cofinal completion, residual tower, and `C / ker(e)`
perfectification are generated.  No finite, projective, coverage, or
determinant premise is admitted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DependentCofinal

open DependentCarrier
open DependentCofinalAxiomFree
open UniversalCofinalPerfectification
open SourceGeneratedCanonicalPerfectPair
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt

noncomputable section

universe s a c t l r h v d f u q

variable {Source : Type s}
variable {Algebra : Source → Type a} {Combinatorial : Source → Type c}
variable {Topological : Source → Type t} {Logical : Source → Type l}
variable {Relation : Source → Type r} {Cochain : Source → Type h}
variable {Carrier : Source → Type v} {DualTarget : Source → Type d}
variable {ActualTarget : Source → Type f}
variable [∀ source, AddCommGroup (Carrier source)]
variable [∀ source, AddCommGroup (DualTarget source)]
variable [∀ source, AddCommGroup (ActualTarget source)]

variable {Generator : Source → Type u}
variable {StageCarrier : Source → Nat → Type u}
variable [∀ source, AddCommGroup (Generator source)]
variable [∀ source stage, AddCommGroup (StageCarrier source stage)]

structure Profile extends
    DependentCofinalAxiomFree.Input Source Algebra Combinatorial Topological
      Logical Relation Cochain Carrier DualTarget ActualTarget Generator
      StageCarrier where
  compatibility :
    CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt.GeneratedCompatibilityCalculationAt
      (CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt.generate
        (dependentOccurrence := toInput.cofinalOccurrence))
  completionEvaluation :
    let face := RootGeneratedCofinalKernelCompletionAt.generate
      (dependentOccurrence := toInput.cofinalOccurrence)
    let calculation := compatibility
    face.completion calculation →ₗ[ℤ]
      Module.Dual ℤ (DualTarget toInput.base.occurrence.root)

abbrev ProfileAt
    (Source : Type s)
    (Algebra : Source → Type a) (Combinatorial : Source → Type c)
    (Topological : Source → Type t) (Logical : Source → Type l)
    (Relation : Source → Type r) (Cochain : Source → Type h)
    (Carrier : Source → Type v) (DualTarget : Source → Type d)
    (ActualTarget : Source → Type f)
    [carrierAdd : ∀ source, AddCommGroup (Carrier source)]
    [dualAdd : ∀ source, AddCommGroup (DualTarget source)]
    [actualAdd : ∀ source, AddCommGroup (ActualTarget source)]
    (Generator : Source → Type u) (StageCarrier : Source → Nat → Type u)
    [generatorAdd : ∀ source, AddCommGroup (Generator source)]
    [stageAdd : ∀ source stage, AddCommGroup (StageCarrier source stage)] :
    Type _ :=
  @Profile Source Algebra Combinatorial Topological Logical Relation Cochain
    Carrier DualTarget ActualTarget carrierAdd dualAdd actualAdd
    Generator StageCarrier generatorAdd stageAdd

abbrev ProfileT
    (Source : Type s)
    (Algebra : Source → Type a) (Combinatorial : Source → Type c)
    (Topological : Source → Type t) (Logical : Source → Type l)
    (Relation : Source → Type r) (Cochain : Source → Type h)
    (Carrier : Source → Type v) (DualTarget : Source → Type d)
    (ActualTarget : Source → Type f)
    [carrierAdd : ∀ source, AddCommGroup (Carrier source)]
    [dualAdd : ∀ source, AddCommGroup (DualTarget source)]
    [actualAdd : ∀ source, AddCommGroup (ActualTarget source)]
    (Generator : Source → Type u) (StageCarrier : Source → Nat → Type u)
    [generatorAdd : ∀ source, AddCommGroup (Generator source)]
    [stageAdd : ∀ source stage, AddCommGroup (StageCarrier source stage)] :
    Type _ :=
  ProfileAt Source Algebra Combinatorial Topological Logical Relation Cochain
    Carrier DualTarget ActualTarget Generator StageCarrier

abbrev rootSource
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :=
  profile.base.occurrence.root

abbrev rootOccurrence
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :=
  profile.cofinalOccurrence

abbrev rootFace
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    RootGeneratedCofinalKernelCompletionAt (rootOccurrence profile) :=
  RootGeneratedCofinalKernelCompletionAt.generate
    (dependentOccurrence := rootOccurrence profile)

abbrev rootCalculation
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    GeneratedCompatibilityCalculationAt (rootFace profile) :=
  profile.compatibility

abbrev rootCompletedCarrier
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :=
  (rootFace profile).completion (rootCalculation profile)

abbrev rootEvaluation
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    rootCompletedCarrier profile →ₗ[ℤ]
      Module.Dual ℤ (DualTarget profile.base.occurrence.root) :=
  profile.completionEvaluation

structure DependentCofinalGenerated
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    Type _ where
  dependent : DependentCarrier.Generated profile.base
  cofinal : UniversalCofinalPerfectification.Generated
    (rootFace profile) (rootCalculation profile) (rootEvaluation profile)
  canonicalPerfectPair :
    SourceGeneratedCanonicalPerfectPair.Generated (rootEvaluation profile)
  root_alignment :
    (rootOccurrence profile).map Prod.fst = profile.base.occurrence

def generate
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    DependentCofinalGenerated profile where
  dependent := DependentCarrier.generate profile.base
  cofinal := UniversalCofinalPerfectification.generate
    (rootFace profile) (rootCalculation profile) (rootEvaluation profile)
  canonicalPerfectPair := SourceGeneratedCanonicalPerfectPair.generate
    (rootEvaluation profile)
  root_alignment := profile.cofinal_root_alignment

theorem generated_total
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    Nonempty (DependentCofinalGenerated profile) :=
  ⟨generate profile⟩

theorem root_alignment
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    (rootOccurrence profile).map Prod.fst = profile.base.occurrence :=
  (generate profile).root_alignment

theorem cofinal_completion_reused
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    (generate profile).cofinal.completion = rootFace profile :=
  rfl

theorem cofinal_residual_map_injective
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    Function.Injective
      (UniversalCofinalPerfectification.cofinalResidualMap
        (rootFace profile) (rootCalculation profile)) :=
  UniversalCofinalPerfectification.completionResidualToResidualLimit_injective
    (rootFace profile) (rootCalculation profile)

theorem perfectification_readback
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    (UniversalCofinalPerfectification.dualEmbedding
      (rootFace profile) (rootCalculation profile) (rootEvaluation profile)).comp
        (UniversalCofinalPerfectification.canonicalMap
          (rootFace profile) (rootCalculation profile) (rootEvaluation profile)) =
      rootEvaluation profile :=
  UniversalCofinalPerfectification.dualEmbedding_comp_canonicalMap
    (rootFace profile) (rootCalculation profile) (rootEvaluation profile)

theorem canonicalPerfectPair_readback
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier) :
    (generate profile).canonicalPerfectPair.inclusion.comp
        (generate profile).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding (rootEvaluation profile) :=
  SourceGeneratedCanonicalPerfectPair.generated_readback
    (rootEvaluation profile)

def boundedObservationDisposition
    (profile : ProfileT Source Algebra Combinatorial Topological Logical Relation
      Cochain Carrier DualTarget ActualTarget Generator StageCarrier)
    {O : Type q} [AddCommGroup O]
    (observation : SourceGeneratedPerfectification.PerfectificationCarrier
      (rootEvaluation profile) →ₗ[ℤ] O) :
    ExactPerfectEnvelopeBoundedDisposition.Disposition
      (rootEvaluation profile) observation :=
  UniversalCofinalPerfectification.boundedObservationDisposition
    (rootFace profile) (rootCalculation profile) (rootEvaluation profile)
    observation

end
end DependentCofinal
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
