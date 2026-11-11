import H0mework.Realization.ScalarCofinal.ExactEnvelope

/-!
# Naturality of the scalar cofinal exact envelope

A root-aware morphism of `R`-linear evaluator histories first induces the
canonical map of cofinal completions.  When the two completed dual evaluations
form their actual square, the existing scalar exact-envelope construction
then generates carrier and dual-image maps.  Their source, ambient-dual, and
coevaluation squares commute.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalExactEnvelopeNaturality

open CategoryTheory
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarExactEnvelope

noncomputable section

universe r u w d

variable {R : Type r} [CommRing R]
variable {Root₁ Root₂ : Type w}
variable {Generator₁ Generator₂ : Type u}
variable [AddCommGroup Generator₁] [Module R Generator₁]
variable [AddCommGroup Generator₂] [Module R Generator₂]
variable {Carrier₁ Carrier₂ : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier₁ stage)]
variable [∀ stage, Module R (Carrier₁ stage)]
variable [∀ stage, AddCommGroup (Carrier₂ stage)]
variable [∀ stage, Module R (Carrier₂ stage)]
variable {occurrence₁ : RootedAccountedUnfolding
  (Root₁ × Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁))}
variable {occurrence₂ : RootedAccountedUnfolding
  (Root₂ × Data (R := R) (Generator := Generator₂) (Carrier := Carrier₂))}
variable {face₁ : Face occurrence₁} {face₂ : Face occurrence₂}
variable (rootMorphism : RootMorphism face₁ face₂)
variable (calculation₁ : Face.GeneratedCompatibilityCalculationAt face₁)
variable (calculation₂ : Face.GeneratedCompatibilityCalculationAt face₂)
variable {DualTarget₁ DualTarget₂ : Type d}
variable [AddCommGroup DualTarget₁] [Module R DualTarget₁]
variable [AddCommGroup DualTarget₂] [Module R DualTarget₂]
variable (evaluation₁ : face₁.completion calculation₁ →ₗ[R]
  Module.Dual R DualTarget₁)
variable (evaluation₂ : face₂.completion calculation₂ →ₗ[R]
  Module.Dual R DualTarget₂)
variable (dualMap : DualTarget₂ →ₗ[R] DualTarget₁)
variable (evaluationSquare :
  (inducedDualTarget dualMap).comp evaluation₁ =
    evaluation₂.comp
      (rootMorphism.completionMorphism calculation₁ calculation₂).hom)

def carrierMap :
    SourceGeneratedScalarCofinalExactEnvelope.Carrier
        face₁ calculation₁ evaluation₁ →ₗ[R]
      SourceGeneratedScalarCofinalExactEnvelope.Carrier
        face₂ calculation₂ evaluation₂ :=
  inducedCarrierMap evaluation₁ evaluation₂
    (rootMorphism.completionMorphism calculation₁ calculation₂).hom
    dualMap evaluationSquare

def dualImageMap :
    SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        face₁ calculation₁ evaluation₁ →ₗ[R]
      SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        face₂ calculation₂ evaluation₂ :=
  inducedDualImageMap evaluation₁ evaluation₂
    (rootMorphism.completionMorphism calculation₁ calculation₂).hom
    dualMap evaluationSquare

theorem carrierMap_source_naturality :
    (carrierMap rootMorphism calculation₁ calculation₂
        evaluation₁ evaluation₂ dualMap evaluationSquare).comp
        (SourceGeneratedScalarCofinalExactEnvelope.sourceMap
          face₁ calculation₁ evaluation₁) =
      (SourceGeneratedScalarCofinalExactEnvelope.sourceMap
        face₂ calculation₂ evaluation₂).comp
        rootMorphism.dataMorphism.generatorMap := by
  apply LinearMap.ext
  intro value
  have envelopeNaturality := LinearMap.congr_fun
    (inducedPerfectificationMap_comp evaluation₁ evaluation₂
      (rootMorphism.completionMorphism calculation₁ calculation₂).hom
      dualMap evaluationSquare)
    (face₁.completionMap calculation₁ value)
  have completionNaturality := ConcreteCategory.congr_hom
    (rootMorphism.completionMorphism_source_naturality
      calculation₁ calculation₂) value
  simpa [carrierMap, SourceGeneratedScalarCofinalExactEnvelope.sourceMap,
    SourceGeneratedScalarExactEnvelope.inducedCarrierMap,
    LinearMap.comp_apply] using envelopeNaturality.trans
      (congrArg (SourceGeneratedScalarPerfectification.canonicalMap evaluation₂)
        completionNaturality)

theorem generatedDualMap_naturality :
    (dualImageMap rootMorphism calculation₁ calculation₂
        evaluation₁ evaluation₂ dualMap evaluationSquare).comp
        (SourceGeneratedScalarExactEnvelope.generatedDualMap evaluation₁) =
      (SourceGeneratedScalarExactEnvelope.generatedDualMap evaluation₂).comp
        (carrierMap rootMorphism calculation₁ calculation₂
          evaluation₁ evaluation₂ dualMap evaluationSquare) :=
  SourceGeneratedScalarExactEnvelope.generatedDualMap_naturality
    evaluation₁ evaluation₂
    (rootMorphism.completionMorphism calculation₁ calculation₂).hom
    dualMap evaluationSquare

theorem dualInclusion_naturality :
    (SourceGeneratedScalarExactEnvelope.dualInclusion evaluation₂).comp
        (dualImageMap rootMorphism calculation₁ calculation₂
          evaluation₁ evaluation₂ dualMap evaluationSquare) =
      (inducedDualTarget dualMap).comp
        (SourceGeneratedScalarExactEnvelope.dualInclusion evaluation₁) :=
  SourceGeneratedScalarExactEnvelope.dualInclusion_naturality
    evaluation₁ evaluation₂
    (rootMorphism.completionMorphism calculation₁ calculation₂).hom
    dualMap evaluationSquare

theorem coevaluation_naturality :
    (carrierMap rootMorphism calculation₁ calculation₂
        evaluation₁ evaluation₂ dualMap evaluationSquare).comp
        (SourceGeneratedScalarExactEnvelope.coevaluation evaluation₁) =
      (SourceGeneratedScalarExactEnvelope.coevaluation evaluation₂).comp
        (dualImageMap rootMorphism calculation₁ calculation₂
          evaluation₁ evaluation₂ dualMap evaluationSquare) :=
  SourceGeneratedScalarExactEnvelope.coevaluation_naturality
    evaluation₁ evaluation₂
    (rootMorphism.completionMorphism calculation₁ calculation₂).hom
    dualMap evaluationSquare

end
end SourceGeneratedScalarCofinalExactEnvelopeNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
