import H0mework.Realization.ScalarCofinal.Naturality
import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Root occurrence for scalar cofinal completion

The scalar evaluator history is a dependent face of one existing
`RootedAccountedUnfolding`.  This adapter only projects that root and data,
records the actual compatibility calculation, and calls the generic scalar
completion/naturality layers.  It creates no sibling root.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalRootOccurrence

open CategoryTheory
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalNaturality

noncomputable section

universe r u w

variable {R : Type r} [CommRing R]
variable {Root : Type w}
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)]
variable [∀ stage, Module R (Carrier stage)]
variable {occurrence : RootedAccountedUnfolding
  (Root × Data (R := R) (Generator := Generator) (Carrier := Carrier))}

structure Face (occurrence : RootedAccountedUnfolding
    (Root × Data (R := R) (Generator := Generator) (Carrier := Carrier))) where
  private mk ::

namespace Face

def generate : Face occurrence := ⟨⟩

def root (_face : Face occurrence) : RootedAccountedUnfolding Root :=
  occurrence.map Prod.fst

def dataOccurrence (_face : Face occurrence) :
    RootedAccountedUnfolding
      (Data (R := R) (Generator := Generator) (Carrier := Carrier)) :=
  occurrence.map Prod.snd

def data (face : Face occurrence) :
    Data (R := R) (Generator := Generator) (Carrier := Carrier) :=
  face.dataOccurrence.root

def CompatibilityLaws (face : Face occurrence) : Prop := face.data.Compatible

structure GeneratedCompatibilityCalculationAt (face : Face occurrence) : Prop where
  private mk ::
  laws : face.CompatibilityLaws

theorem generateCompatibility (face : Face occurrence)
    (laws : face.CompatibilityLaws) :
    GeneratedCompatibilityCalculationAt face :=
  ⟨laws⟩

abbrev StageQuotient (face : Face occurrence) (stage : Nat) :=
  face.data.StageQuotient stage

noncomputable def completion (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) : ModuleCat.{u} R :=
  face.data.Completion calculation.laws

noncomputable def completionMap (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    ModuleCat.of R Generator ⟶ face.completion calculation :=
  face.data.completionMap calculation.laws

noncomputable def restriction (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) (stage : Nat) :
    face.completion calculation ⟶ ModuleCat.of R (face.StageQuotient stage) :=
  face.data.restriction calculation.laws stage

@[reassoc (attr := simp)] theorem completionMap_restriction
    (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) (stage : Nat) :
    face.completionMap calculation ≫ face.restriction calculation stage =
      ModuleCat.ofHom (face.data.quotientMap stage) :=
  face.data.completionMap_restriction calculation.laws stage

@[reassoc (attr := simp)] theorem source_to_evaluator
    (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) (stage : Nat) :
    face.completionMap calculation ≫ face.restriction calculation stage ≫
        ModuleCat.ofHom (face.data.stageRealization stage) =
      ModuleCat.ofHom (face.data.evaluator stage) :=
  face.data.source_to_evaluator calculation.laws stage

theorem completionMap_injective (face : Face occurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (separated : face.data.KernelSeparated) :
    Function.Injective (face.completionMap calculation) :=
  face.data.completionMap_injective calculation.laws separated

@[simp] theorem data_root (face : Face occurrence) :
    face.data = occurrence.root.2 := by
  simp [data, dataOccurrence]

theorem preserves_root_and_data (face : Face occurrence) :
    face.root = occurrence.map Prod.fst ∧
      face.dataOccurrence = occurrence.map Prod.snd ∧
      face.data = occurrence.root.2 :=
  ⟨rfl, rfl, face.data_root⟩

end Face

/-! Root-aware transport delegates to the scalar naturality map and records
the only lawful root relabelling. -/

section Naturality

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

structure RootMorphism (face₁ : Face occurrence₁) (face₂ : Face occurrence₂) where
  dataMorphism : SourceGeneratedScalarCofinalNaturality.Morphism
    face₁.data face₂.data
  rootMap : Root₁ → Root₂
  root_naturality : face₂.root = face₁.root.map rootMap

namespace RootMorphism

noncomputable def completionMorphism (morphism : RootMorphism face₁ face₂)
    (calculation₁ : Face.GeneratedCompatibilityCalculationAt face₁)
    (calculation₂ : Face.GeneratedCompatibilityCalculationAt face₂) :
    face₁.completion calculation₁ ⟶ face₂.completion calculation₂ :=
  morphism.dataMorphism.completionMorphism calculation₁.laws calculation₂.laws

theorem completionMorphism_source_naturality
    (morphism : RootMorphism face₁ face₂)
    (calculation₁ : Face.GeneratedCompatibilityCalculationAt face₁)
    (calculation₂ : Face.GeneratedCompatibilityCalculationAt face₂) :
    face₁.completionMap calculation₁ ≫
        morphism.completionMorphism calculation₁ calculation₂ =
      ModuleCat.ofHom morphism.dataMorphism.generatorMap ≫
        face₂.completionMap calculation₂ :=
  morphism.dataMorphism.completionMorphism_source_naturality
    calculation₁.laws calculation₂.laws

end RootMorphism
end Naturality

end
end SourceGeneratedScalarCofinalRootOccurrence
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
