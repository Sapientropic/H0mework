import H0mework.Realization.ScalarCofinal.Naturality

/-!
# Functoriality of scalar cofinal completion

Identity and composition of source-diagram morphisms are preserved by both
the stage kernel quotients and the canonical inverse-limit completion.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalNaturality

open CategoryTheory CategoryTheory.Limits
open SourceGeneratedScalarCofinalKernelCompletion

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator₁ Generator₂ Generator₃ : Type u}
variable [AddCommGroup Generator₁] [Module R Generator₁]
variable [AddCommGroup Generator₂] [Module R Generator₂]
variable [AddCommGroup Generator₃] [Module R Generator₃]
variable {Carrier₁ Carrier₂ Carrier₃ : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier₁ stage)]
variable [∀ stage, Module R (Carrier₁ stage)]
variable [∀ stage, AddCommGroup (Carrier₂ stage)]
variable [∀ stage, Module R (Carrier₂ stage)]
variable [∀ stage, AddCommGroup (Carrier₃ stage)]
variable [∀ stage, Module R (Carrier₃ stage)]

namespace Morphism

def id (data : Data (R := R) (Generator := Generator₁)
    (Carrier := Carrier₁)) : Morphism data data where
  generatorMap := LinearMap.id
  stageMap := fun _ ↦ LinearMap.id
  transition_naturality := by intro stage; rfl
  evaluator_naturality := by intro stage; rfl

def comp
    {data₁ : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁)}
    {data₂ : Data (R := R) (Generator := Generator₂) (Carrier := Carrier₂)}
    {data₃ : Data (R := R) (Generator := Generator₃) (Carrier := Carrier₃)}
    (second : Morphism data₂ data₃) (first : Morphism data₁ data₂) :
    Morphism data₁ data₃ where
  generatorMap := second.generatorMap.comp first.generatorMap
  stageMap := fun stage ↦ (second.stageMap stage).comp (first.stageMap stage)
  transition_naturality := by
    intro stage
    apply LinearMap.ext
    intro value
    have firstLaw := LinearMap.congr_fun
      (first.transition_naturality stage) value
    have secondLaw := LinearMap.congr_fun
      (second.transition_naturality stage) (first.stageMap (stage + 1) value)
    simp only [LinearMap.comp_apply] at firstLaw secondLaw ⊢
    rw [firstLaw, secondLaw]
  evaluator_naturality := by
    intro stage
    apply LinearMap.ext
    intro value
    have firstLaw := LinearMap.congr_fun
      (first.evaluator_naturality stage) value
    have secondLaw := LinearMap.congr_fun
      (second.evaluator_naturality stage) (first.generatorMap value)
    simp only [LinearMap.comp_apply] at firstLaw secondLaw ⊢
    rw [firstLaw, secondLaw]

theorem stageQuotientMap_id
    (data : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁))
    (stage : Nat) :
    (Morphism.id data).stageQuotientMap stage = LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (data.stageKernel stage) quotient
  rfl

theorem stageQuotientMap_comp
    {data₁ : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁)}
    {data₂ : Data (R := R) (Generator := Generator₂) (Carrier := Carrier₂)}
    {data₃ : Data (R := R) (Generator := Generator₃) (Carrier := Carrier₃)}
    (second : Morphism data₂ data₃) (first : Morphism data₁ data₂)
    (stage : Nat) :
    (Morphism.comp second first).stageQuotientMap stage =
      (second.stageQuotientMap stage).comp (first.stageQuotientMap stage) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (data₁.stageKernel stage) quotient
  rfl

theorem completionMorphism_id
    (data : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁))
    (compatible : data.Compatible) :
    (Morphism.id data).completionMorphism compatible compatible =
      𝟙 (data.Completion compatible) := by
  apply (limit.isLimit (data.quotientTower compatible)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (Morphism.id data).completionMorphism compatible compatible ≫
      data.restriction compatible stage =
    𝟙 (data.Completion compatible) ≫ data.restriction compatible stage
  rw [Morphism.completionMorphism_restriction, Morphism.stageQuotientMap_id]
  simp

theorem completionMorphism_comp
    {data₁ : Data (R := R) (Generator := Generator₁) (Carrier := Carrier₁)}
    {data₂ : Data (R := R) (Generator := Generator₂) (Carrier := Carrier₂)}
    {data₃ : Data (R := R) (Generator := Generator₃) (Carrier := Carrier₃)}
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible)
    (compatible₃ : data₃.Compatible)
    (second : Morphism data₂ data₃) (first : Morphism data₁ data₂) :
    (Morphism.comp second first).completionMorphism compatible₁ compatible₃ =
      first.completionMorphism compatible₁ compatible₂ ≫
        second.completionMorphism compatible₂ compatible₃ := by
  apply (limit.isLimit (data₃.quotientTower compatible₃)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (Morphism.comp second first).completionMorphism compatible₁ compatible₃ ≫
      data₃.restriction compatible₃ stage =
    (first.completionMorphism compatible₁ compatible₂ ≫
      second.completionMorphism compatible₂ compatible₃) ≫
        data₃.restriction compatible₃ stage
  calc
    _ = data₁.restriction compatible₁ stage ≫ ModuleCat.ofHom
        ((Morphism.comp second first).stageQuotientMap stage) :=
      Morphism.completionMorphism_restriction _ _ _ _
    _ = data₁.restriction compatible₁ stage ≫
        (ModuleCat.ofHom (first.stageQuotientMap stage) ≫
          ModuleCat.ofHom (second.stageQuotientMap stage)) := by
            rw [Morphism.stageQuotientMap_comp]
            apply congrArg
            apply ModuleCat.hom_ext
            rfl
    _ = (first.completionMorphism compatible₁ compatible₂ ≫
        second.completionMorphism compatible₂ compatible₃) ≫
          data₃.restriction compatible₃ stage := by
            calc
              data₁.restriction compatible₁ stage ≫
                    (ModuleCat.ofHom (first.stageQuotientMap stage) ≫
                      ModuleCat.ofHom (second.stageQuotientMap stage)) =
                  (data₁.restriction compatible₁ stage ≫
                    ModuleCat.ofHom (first.stageQuotientMap stage)) ≫
                      ModuleCat.ofHom (second.stageQuotientMap stage) := by
                        rw [Category.assoc]
              _ = (first.completionMorphism compatible₁ compatible₂ ≫
                    data₂.restriction compatible₂ stage) ≫
                      ModuleCat.ofHom (second.stageQuotientMap stage) := by
                        rw [first.completionMorphism_restriction]
              _ = (first.completionMorphism compatible₁ compatible₂ ≫
                    second.completionMorphism compatible₂ compatible₃) ≫
                      data₃.restriction compatible₃ stage := by
                        calc
                          (first.completionMorphism compatible₁ compatible₂ ≫
                              data₂.restriction compatible₂ stage) ≫
                              ModuleCat.ofHom (second.stageQuotientMap stage) =
                            first.completionMorphism compatible₁ compatible₂ ≫
                              (data₂.restriction compatible₂ stage ≫
                                ModuleCat.ofHom (second.stageQuotientMap stage)) := by
                                  rw [Category.assoc]
                          _ = first.completionMorphism compatible₁ compatible₂ ≫
                              (second.completionMorphism compatible₂ compatible₃ ≫
                                data₃.restriction compatible₃ stage) := by
                                  rw [second.completionMorphism_restriction]
                          _ = (first.completionMorphism compatible₁ compatible₂ ≫
                              second.completionMorphism compatible₂ compatible₃) ≫
                                data₃.restriction compatible₃ stage := by
                                  rw [Category.assoc]

end Morphism
end
end SourceGeneratedScalarCofinalNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
