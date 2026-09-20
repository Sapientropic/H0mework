import H0mework.Realization.ScalarCofinal.KernelCompletion

/-!
# Naturality of scalar cofinal kernel completion

Commuting `R`-linear source diagrams induce maps of the quotient towers and
their inverse limits.  The generated completion map commutes with the source
map; no finite or perfect structure is used.
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
variable {Generator₁ Generator₂ : Type u}
variable [AddCommGroup Generator₁] [Module R Generator₁]
variable [AddCommGroup Generator₂] [Module R Generator₂]
variable {Carrier₁ Carrier₂ : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier₁ stage)]
variable [∀ stage, Module R (Carrier₁ stage)]
variable [∀ stage, AddCommGroup (Carrier₂ stage)]
variable [∀ stage, Module R (Carrier₂ stage)]

variable (data₁ : Data (R := R) (Generator := Generator₁)
  (Carrier := Carrier₁))
variable (data₂ : Data (R := R) (Generator := Generator₂)
  (Carrier := Carrier₂))

structure Morphism where
  generatorMap : Generator₁ →ₗ[R] Generator₂
  stageMap : (stage : Nat) → Carrier₁ stage →ₗ[R] Carrier₂ stage
  transition_naturality : ∀ stage,
    (stageMap stage).comp (data₁.transition stage) =
      (data₂.transition stage).comp (stageMap (stage + 1))
  evaluator_naturality : ∀ stage,
    (stageMap stage).comp (data₁.evaluator stage) =
      (data₂.evaluator stage).comp generatorMap

namespace Morphism

variable {data₁ : Data (R := R) (Generator := Generator₁)
  (Carrier := Carrier₁)}
variable {data₂ : Data (R := R) (Generator := Generator₂)
  (Carrier := Carrier₂)}
variable (morphism : Morphism data₁ data₂)

def stageQuotientMap (stage : Nat) :
    data₁.StageQuotient stage →ₗ[R] data₂.StageQuotient stage :=
  (data₁.stageKernel stage).liftQ
    ((data₂.quotientMap stage).comp morphism.generatorMap) (by
      intro value value_mem
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [Data.stageKernel, LinearMap.mem_ker] at value_mem ⊢
      have naturality := LinearMap.congr_fun
        (morphism.evaluator_naturality stage) value
      rw [LinearMap.comp_apply, value_mem, map_zero] at naturality
      exact naturality.symm)

@[simp] theorem stageQuotientMap_quotientMap (stage : Nat) :
    (morphism.stageQuotientMap stage).comp (data₁.quotientMap stage) =
      (data₂.quotientMap stage).comp morphism.generatorMap := by
  unfold stageQuotientMap Data.quotientMap
  exact Submodule.liftQ_mkQ _ _ _

theorem stageQuotientMap_transition
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible)
    (stage : Nat) :
    (morphism.stageQuotientMap stage).comp
        (data₁.quotientTransition compatible₁ stage) =
      (data₂.quotientTransition compatible₂ stage).comp
        (morphism.stageQuotientMap (stage + 1)) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (data₁.stageKernel (stage + 1)) quotient
  rfl

noncomputable def quotientNaturalTransformation
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible) :
    data₁.quotientTower compatible₁ ⟶ data₂.quotientTower compatible₂ :=
  NatTrans.ofOpSequence
    (fun stage ↦ ModuleCat.ofHom (morphism.stageQuotientMap stage))
    (fun stage ↦ by
      simp only [Data.quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact morphism.stageQuotientMap_transition compatible₁ compatible₂ stage)

noncomputable def completionMorphism
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible) :
    data₁.Completion compatible₁ ⟶ data₂.Completion compatible₂ :=
  limMap (morphism.quotientNaturalTransformation compatible₁ compatible₂)

theorem completionMorphism_restriction
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible)
    (stage : Nat) :
    morphism.completionMorphism compatible₁ compatible₂ ≫
        data₂.restriction compatible₂ stage =
      data₁.restriction compatible₁ stage ≫
        ModuleCat.ofHom (morphism.stageQuotientMap stage) :=
  limMap_π (morphism.quotientNaturalTransformation compatible₁ compatible₂)
    (Opposite.op stage)

theorem completionMorphism_source_naturality
    (compatible₁ : data₁.Compatible) (compatible₂ : data₂.Compatible) :
    data₁.completionMap compatible₁ ≫
        morphism.completionMorphism compatible₁ compatible₂ =
      ModuleCat.ofHom morphism.generatorMap ≫
        data₂.completionMap compatible₂ := by
  apply (limit.isLimit (data₂.quotientTower compatible₂)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change (data₁.completionMap compatible₁ ≫
      morphism.completionMorphism compatible₁ compatible₂) ≫
        data₂.restriction compatible₂ stage =
    (ModuleCat.ofHom morphism.generatorMap ≫
      data₂.completionMap compatible₂) ≫
        data₂.restriction compatible₂ stage
  calc
    _ = data₁.completionMap compatible₁ ≫
        (morphism.completionMorphism compatible₁ compatible₂ ≫
          data₂.restriction compatible₂ stage) := by rw [Category.assoc]
    _ = data₁.completionMap compatible₁ ≫
        (data₁.restriction compatible₁ stage ≫
          ModuleCat.ofHom (morphism.stageQuotientMap stage)) := by
            rw [morphism.completionMorphism_restriction]
    _ = (data₁.completionMap compatible₁ ≫
        data₁.restriction compatible₁ stage) ≫
          ModuleCat.ofHom (morphism.stageQuotientMap stage) := by rw [Category.assoc]
    _ = ModuleCat.ofHom (data₁.quotientMap stage) ≫
          ModuleCat.ofHom (morphism.stageQuotientMap stage) := by
            rw [data₁.completionMap_restriction]
    _ = ModuleCat.ofHom morphism.generatorMap ≫
          ModuleCat.ofHom (data₂.quotientMap stage) := by
            apply ModuleCat.hom_ext
            exact morphism.stageQuotientMap_quotientMap stage
    _ = (ModuleCat.ofHom morphism.generatorMap ≫
        data₂.completionMap compatible₂) ≫
          data₂.restriction compatible₂ stage := by
            rw [Category.assoc, data₂.completionMap_restriction]

end Morphism
end
end SourceGeneratedScalarCofinalNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
