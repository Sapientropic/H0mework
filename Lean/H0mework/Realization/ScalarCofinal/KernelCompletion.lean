import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Scalar cofinal kernel completion

An actual compatible history of `R`-linear evaluators canonically generates
the tower `C / ker(e_n)`, its `ModuleCat R` inverse limit, and the source map.
No finiteness, projectivity, duality, determinant, or coverage input enters.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalKernelCompletion

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u

variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {Carrier : Nat → Type u}
variable [∀ stage, AddCommGroup (Carrier stage)]
variable [∀ stage, Module R (Carrier stage)]

structure Data where
  evaluator : (stage : Nat) → Generator →ₗ[R] Carrier stage
  transition : (stage : Nat) → Carrier (stage + 1) →ₗ[R] Carrier stage

namespace Data

variable (data : Data (R := R) (Generator := Generator) (Carrier := Carrier))

def Compatible : Prop :=
  ∀ stage, (data.transition stage).comp (data.evaluator (stage + 1)) =
    data.evaluator stage

def stageKernel (stage : Nat) : Submodule R Generator :=
  LinearMap.ker (data.evaluator stage)

abbrev StageQuotient (stage : Nat) := Generator ⧸ data.stageKernel stage

theorem stageKernel_succ_le (compatible : data.Compatible) (stage : Nat) :
    data.stageKernel (stage + 1) ≤ data.stageKernel stage := by
  intro value highKernel
  rw [stageKernel, LinearMap.mem_ker] at highKernel ⊢
  have equality := LinearMap.congr_fun (compatible stage) value
  rw [LinearMap.comp_apply, highKernel, map_zero] at equality
  exact equality.symm

def quotientMap (stage : Nat) : Generator →ₗ[R] data.StageQuotient stage :=
  Submodule.mkQ (data.stageKernel stage)

def quotientTransition (compatible : data.Compatible) (stage : Nat) :
    data.StageQuotient (stage + 1) →ₗ[R] data.StageQuotient stage :=
  (data.stageKernel (stage + 1)).liftQ (data.quotientMap stage) (by
    intro value highKernel
    apply (Submodule.Quotient.mk_eq_zero _).2
    exact data.stageKernel_succ_le compatible stage highKernel)

@[simp] theorem quotientTransition_quotientMap
    (compatible : data.Compatible) (stage : Nat) :
    (data.quotientTransition compatible stage).comp
        (data.quotientMap (stage + 1)) = data.quotientMap stage := by
  unfold quotientTransition quotientMap
  exact Submodule.liftQ_mkQ _ _ _

@[reducible] noncomputable def quotientTower
    (compatible : data.Compatible) : ℕᵒᵖ ⥤ ModuleCat.{u} R :=
  Functor.ofOpSequence
    (X := fun stage ↦ ModuleCat.of R (data.StageQuotient stage))
    (fun stage ↦ ModuleCat.ofHom (data.quotientTransition compatible stage))

noncomputable def sourceState (compatible : data.Compatible) :
    (Functor.const ℕᵒᵖ).obj (ModuleCat.of R Generator) ⟶
      data.quotientTower compatible :=
  NatTrans.ofOpSequence
    (fun stage ↦ ModuleCat.ofHom (data.quotientMap stage))
    (fun stage ↦ by
      simp only [Functor.const_obj_map, quotientTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact data.quotientTransition_quotientMap compatible stage)

noncomputable def sourceCone (compatible : data.Compatible) :
    Cone (data.quotientTower compatible) :=
  Cone.mk (ModuleCat.of R Generator) (data.sourceState compatible)

noncomputable def Completion (compatible : data.Compatible) : ModuleCat.{u} R :=
  limit (data.quotientTower compatible)

noncomputable def completionMap (compatible : data.Compatible) :
    ModuleCat.of R Generator ⟶ data.Completion compatible :=
  limit.lift (data.quotientTower compatible) (data.sourceCone compatible)

noncomputable def restriction (compatible : data.Compatible) (stage : Nat) :
    data.Completion compatible ⟶ ModuleCat.of R (data.StageQuotient stage) :=
  limit.π (data.quotientTower compatible) (Opposite.op stage)

@[reassoc (attr := simp)] theorem completionMap_restriction
    (compatible : data.Compatible) (stage : Nat) :
    data.completionMap compatible ≫ data.restriction compatible stage =
      ModuleCat.ofHom (data.quotientMap stage) :=
  limit.lift_π (data.sourceCone compatible) (Opposite.op stage)

def stageRealization (stage : Nat) :
    data.StageQuotient stage →ₗ[R] Carrier stage :=
  (data.stageKernel stage).liftQ (data.evaluator stage) le_rfl

theorem stageRealization_injective (stage : Nat) :
    Function.Injective (data.stageRealization stage) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

@[simp] theorem stageRealization_quotientMap (stage : Nat) :
    (data.stageRealization stage).comp (data.quotientMap stage) =
      data.evaluator stage := by
  unfold stageRealization quotientMap
  exact Submodule.liftQ_mkQ _ _ _

@[reassoc (attr := simp)] theorem source_to_evaluator
    (compatible : data.Compatible) (stage : Nat) :
    data.completionMap compatible ≫ data.restriction compatible stage ≫
        ModuleCat.ofHom (data.stageRealization stage) =
      ModuleCat.ofHom (data.evaluator stage) := by
  rw [← Category.assoc, data.completionMap_restriction]
  apply ModuleCat.hom_ext
  exact data.stageRealization_quotientMap stage

def KernelSeparated : Prop :=
  ∀ value : Generator, (∀ stage, data.evaluator stage value = 0) → value = 0

theorem evaluator_eq_zero_of_completionMap_eq_zero
    (compatible : data.Compatible) (value : Generator)
    (completionZero : data.completionMap compatible value = 0)
    (stage : Nat) : data.evaluator stage value = 0 := by
  have atStage := congrArg
    (fun completed ↦ (data.restriction compatible stage).hom completed)
    completionZero
  simp only [map_zero] at atStage
  have projection := ConcreteCategory.congr_hom
    (data.completionMap_restriction compatible stage) value
  have quotientZero : data.quotientMap stage value = 0 :=
    projection.symm.trans atStage
  exact LinearMap.mem_ker.mp
    ((Submodule.Quotient.mk_eq_zero _).mp quotientZero)

theorem completionMap_injective
    (compatible : data.Compatible) (separated : data.KernelSeparated) :
    Function.Injective (data.completionMap compatible) := by
  intro left right equality
  apply sub_eq_zero.mp
  apply separated (left - right)
  intro stage
  apply data.evaluator_eq_zero_of_completionMap_eq_zero compatible
  rw [map_sub, equality, sub_self]

end Data
end
end SourceGeneratedScalarCofinalKernelCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
