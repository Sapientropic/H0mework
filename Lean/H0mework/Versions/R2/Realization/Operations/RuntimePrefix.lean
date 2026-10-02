import H0mework.Versions.R2.Foundation.Runtime.Activation
import H0mework.Realization.Operations.ScalarRelations
import H0mework.Realization.ScalarCofinal.KernelCompletion

/-! Actual material differences generate complete operation inventories along a fixed runtime. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationRuntime

open SourceOperationEffects SourceOperationScalarRelations
open SourceGeneratedScalarCofinalKernelCompletion CategoryTheory CategoryTheory.Limits

noncomputable section

universe r u v m n

abbrev FormalCarrier (R : Type r) [CommRing R] {Sorts : Type u}
    (Value Var : Sorts → Type v) [∀ s, AddCommGroup (Value s)] (s : Sorts) :=
  Formal R Value Var s

abbrev PrefixCarrier {Sorts : Type u} (Value : Sorts → Type v) (s : Sorts) (bound : Nat) :=
  Fin (bound + 1) → Value s × Value s

variable {N : WorldRelationNetwork.{n}} {process : SourceNativeLivingRootProcess N}

def materialHistory (runtime : LivingRuntimeState process) (bound : Nat) :=
  SourceGeneratedRuntimeMaterialHistoryAt.generate runtime (bound + 1)

section Environment

variable {Sorts : Type u} {Value Var : Sorts → Type v}
variable [∀ s, AddCommGroup (Value s)]
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

def oldEnvironment {runtime : LivingRuntimeState process}
    (_stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Env Value Var :=
  environment (readMaterial runtime.state)

def incrementEnvironment {runtime : LivingRuntimeState process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) : Env Value Var :=
  environment (readMaterial stage.next.state - readMaterial runtime.state)

end Environment

variable {R : Type r} [CommRing R] {Sorts : Type u}
variable {Value Var : Sorts → Type (max r u)}
variable [∀ s, AddCommGroup (Value s)] [∀ s, Module R (Value s)] {s : Sorts}
variable {Material : Type m} [AddCommGroup Material]
variable (readMaterial : process.State → Material) (environment : Material →+ Env Value Var)

def stageInventory {runtime : LivingRuntimeState process}
    (stage : SourceGeneratedRuntimeMaterialStageAt runtime) :
    FormalCarrier R Value Var s →ₗ[R] Value s × Value s :=
  updateInventory (R := R) (s := s)
    (oldEnvironment readMaterial environment stage) (incrementEnvironment readMaterial environment stage)

def prefixEvaluator (runtime : LivingRuntimeState process) (bound : Nat) :
    FormalCarrier R Value Var s →ₗ[R] PrefixCarrier Value s bound :=
  LinearMap.pi fun index => stageInventory readMaterial environment
    ((materialHistory runtime bound).stageAt index)

def prefixRestriction (bound : Nat) :
    PrefixCarrier Value s (bound + 1) →ₗ[R] PrefixCarrier Value s bound :=
  LinearMap.pi fun index => LinearMap.proj index.castSucc

def prefixData (runtime : LivingRuntimeState process) :
    Data (R := R) (Generator := FormalCarrier R Value Var s) (Carrier := PrefixCarrier Value s) where
  evaluator := prefixEvaluator readMaterial environment runtime
  transition := prefixRestriction

theorem prefix_compatible (runtime : LivingRuntimeState process) :
    (prefixData (R := R) (s := s) readMaterial environment runtime).Compatible := by
  intro bound
  apply LinearMap.ext
  intro word
  funext index
  rfl

def completion (runtime : LivingRuntimeState process) :=
  (prefixData (R := R) (s := s) readMaterial environment runtime).Completion
    (prefix_compatible readMaterial environment runtime)

def completionMap (runtime : LivingRuntimeState process) :=
  (prefixData (R := R) (s := s) readMaterial environment runtime).completionMap
    (prefix_compatible readMaterial environment runtime)

def stageRead (runtime : LivingRuntimeState process) (bound : Nat) :
    completion (R := R) (s := s) readMaterial environment runtime →ₗ[R] PrefixCarrier Value s bound :=
  ((prefixData readMaterial environment runtime).stageRealization bound).comp
    ((prefixData readMaterial environment runtime).restriction
      (prefix_compatible readMaterial environment runtime) bound).hom

theorem completion_source_to_prefix (runtime : LivingRuntimeState process) (bound : Nat) :
    completionMap (R := R) (s := s) readMaterial environment runtime ≫
        ModuleCat.ofHom (stageRead readMaterial environment runtime bound) =
      ModuleCat.ofHom (prefixEvaluator readMaterial environment runtime bound) := by
  exact (prefixData readMaterial environment runtime).source_to_evaluator
    (prefix_compatible readMaterial environment runtime) bound

theorem completion_source_to_actual_stage (runtime : LivingRuntimeState process)
    (bound : Nat) (word : FormalCarrier R Value Var s) (index : Fin (bound + 1)) :
    stageRead readMaterial environment runtime bound
        ((completionMap readMaterial environment runtime).hom word) index =
      stageInventory readMaterial environment ((materialHistory runtime bound).stageAt index) word := by
  exact congrFun (ConcreteCategory.congr_hom
    (completion_source_to_prefix readMaterial environment runtime bound) word) index

theorem completion_fibre_iff (runtime : LivingRuntimeState process)
    (left right : FormalCarrier R Value Var s) :
    (completionMap readMaterial environment runtime).hom left =
        (completionMap readMaterial environment runtime).hom right ↔
      ∀ bound (index : Fin (bound + 1)),
        stageInventory readMaterial environment ((materialHistory runtime bound).stageAt index) left =
          stageInventory readMaterial environment ((materialHistory runtime bound).stageAt index) right := by
  constructor
  · intro same bound index
    have observed := congrArg (fun value => stageRead readMaterial environment runtime bound value index) same
    exact (completion_source_to_actual_stage readMaterial environment runtime bound left index).symm.trans
      (observed.trans (completion_source_to_actual_stage readMaterial environment runtime bound right index))
  · intro same
    apply Limits.Concrete.limit_ext
      ((prefixData readMaterial environment runtime).quotientTower
        (prefix_compatible readMaterial environment runtime))
    intro bound
    apply (prefixData readMaterial environment runtime).stageRealization_injective bound.unop
    change stageRead readMaterial environment runtime bound.unop
        ((completionMap readMaterial environment runtime).hom left) =
      stageRead readMaterial environment runtime bound.unop
        ((completionMap readMaterial environment runtime).hom right)
    funext index
    rw [completion_source_to_actual_stage, completion_source_to_actual_stage]
    exact same bound.unop index

end
end SourceOperationRuntime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
