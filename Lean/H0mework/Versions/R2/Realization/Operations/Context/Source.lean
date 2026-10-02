import H0mework.Versions.R2.Realization.Operations.NativeState
import H0mework.Realization.Operations.Effects

/-! A complete native source slot extends the original operation sorts without changing their values. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

abbrev ContextSort (Sorts : Type u) := Sorts ⊕ PUnit.{u + 1}

abbrev Value (process : SourceNativeLivingRootProcess N) (PhysicalValue : Sorts → Type u) : ContextSort Sorts → Type u
  | .inl sort => PhysicalValue sort
  | .inr _ => Carrier process

/-- Original variables are embedded through their native observer; these slots contain no variables. -/
abbrev Var (Sorts : Type u) : ContextSort Sorts → Type u
  | .inl _ => PEmpty.{u + 1}
  | .inr _ => PUnit.{u + 1}

instance : ∀ sort, AddCommGroup (Value process PhysicalValue sort)
  | .inl _ => inferInstance
  | .inr _ => inferInstance

def environment : Carrier process →+ Env (Value process PhysicalValue) (Var Sorts) where
  toFun material := fun sort name => match sort with
    | .inl _ => PEmpty.elim name
    | .inr _ => material
  map_zero' := by
    funext sort name
    cases sort with
    | inl _ => exact PEmpty.elim name
    | inr _ => rfl
  map_add' _ _ := by
    funext sort name
    cases sort with
    | inl _ => exact PEmpty.elim name
    | inr _ => rfl

def binding : ∀ sort, Var Sorts sort → Expr (Value process PhysicalValue) (Var Sorts) sort
  | .inl _, name => PEmpty.elim name
  | .inr _, name => .linear (sourceAction process).toAddMonoidHom (.var name)

theorem binding_eval (runtime : LivingRuntimeState process) :
    (fun sort name => (binding sort name).eval (environment (point runtime))) =
      environment (PhysicalValue := PhysicalValue) (point runtime.tick.next) := by
  funext sort name
  cases sort with
  | inl _ => exact PEmpty.elim name
  | inr _ => exact sourceAction_point runtime

theorem binding_effect (runtime : LivingRuntimeState process) :
    (fun sort name => (binding sort name).effect (environment (point runtime))
      (environment (point runtime.tick.next - point runtime))) =
      environment (PhysicalValue := PhysicalValue) (point runtime.tick.next.tick.next - point runtime.tick.next) := by
  funext sort name
  cases sort with
  | inl _ => exact PEmpty.elim name
  | inr _ =>
      exact (map_sub (sourceAction process) _ _).trans
        (congrArg₂ (· - ·) (sourceAction_point runtime.tick.next) (sourceAction_point runtime))

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
