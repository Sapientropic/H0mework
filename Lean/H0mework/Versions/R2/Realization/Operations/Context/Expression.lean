import H0mework.Versions.R2.Realization.Operations.Context.Source

/-! Original expressions read the complete native context through the existing free observers. -/

set_option autoImplicit false

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context

open SourceOperationEffects

noncomputable section

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]

def embed (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts} :
    Expr PhysicalValue PhysicalVar s → Expr (Value process PhysicalValue) (Var Sorts) (.inl s)
  | .var name => .linear (s := Sum.inr PUnit.unit) (t := Sum.inl s)
      (observer process (fun state => readEnv state s name)).toAddMonoidHom (.var PUnit.unit)
  | .const value => .const value
  | .add left right => .add (embed readEnv left) (embed readEnv right)
  | .linear operation argument => .linear operation (embed readEnv argument)
  | .bilinear operation left right => .bilinear operation (embed readEnv left) (embed readEnv right)

theorem embed_eval (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts}
    (expression : Expr PhysicalValue PhysicalVar s) (runtime : LivingRuntimeState process) :
    (embed readEnv expression).eval (environment (point runtime)) =
      expression.eval (readEnv runtime.state) := by
  induction expression with
  | var name => exact observer_point (fun source => readEnv source _ name) runtime
  | const value => rfl
  | add left right ihLeft ihRight => exact congrArg₂ (· + ·) ihLeft ihRight
  | linear operation argument ih => exact congrArg operation ih
  | bilinear operation left right ihLeft ihRight => exact congrArg₂ (fun a b => operation a b) ihLeft ihRight

theorem embed_effect (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts}
    (expression : Expr PhysicalValue PhysicalVar s) (runtime : LivingRuntimeState process) :
    (embed readEnv expression).effect (environment (point runtime))
      (environment (point runtime.tick.next - point runtime)) =
        expression.effect (readEnv runtime.state) (readEnv runtime.tick.next.state - readEnv runtime.state) := by
  apply add_left_cancel (a := expression.eval (readEnv runtime.state))
  rw [← embed_eval readEnv expression runtime, ← Expr.eval_update]
  rw [← map_add, add_sub_cancel]
  simp only [embed_eval]
  rw [← Expr.eval_update, add_sub_cancel]

theorem literalnext_pair (readEnv : process.State → Env PhysicalValue PhysicalVar) {s : Sorts}
    (expression : Expr PhysicalValue PhysicalVar s) (runtime : LivingRuntimeState process) :
    (((embed readEnv expression).subst binding).eval (environment (point runtime)),
      ((embed readEnv expression).subst binding).effect (environment (point runtime))
        (environment (point runtime.tick.next - point runtime))) =
      (expression.eval (readEnv runtime.tick.next.state),
        expression.effect (readEnv runtime.tick.next.state)
          (readEnv runtime.tick.next.tick.next.state - readEnv runtime.tick.next.state)) := by
  rw [Expr.eval_subst, Expr.effect_subst, binding_eval, binding_effect, embed_eval, embed_effect]

end
end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
