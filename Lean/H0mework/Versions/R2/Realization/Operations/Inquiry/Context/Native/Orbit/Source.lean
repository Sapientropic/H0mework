import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Consumer
import H0mework.Realization.Operations.Substitution.Complex

/-! Original physical observers close under the actual source action.
Orbit depth is syntax depth; the complete sealed state remains the native
carrier, and the physical operation sorts and values are unchanged. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

abbrev Var (PhysicalVar : Sorts → Type u) (target : Sorts) := Nat × PhysicalVar target

def environment : Carrier runtime →+ Env PhysicalValue (Var PhysicalVar) where
  toFun material := fun target name => Context.environment runtime source
    ((sourceAction runtime ^ name.1) material) target name.2
  map_zero' := by
    funext target name
    simp only [map_zero]
    rfl
  map_add' first second := by
    funext target name
    simp only [map_add]
    rfl

def binding : ∀ target, Var PhysicalVar target → Expr PhysicalValue (Var PhysicalVar) target :=
  fun _ name => .var (name.1 + 1, name.2)

def embed {target : Sorts} : Expr PhysicalValue PhysicalVar target → Expr PhysicalValue (Var PhysicalVar) target
  | .var name => .var (0, name)
  | .const value => .const value
  | .add left right => .add (embed left) (embed right)
  | .linear operation argument => .linear operation (embed argument)
  | .bilinear operation left right => .bilinear operation (embed left) (embed right)

theorem binding_eval (material : Carrier runtime) :
    (fun target name => (binding (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) target name).eval
      (environment runtime source material)) = environment runtime source (sourceAction runtime material) := by
  funext target name
  simp only [binding, Expr.eval, environment, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pow_succ, Module.End.mul_apply]

theorem binding_effect (material change : Carrier runtime) :
    (fun target name => (binding (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) target name).effect
      (environment runtime source material) (environment runtime source change)) =
      environment runtime source (sourceAction runtime change) := binding_eval runtime source change

theorem environment_point (state : runtime.State) (target : Sorts) (name : PhysicalVar target) :
    environment runtime source (point runtime state) target (0, name) = readEnv runtime source state target name := by
  change Context.environment runtime source ((sourceAction runtime ^ 0) (point runtime state)) target name = _
  rw [pow_zero, Module.End.one_apply, Context.environment_point]

theorem binding_point (state : runtime.State) :
    (fun target name => (binding (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) target name).eval
      (environment runtime source (point runtime state))) = environment runtime source (point runtime state.tick.nextState) :=
  (binding_eval runtime source _).trans (congrArg (environment runtime source) (point_action runtime state))

theorem binding_difference (state : runtime.State) :
    (fun target name => (binding (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) target name).effect
      (environment runtime source (point runtime state))
      (environment runtime source (point runtime state.tick.nextState - point runtime state))) =
    environment runtime source (point runtime state.tick.nextState.tick.nextState - point runtime state.tick.nextState) :=
  (binding_effect runtime source _ _).trans (congrArg (environment runtime source)
    ((map_sub (sourceAction runtime) _ _).trans
      (congrArg₂ (· - ·) (point_action runtime state.tick.nextState) (point_action runtime state))))

theorem embed_eval {target : Sorts} (expression : Expr PhysicalValue PhysicalVar target) (state : runtime.State) :
    (embed expression).eval (environment runtime source (point runtime state)) =
      expression.eval (readEnv runtime source state) := by
  induction expression with
  | var name => exact environment_point runtime source state _ name
  | const value => rfl
  | add left right first second => exact congrArg₂ (· + ·) first second
  | linear operation argument prior => exact congrArg operation prior
  | bilinear operation left right first second => exact congrArg₂ (fun a b => operation a b) first second

theorem embed_effect {target : Sorts} (expression : Expr PhysicalValue PhysicalVar target) (state : runtime.State) :
    (embed expression).effect (environment runtime source (point runtime state))
      (environment runtime source (point runtime state.tick.nextState - point runtime state)) =
        expression.effect (readEnv runtime source state) (increment runtime source state) := by
  apply add_left_cancel (a := expression.eval (readEnv runtime source state))
  rw [← embed_eval runtime source expression state, ← Expr.eval_update, ← map_add, add_sub_cancel,
    embed_eval runtime source expression state.tick.nextState, embed_eval runtime source expression state,
    ← Expr.eval_update, updated_environment]

theorem literalnext_pair {target : Sorts} (expression : Expr PhysicalValue PhysicalVar target) (state : runtime.State) :
    (((embed expression).subst binding).eval (environment runtime source (point runtime state)),
      ((embed expression).subst binding).effect (environment runtime source (point runtime state))
        (environment runtime source (point runtime state.tick.nextState - point runtime state))) =
    (expression.eval (readEnv runtime source state.tick.nextState),
      expression.effect (readEnv runtime source state.tick.nextState) (increment runtime source state.tick.nextState)) := by
  rw [Expr.eval_subst, Expr.effect_subst, binding_point, binding_difference, embed_eval, embed_effect]

end SourceOperationInquiry.Context.Native.Orbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
