import H0mework.Versions.R2.Realization.Operations.Context.Action
import H0mework.Realization.Operations.Execution.Substitution.Source

/-! Original forward steps generate their full contextual execution. A
native binding replays source syntax and retains its actual intermediates. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context
open SourceOperationEffects SourceOperationExecution SourceOperationNative

variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)]
variable (readEnv : process.State → Env PhysicalValue PhysicalVar)
variable (runtime : LivingRuntimeState process)

def embeddedStep {s : Sorts} {before after : Expr PhysicalValue PhysicalVar s} :
    Step (readEnv runtime.state) before after →
      Trace (Context.environment (point runtime)) (Context.embed readEnv before) (Context.embed readEnv after)
  | .bind name => by
    have generated := execution (Context.environment (point runtime)) (Context.embed readEnv (.var name))
    have original := Context.embed_eval readEnv (.var name) runtime
    rw [original] at generated
    exact generated
  | @Step.addConst _ _ _ _ _ source left right =>
      Trace.single (Step.addConst (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (sort := .inl source) left right)
  | @Step.linearConst _ _ _ _ _ source target operation value =>
      Trace.single (Step.linearConst (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (source := .inl source) (target := .inl target) operation value)
  | @Step.bilinearConst _ _ _ _ _ leftSort rightSort target operation left right =>
      Trace.single (Step.bilinearConst (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (leftSort := .inl leftSort) (rightSort := .inl rightSort) (target := .inl target) operation left right)
  | .addLeft step => (embeddedStep step).addLeft _
  | .addRight step => Trace.addRight _ (embeddedStep step)
  | @Step.linear _ _ _ _ _ source target operation _ _ step =>
      Trace.linear (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (sort := .inl source) (target := .inl target) operation (embeddedStep step)
  | @Step.bilinearLeft _ _ _ _ _ leftSort rightSort target operation _ _ right step =>
      Trace.bilinearLeft (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (sort := .inl leftSort) (rightSort := .inl rightSort) (target := .inl target)
        operation (embeddedStep step) (Context.embed readEnv right)
  | @Step.bilinearRight _ _ _ _ _ leftSort rightSort target operation left _ _ step =>
      Trace.bilinearRight (Value := Context.Value process PhysicalValue) (Var := Context.Var Sorts)
        (leftSort := .inl leftSort) (sort := .inl rightSort) (target := .inl target)
        operation (Context.embed readEnv left) (embeddedStep step)

def embeddedTrace {s : Sorts} {before after : Expr PhysicalValue PhysicalVar s} :
    Trace (readEnv runtime.state) before after →
      Trace (Context.environment (point runtime)) (Context.embed readEnv before) (Context.embed readEnv after)
  | .nil expression => .nil (Context.embed readEnv expression)
  | .cons step tail => (embeddedStep readEnv runtime step).append (embeddedTrace tail)

def nextForwardTrace {s : Sorts} {before after : Expr PhysicalValue PhysicalVar s}
    (trace : Trace (readEnv runtime.tick.next.state) before after) :
    Trace (Context.environment (point runtime))
      ((Context.embed readEnv before).subst Context.binding)
      ((Context.embed readEnv after).subst Context.binding) :=
  Trace.substitutedTrace Context.binding (Context.environment (point runtime)) (by
    rw [Context.binding_eval runtime]
    exact embeddedTrace readEnv runtime.tick.next trace)

theorem next_forward_charge {s : Sorts} {before : Expr PhysicalValue PhysicalVar s} {value : PhysicalValue s}
    (trace : Trace (readEnv runtime.tick.next.state) before (.const value)) :
    (nextForwardTrace readEnv runtime trace).length =
      remaining ((Context.embed readEnv before).subst Context.binding) :=
  (nextForwardTrace readEnv runtime trace).length_to_const

end SourceOperationNative.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
