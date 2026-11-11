import H0mework.Versions.R2.Realization.Operations.Context.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Context.WordExecution
open SourceOperationEffects SourceOperationExecution SourceOperationNative
variable {N : WorldRelationNetwork.{u}} {process : SourceNativeLivingRootProcess N}
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ sort, AddCommGroup (PhysicalValue sort)]
variable (readEnv : process.State → Env PhysicalValue PhysicalVar)

def observerEnvironment (word : Carrier process) : Env PhysicalValue PhysicalVar :=
 fun sort name => observer process (fun state => readEnv state sort name) word

theorem observerEnvironment_point (runtime : LivingRuntimeState process) :
 observerEnvironment readEnv (point runtime) = readEnv runtime.state := by
 funext sort name
 exact SourceOperationNative.observer_point (fun state => readEnv state sort name) runtime

theorem embed_eval {s : Sorts} (expression : Expr PhysicalValue PhysicalVar s) (word : Carrier process) :
 (Context.embed readEnv expression).eval (Context.environment word) =
 expression.eval (observerEnvironment readEnv word) := by
 induction expression with
 | var name => rfl
 | const value => rfl
 | add left right ihLeft ihRight => exact congrArg₂ (· + ·) ihLeft ihRight
 | linear operation argument ih => exact congrArg operation ih
 | bilinear operation left right ihLeft ihRight => exact congrArg₂ (fun a b => operation a b) ihLeft ihRight

theorem binding_word (word : Carrier process) :
 (fun sort name => (Context.binding sort name).eval
  (Context.environment (PhysicalValue := PhysicalValue) word)) =
 Context.environment (PhysicalValue := PhysicalValue) (sourceAction process word) := by
 funext sort name
 cases sort with
 | inl _ => exact PEmpty.elim name
 | inr _ => rfl

variable (word : Carrier process)

def embeddedStep {s : Sorts} {before after : Expr PhysicalValue PhysicalVar s} :
    Step (observerEnvironment readEnv word) before after →
      Trace (Context.environment word) (Context.embed readEnv before) (Context.embed readEnv after)
  | .bind name => by
    have generated := execution (Context.environment word) (Context.embed readEnv (.var name))
    have original := embed_eval readEnv (.var name) word
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
    Trace (observerEnvironment readEnv word) before after →
      Trace (Context.environment word) (Context.embed readEnv before) (Context.embed readEnv after)
  | .nil expression => .nil (Context.embed readEnv expression)
  | .cons step tail => (embeddedStep readEnv word step).append (embeddedTrace tail)

def nextForwardTrace {s : Sorts} {before after : Expr PhysicalValue PhysicalVar s}
 (trace : Trace (observerEnvironment readEnv (sourceAction process word)) before after) :
 Trace (Context.environment word)
  ((Context.embed readEnv before).subst Context.binding)
  ((Context.embed readEnv after).subst Context.binding) :=
 Trace.substitutedTrace Context.binding (Context.environment word) (by
  rw [binding_word]
  exact embeddedTrace readEnv (sourceAction process word) trace)

def forward {s : Sorts} (expression : Expr PhysicalValue PhysicalVar s) :=
 nextForwardTrace readEnv word (execution (observerEnvironment readEnv (sourceAction process word)) expression)

def pairedForward {s : Sorts} (expression : Expr PhysicalValue PhysicalVar s) :=
 SourceInventoryExecutionFeed.WordReceipt.liftTraceZero (forward readEnv word expression)

theorem forward_charge {s : Sorts} (expression : Expr PhysicalValue PhysicalVar s) :
 (forward readEnv word expression).length = remaining ((Context.embed readEnv expression).subst Context.binding) :=
 (forward readEnv word expression).length_to_const

end SourceOperationNative.Context.WordExecution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
