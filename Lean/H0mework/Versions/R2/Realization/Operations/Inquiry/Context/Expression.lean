import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Source
import H0mework.Realization.Operations.Execution.Run
import H0mework.Realization.Operations.Execution.Relations

/-! Original typed operations execute in the actual current/next source
reads. The pair executor preserves both ordered cross terms and their joint
effect without changing the original value types. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationScalarPresentation

variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)] {sort : Sorts}
variable (source : RawSource (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) runtime)

def pairEnvironmentAt (state : runtime.State) :=
  pairEnvironment (readEnv runtime source state) (increment runtime source state)

def pairValue (state : runtime.State) : PhysicalValue sort × PhysicalValue sort :=
  (liftExpr (raw runtime source state).expression).eval (pairEnvironmentAt runtime source state)

def pairTrace (state : runtime.State) :
    Trace (pairEnvironmentAt runtime source state) (liftExpr (raw runtime source state).expression)
      (.const (pairValue runtime source state)) :=
  execution (pairEnvironmentAt runtime source state) (liftExpr (raw runtime source state).expression)

theorem pair_value (state : runtime.State) : pairValue runtime source state =
    ((raw runtime source state).expression.eval (readEnv runtime source state),
      (raw runtime source state).expression.effect (readEnv runtime source state) (increment runtime source state)) :=
  eval_liftExpr _ _ _

theorem pair_trace_length (state : runtime.State) :
    (pairTrace runtime source state).length = remaining (liftExpr (raw runtime source state).expression) :=
  execution_length _ _

theorem next_value (state : runtime.State) :
    (raw runtime source state).expression.eval (readEnv runtime source state.tick.nextState) =
      (pairValue runtime source state).1 + (pairValue runtime source state).2 := by
  rw [pair_value, ← Expr.eval_update, updated_environment]

/-- Run the original expression at the actual successor read. The trace
keeps the current source syntax even when the successor has a new request. -/
def nextTrace (state : runtime.State) :
    Trace (readEnv runtime source state.tick.nextState) (raw runtime source state).expression
      (.const ((raw runtime source state).expression.eval (readEnv runtime source state.tick.nextState))) :=
  execution (readEnv runtime source state.tick.nextState) (raw runtime source state).expression

def oldTrace (state : runtime.State) :
    Trace (readEnv runtime source state) (raw runtime source state).expression
      (.const ((raw runtime source state).expression.eval (readEnv runtime source state))) :=
  execution (readEnv runtime source state) (raw runtime source state).expression

def relationWords (state : runtime.State) := (oldTrace runtime source state).relationWords (R := ℤ)

theorem relation_boundary (state : runtime.State) :
    relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state) =
      Finsupp.single (raw runtime source state).expression 1 -
        Finsupp.single (.const ((raw runtime source state).expression.eval (readEnv runtime source state))) 1 :=
  (oldTrace runtime source state).relation_boundary

theorem actual_updated_inverse (state : runtime.State) :
    (SourceGeneratedScalarDifferentialResidual.residualEquivRange
      (evaluation (R := ℤ) (readEnv runtime source state.tick.nextState))
      (SourceGeneratedScalarDifferentialResidual.canonicalResidual
        (evaluation (R := ℤ) (readEnv runtime source state.tick.nextState))
        (relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state)))).val =
      effectEvaluator (R := ℤ) (readEnv runtime source state) (increment runtime source state)
        (relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state)) := by
  have paid := (oldTrace runtime source state).updated_residual (R := ℤ) (increment runtime source state)
  rw [updated_environment] at paid
  exact paid

theorem actual_relation_cochain (state : runtime.State) :
    SourceOperationScalarCochain.boundary (R := ℤ)
      (relationMap (R := ℤ) (readEnv runtime source state) (relationWords runtime source state)) ∈
        LinearMap.range (relationMap (R := ℤ)
          (mixedEnvironment (readEnv runtime source state) (increment runtime source state))) :=
  (oldTrace runtime source state).relation_cochain (increment runtime source state)

end SourceOperationInquiry.Context
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
