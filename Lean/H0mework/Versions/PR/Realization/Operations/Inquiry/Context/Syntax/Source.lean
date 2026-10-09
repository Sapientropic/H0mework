import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Expression

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Syntax
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) runtime)
variable (state : runtime.State)

-- The current and successor requests are independently read from this runtime.
def currentWord : Formal ℤ PhysicalValue PhysicalVar sort :=
 Finsupp.single (raw runtime source state).expression 1
def nextWord : Formal ℤ PhysicalValue PhysicalVar sort :=
 Finsupp.single (raw runtime source state.tick.nextState).expression 1
def deltaWord := nextWord runtime source state - currentWord runtime source state
def deltaValue := evaluation (R:=ℤ) (readEnv runtime source state.tick.nextState)
 (deltaWord runtime source state)
def successorTrace := oldTrace runtime source state.tick.nextState

def successorRelation := (successorTrace runtime source state).relationWords (R:=ℤ)
theorem successor_boundary : relationMap (R:=ℤ) (readEnv runtime source state.tick.nextState)
 (successorRelation runtime source state) = nextWord runtime source state -
 Finsupp.single (.const ((raw runtime source state.tick.nextState).expression.eval
  (readEnv runtime source state.tick.nextState))) 1 :=
 (successorTrace runtime source state).relation_boundary

theorem delta_value : deltaValue runtime source state =
 (raw runtime source state.tick.nextState).expression.eval (readEnv runtime source state.tick.nextState) -
 (raw runtime source state).expression.eval (readEnv runtime source state.tick.nextState) := by
 simp only [deltaValue,deltaWord,map_sub,nextWord,currentWord,evaluation,
  Finsupp.linearCombination_single,one_smul]

theorem successor_trace_length : (successorTrace runtime source state).length =
 remaining (raw runtime source state.tick.nextState).expression :=
 execution_length _ _

theorem moving_equation :
 (raw runtime source state.tick.nextState).expression.eval (readEnv runtime source state.tick.nextState) -
 (raw runtime source state).expression.eval (readEnv runtime source state) =
 (raw runtime source state).expression.effect (readEnv runtime source state) (increment runtime source state) +
 deltaValue runtime source state := by
 have effect := Expr.eval_update (raw runtime source state).expression
  (readEnv runtime source state) (increment runtime source state)
 rw [updated_environment] at effect
 rw [delta_value,effect]
 abel


variable (count : Nat)
-- Result equalities are posterior readouts; both Raw requests are source-owned.
theorem stage_result_equation (currentValue nextValue : PhysicalValue sort)
 (currentPaid : (raw runtime source (runtime.stateAt count)).expression.eval
  (readEnv runtime source (runtime.stateAt count)) = currentValue)
 (nextPaid : (raw runtime source (runtime.stateAt (count+1))).expression.eval
  (readEnv runtime source (runtime.stateAt (count+1))) = nextValue) :
 nextValue-currentValue = (raw runtime source (runtime.stateAt count)).expression.effect
  (readEnv runtime source (runtime.stateAt count)) (increment runtime source (runtime.stateAt count)) +
 deltaValue runtime source (runtime.stateAt count) := by
 have generated := moving_equation runtime source (runtime.stateAt count)
 change (raw runtime source (runtime.stateAt (count+1))).expression.eval
   (readEnv runtime source (runtime.stateAt (count+1))) -
  (raw runtime source (runtime.stateAt count)).expression.eval (readEnv runtime source (runtime.stateAt count)) = _ at generated
 rw [currentPaid,nextPaid] at generated
 exact generated

end SourceOperationInquiry.Context.Syntax
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
