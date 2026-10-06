import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Action
import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Exposure
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing.Orbit
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
def iterate (seed : Expr Value (O.Var Var) slot) : Nat → Expr Value (O.Var Var) slot
 | 0 => seed
 | count+1 => (iterate seed count).subst O.binding
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
def actedClass (seed : Expr Value (O.Var Var) slot) : Nat → Carrier runtime source
 | 0 => canonical runtime source (Finsupp.single seed (1:ℤ))
 | count+1 => action runtime source (actedClass seed count)
theorem class_source (seed : Expr Value (O.Var Var) slot) (count : Nat) :
 actedClass runtime source seed count=canonical runtime source (Finsupp.single (iterate seed count) (1:ℤ)) := by
 induction count with
 | zero => rfl
 | succ count previous =>
  rw [actedClass,previous,action_source]
  change canonical runtime source (substitution (R:=ℤ) O.binding (Finsupp.single (iterate seed count) (1:ℤ)))=_
  rw [substitution,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rfl

def trace (state : runtime.State) (seed : Expr Value (O.Var Var) slot) (count : Nat) :=
 execution (pairEnvironment (old runtime source state) (increment runtime source state)) (liftExpr (iterate seed count))
def prefixTraces (state : runtime.State) (seed : Expr Value (O.Var Var) slot) (count : Nat) :=
 List.ofFn (fun index : Fin (count+1) => SourceOperationPaidRelations.exposure (trace runtime source state seed index.val))
def inventory (state : runtime.State) (seed : Expr Value (O.Var Var) slot) : Nat →
 RootedAccountedUnfolding (CofinalHistorySettlement.PresentedRelationEventAt (Expr (PairValue Value) (O.Var Var) slot))
 | 0 => SourceOperationPaidRelations.exposure (trace runtime source state seed 0)
 | count+1 => SourceHistoryCommon.seed (inventory state seed count)
   (SourceOperationPaidRelations.exposure (trace runtime source state seed (count+1)))
def totalCost (seed : Expr Value (O.Var Var) slot) (count : Nat) :=
 (List.ofFn (fun index : Fin (count+1) => remaining (liftExpr (iterate seed index.val)))).sum
theorem class_read (state : runtime.State) (seed : Expr Value (O.Var Var) slot) (count : Nat) :
 read runtime source state (actedClass runtime source seed count)=
 ((iterate seed count).eval (old runtime source state),(iterate seed count).effect (old runtime source state) (increment runtime source state)) := by
 rw [class_source,read_source]
 apply Prod.ext
 · change evaluation (R:=ℤ) _ (Finsupp.single (iterate seed count) (1:ℤ))=_
   rw [evaluation,Finsupp.linearCombination_single,one_smul]
 · change effectEvaluator (R:=ℤ) _ _ (Finsupp.single (iterate seed count) (1:ℤ))=_
   rw [effectEvaluator,Finsupp.linearCombination_single,one_smul]

theorem complete_charge (state : runtime.State) (seed : Expr Value (O.Var Var) slot) (count : Nat) :
 (List.ofFn (fun index : Fin (count+1) => (trace runtime source state seed index.val).length)).sum=totalCost seed count := by
 apply congrArg List.sum
 apply congrArg List.ofFn
 funext index
 exact execution_length _ _
theorem complete_inventory (state : runtime.State) (seed : Expr Value (O.Var Var) slot) (count : Nat)
 (index : Fin (count+1)) (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (trace runtime source state seed index.val)).trace) :
 event ∈ (inventory runtime source state seed count).trace := by
 induction count with
 | zero =>
  have h : index.val=0 := by omega
  have same := congrArg (fun n => (SourceOperationPaidRelations.exposure (trace runtime source state seed n)).trace) h
  exact same ▸ present
 | succ count previous =>
  by_cases last : index.val=count+1
  · apply (SourceHistoryCommon.parallel_right _ _ _).1
    have same := congrArg (fun n => (SourceOperationPaidRelations.exposure (trace runtime source state seed n)).trace) last
    exact same ▸ present
  · apply (SourceHistoryCommon.parallel_left _ _ _).1
    exact previous ⟨index.val,by omega⟩ present
end SourceOperationInquiry.Context.Native.Pairing.Orbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
