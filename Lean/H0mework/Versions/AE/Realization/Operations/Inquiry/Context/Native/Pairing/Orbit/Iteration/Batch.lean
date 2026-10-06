import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration
import H0mework.Realization.Operations.Execution.InventoryVector.Source
set_option autoImplicit false
noncomputable section
universe u z
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (seed : Expr Value (O.Var Var) slot) (count : Nat)
abbrev Index := Fin (count+1)
def term (index : Index count) := liftExpr (iterate seed index.val)
def items := List.ofFn (fun index : Index count => (index,term seed count index))
def query := InventoryVector.query (Index count) (items seed count)
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
variable (state : runtime.State)
def environment := InventoryVector.environment (Index count)
 (pairEnvironment (old runtime source state) (increment runtime source state))
def trace := execution (environment count runtime source state) (query seed count)
theorem coordinate (index : Index count) :
 (query seed count).eval (environment count runtime source state) index=
 ((iterate seed index.val).eval (old runtime source state),
  (iterate seed index.val).effect (old runtime source state) (increment runtime source state)) := by
 have read := InventoryVector.query_read (Index count) (items seed count)
  (pairEnvironment (old runtime source state) (increment runtime source state)) index
 have single : ((items seed count).map (fun item => if index=item.1 then
   item.2.eval (pairEnvironment (old runtime source state) (increment runtime source state)) else 0)).sum=
  (term seed count index).eval (pairEnvironment (old runtime source state) (increment runtime source state)) := by
  simp only [items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : Index count => (term seed count coordinate).eval
    (pairEnvironment (old runtime source state) (increment runtime source state)))
   |>.trans (if_pos (Finset.mem_univ index))
 exact read.trans (single.trans (eval_liftExpr _ _ _))
theorem class_coordinate (index : Index count) :
 (query seed count).eval (environment count runtime source state) index=
 read runtime source state (actedClass runtime source seed index.val) :=
 (coordinate seed count runtime source state index).trans (class_read runtime source state seed index.val).symm
private theorem list_charge {Index : Type z} (entries : List (Index × Expr (PairValue Value) (O.Var Var) slot)) :
 InventoryVector.charge Index entries=(entries.map (fun item => remaining item.2)).sum+2*entries.length := by
 induction entries with
 | nil => rfl
 | cons head tail previous =>
  simp only [InventoryVector.charge,List.map_cons,List.sum_cons,List.length_cons,previous]
  omega
theorem query_charge : remaining (query seed count)=totalCost seed count+2*(count+1) := by
 rw [query,InventoryVector.query_charge,list_charge]
 simp only [items,List.map_ofFn,List.length_ofFn,term,totalCost]
 rfl
theorem complete_charge : (trace seed count runtime source state).length=totalCost seed count+2*(count+1) :=
 (execution_length _ _).trans (query_charge seed count)
end SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
