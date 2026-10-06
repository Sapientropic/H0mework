import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Finite
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Orbit.Iteration.Batch
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Finite.Batch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
namespace B
export SourceOperationInquiry.Context.Native.Pairing.Orbit.Batch (Index items query term)
end B
namespace P
export SourceOperationInquiry.Context.Native.Pairing.Orbit (iterate)
end P
variable (seed : Expr Value (Orbit.Var Var) slot) (count : Nat)
def bound := Finset.univ.sup (fun index : B.Index count => depth (P.iterate seed index.val))
theorem depth_bounded (index : B.Index count) : depth (P.iterate seed index.val)≤bound seed count :=
 Finset.le_sup (f:=fun index : B.Index count => depth (P.iterate seed index.val)) (Finset.mem_univ index)
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
variable (offset : Nat)
abbrev observations := environments runtime source offset (bound seed count)
def environment := InventoryVector.environment (B.Index count)
 (pairEnvironment (finiteOld runtime source offset (bound seed count)) (finiteIncrement runtime source offset (bound seed count)))
def trace := execution (environment seed count runtime source offset) (B.query seed count)
theorem coordinate (index : B.Index count) :
 (B.query seed count).eval (environment seed count runtime source offset) index=
 ((P.iterate seed index.val).eval (Pairing.Orbit.old runtime source (runtime.stateAt offset)),
  (P.iterate seed index.val).effect (Pairing.Orbit.old runtime source (runtime.stateAt offset))
   (Pairing.Orbit.increment runtime source (runtime.stateAt offset))) := by
 have read := InventoryVector.query_read (B.Index count) (B.items seed count)
  (pairEnvironment (finiteOld runtime source offset (bound seed count)) (finiteIncrement runtime source offset (bound seed count))) index
 have single : ((B.items seed count).map (fun item => if index=item.1 then item.2.eval
  (pairEnvironment (finiteOld runtime source offset (bound seed count)) (finiteIncrement runtime source offset (bound seed count))) else 0)).sum=
  (B.term seed count index).eval
   (pairEnvironment (finiteOld runtime source offset (bound seed count)) (finiteIncrement runtime source offset (bound seed count))) := by
  simp only [B.items,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_ite_eq (s:=Finset.univ) index
   (fun coordinate : B.Index count => (B.term seed count coordinate).eval
    (pairEnvironment (finiteOld runtime source offset (bound seed count)) (finiteIncrement runtime source offset (bound seed count))))
   |>.trans (if_pos (Finset.mem_univ index))
 exact read.trans (single.trans ((eval_liftExpr _ _ _).trans
  (finite_pair_bound runtime source (P.iterate seed index.val) offset (bound seed count) (depth_bounded seed count index))))
theorem original_query : (B.query seed count).eval (environment seed count runtime source offset)=
 (B.query seed count).eval (Pairing.Orbit.Batch.environment count runtime source (runtime.stateAt offset)) := by
 funext index
 exact (coordinate seed count runtime source offset index).trans
  (Pairing.Orbit.Batch.coordinate seed count runtime source (runtime.stateAt offset) index).symm
end SourceOperationInquiry.Context.Native.Orbit.Finite.Batch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
