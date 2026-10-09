import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Curve
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation

open RootInquiryCompletion SourceOperationEffects SourceOperationScalarInventoryLift SourceOperationScalarPresentation SourceOperationScalarRelations
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Tail
open Lower.SourceFamily.Foresight.Contextual.Profile.Curve
namespace L
export Lower.SourceFamily.Foresight.Tail (State advance tail tail_after_actual_step)
end L
variable {S : Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t)
abbrev CurveShape := Sigma (EnvCurve (W:=W) (X:=X))
def shape (state:L.State (W:=W) (X:=X) (s:=s)) : CurveShape (W:=W) (X:=X) :=
 ⟨state.1,curve state.1 state.2⟩
def advanceShape (source:CurveShape (W:=W) (X:=X)) : CurveShape (W:=W) (X:=X) :=
 ⟨source.1+1,push binding source.1 source.2⟩
theorem source_advance (state:L.State (W:=W) (X:=X) (s:=s)) :
 shape (L.advance binding state)=advanceShape binding (shape state) :=
 congrArg (fun c=> (⟨state.1+1,c⟩:CurveShape (W:=W) (X:=X))) (replay_step_curve binding state.1 state.2)
theorem same_source_tail
 (left right:L.State (W:=W) (X:=X) (s:=s)) (same:shape left=shape right) (k:Nat) :
 shape (L.tail binding left k)=shape (L.tail binding right k) :=by
 induction k with
 | zero=>exact same
 | succ k previous=>
  exact (source_advance binding (L.tail binding left k)).trans
   ((congrArg (advanceShape binding) previous).trans (source_advance binding (L.tail binding right k)).symm)

variable (n:Nat) (data:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev actualNextState : L.State (W:=W) (X:=X) (s:=s) :=
 ⟨n+1,Lower.SourceFamily.step (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n data⟩
theorem actual_next_curve :
 shape (actualNextState binding n data)=shape (L.advance binding ⟨n,data⟩) :=
 congrArg (fun c=>(⟨n+1,c⟩:CurveShape (W:=W) (X:=X)))
  ((actual_step_curve binding n data).trans (replay_step_curve binding n data).symm)
theorem actual_next_all_curves (k:Nat) :
 shape (L.tail binding (actualNextState binding n data) k)=shape (L.tail binding ⟨n,data⟩ (k+1)) :=
 (same_source_tail binding (actualNextState binding n data) (L.advance binding ⟨n,data⟩)
  (actual_next_curve binding n data) k).trans
   (congrArg shape (L.tail_after_actual_step binding ⟨n,data⟩ k))

abbrev ReadShape := Sigma (fun j=>Env (PairValue (Lower.Value W j)) X)
def readShape (source:CurveShape (W:=W) (X:=X)) : ReadShape (W:=W) (X:=X) :=
 ⟨source.1,pairEnvironment (source.2 0)
   (SourceSubstitution.sourceEnvironment (Future.Replay.Binding.at binding source.1) (source.2 0)-source.2 0)⟩
def queryShape (state:L.State (W:=W) (X:=X) (s:=s)) : ReadShape (W:=W) (X:=X) :=
 ⟨state.1,Lower.SourceFamily.Foresight.environment binding state 0⟩
theorem query_source (state:L.State (W:=W) (X:=X) (s:=s)) :
 queryShape binding state=readShape binding (shape state) :=by
 apply congrArg (fun e=>(⟨state.1,e⟩:ReadShape (W:=W) (X:=X)))
 exact congrArg (fun raw=>raw.environment)
  (Lower.SourceFamily.Replay.factory_raw binding state.1 state.2.2 state.2.1)
theorem actual_next_all_reads (k:Nat) :
 queryShape binding (L.tail binding (actualNextState binding n data) k)=
 queryShape binding (L.tail binding ⟨n,data⟩ (k+1)) :=
 (query_source binding (L.tail binding (actualNextState binding n data) k)).trans
  ((congrArg (readShape binding) (actual_next_all_curves binding n data k)).trans
   (query_source binding (L.tail binding ⟨n,data⟩ (k+1))).symm)
end Lower.SourceFamily.Foresight.Contextual.Profile.Tail
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
