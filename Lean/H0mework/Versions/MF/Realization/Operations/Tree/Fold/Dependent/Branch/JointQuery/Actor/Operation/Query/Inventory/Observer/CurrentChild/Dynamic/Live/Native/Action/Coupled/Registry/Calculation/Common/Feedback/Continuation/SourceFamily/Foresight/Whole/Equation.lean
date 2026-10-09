import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Generation
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Elimination
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Whole
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

def realDecoder := Lower.SourceFamily.Foresight.Contextual.Effect.actualDecoder binding n data
def realIncrement := Lower.SourceFamily.Foresight.Contextual.Effect.actualIncrement binding n data

namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query)
end Q
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E

theorem epoch_of_zero (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) (depth : frame.depth=0) :
 E.epoch frame=frame := by
 cases frame with
 | mk N V old registered packetAt environment frameDepth inventory pairInventory =>
  change frameDepth=0 at depth
  cases depth
  rfl

theorem model_environment_zero (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 Lower.SourceFamily.Foresight.environment binding (I.nativeState n seed frame) 0=
 (Q.query (E.epoch frame) (Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding) n seed)).raw.environment := rfl

theorem source_environment_same (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 (Q.query frame (Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding) n seed)).raw.environment=
 (Q.query frame (Lower.SourceFamily.cfg (F.factory (s:=s) binding) n seed)).raw.environment :=
 (congrArg (fun raw => raw.environment) (Lower.SourceFamily.Replay.factory_raw binding n seed frame)).trans
 (Lower.SourceFamily.Foresight.Contextual.factory_environment binding n seed frame).symm


theorem native_environment_zero (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) (depth : frame.depth=0) :
 Lower.SourceFamily.Foresight.environment binding (I.nativeState n seed frame) 0=
 (Q.query frame (Lower.SourceFamily.cfg (F.factory (s:=s) binding) n seed)).raw.environment :=
 (model_environment_zero binding n seed frame).trans
 ((congrArg (fun physical => (Q.query physical
  (Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s:=s) binding) n seed)).raw.environment)
  (epoch_of_zero n frame depth)).trans (source_environment_same binding n seed frame))

theorem actual_next_update (t : S) (word : Word binding n data t) :
 nextPrefix binding n data t 0 (fullMap binding n data t word) ⟨0,by omega⟩=
 updateInventory (R:=ℤ) (s:=t) (realDecoder binding n data) (realIncrement binding n data) word := by
 have futureRead := next_prefix binding n data t 0 word
 have head := congrArg (fun values => values ⟨0,by omega⟩) futureRead
 apply head.trans
 have envLaw := native_environment_zero binding (n+1) (actualNext binding n data).2 (actualNext binding n data).1 rfl
 have generated := Lower.SourceFamily.Foresight.Contextual.Effect.actual_word binding n data t word
 exact (congrArg (fun environment => evaluation (R:=ℤ) (s:=t) environment (action binding n data t word)) envLaw).trans generated

theorem actual_high_dual (depth : data.1.depth=0) (t : S) : dual binding n data t=
 Lower.SourceFamily.Foresight.Contextual.Elimination.dual binding n data.2 data.1 depth t := rfl

theorem actual_high_head (t : S) (word : Word binding n data t) :
 Lower.SourceFamily.Foresight.Contextual.Elimination.prefixRead binding (n+1) (actualNext binding n data).2
  (actualNext binding n data).1 rfl t 0 (nextRestriction binding n data t (fullMap binding n data t word)) ⟨0,by omega⟩=
 updateInventory (R:=ℤ) (s:=t) (realDecoder binding n data) (realIncrement binding n data) word := actual_next_update _ _ _ _ _

theorem actual_coordinate_update (t : S) (name : X t) : type_of%
 (actual_high_head binding n data t (coordinate binding n data t name)) := actual_high_head _ _ _ _ _
theorem actual_raw_update : type_of% (actual_high_head binding n data s (rawWord binding n data)) := actual_high_head _ _ _ _ _
theorem source_effect_consumption (bound : Nat) :
 type_of% (actual_raw_update binding n data) ∧ type_of% (actual_raw_prefix binding n data bound) ∧
 type_of% (actual_raw_residual binding n data) ∧ type_of% (actual_whole_root binding n data) :=
 ⟨actual_raw_update _ _ _,actual_raw_prefix _ _ _ _,actual_raw_residual _ _ _,actual_whole_root _ _ _⟩
end Lower.SourceFamily.Foresight.Whole
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
