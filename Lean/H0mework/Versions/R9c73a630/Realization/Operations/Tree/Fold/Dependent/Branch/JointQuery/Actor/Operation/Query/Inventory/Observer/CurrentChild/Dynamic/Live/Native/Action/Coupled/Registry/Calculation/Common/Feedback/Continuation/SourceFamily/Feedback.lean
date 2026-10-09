import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Runtime
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Binding
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Written

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Lower.SourceFamily.Replay
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance familyGroups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (originalBinding : ∀ t,X t → Expr W X t)
def factory : Lower.SourceFamily.Factory W X s where
 datum n seed frame :=
  (Future.Replay.Move.Faces.configuration (Future.Replay.Installed.programme
   (Future.Replay.Binding.at originalBinding n) seed)).datum frame
 nextInventory n seed frame :=
  (Future.Replay.Installed.programme (Future.Replay.Binding.at originalBinding n) seed).nextInventory frame
 nextPairInventory n seed frame :=
  (Future.Replay.Installed.programme (Future.Replay.Binding.at originalBinding n) seed).nextPairInventory frame
 extraScalar n seed frame := some ((Future.Replay.Installed.scalarStock (Future.Replay.Binding.at originalBinding n) seed frame).map
  (T.liftEvent (W:=Lower.Value W n) (X:=X) (s:=s)))
 extraPair n seed frame := some ((Future.Replay.Installed.pairStock (Future.Replay.Binding.at originalBinding n) seed frame).map
  (T.liftEvent (W:=PairValue (Lower.Value W n)) (X:=X) (s:=s)))

theorem cfg_from_source (n : Nat) (seed : Lower.SourceFamily.Seed W X s n) :
 Lower.SourceFamily.cfg (factory (s:=s) originalBinding) n seed=
 Future.Replay.Move.cfg (Future.Replay.Binding.at originalBinding n) seed := rfl

theorem pair_from_source (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) :
 Lower.SourceFamily.pair (factory (s:=s) originalBinding) n data=
 Future.Replay.Move.pair (Future.Replay.Binding.at originalBinding n) data.2 data.1 := rfl

theorem scalar_from_source (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) :
 Lower.SourceFamily.scalar (factory (s:=s) originalBinding) n data=
 Future.Replay.Move.scalar (Future.Replay.Binding.at originalBinding n) data.2 data.1 := rfl

theorem factory_raw (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
 (frame : M.Frame (Value:=Lower.Value W n) (Var:=X) (sort:=s)) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
 (Lower.SourceFamily.cfg (factory (s:=s) originalBinding) n seed)).raw=
 Future.Replay.Source.raw (Future.Replay.Binding.at originalBinding n) seed
 (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
 (Future.Replay.Installed.Q.actualOccurrence frame) := congrArg (fun query => query.raw) (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame (Lower.SourceFamily.cfg (factory (s:=s) originalBinding) n seed))

theorem factory_paid (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n) (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (Future.Replay.Source.result
 (Future.Replay.Binding.at originalBinding n) data.2 data.1
 (Future.Replay.Installed.Q.actualOccurrence data.1)).2.1.2).trace) :
 T.liftEvent (W:=PairValue (Lower.Value W n)) (X:=X) (s:=s) event ∈
 (Lower.SourceFamily.pair (factory (s:=s) originalBinding) n data).trace := by
 have source := Future.Replay.Ledger.all_new_paid (Future.Replay.Binding.at originalBinding n) data.2 data.1 event present
 exact Eq.mpr (congrArg (fun stock => T.liftEvent (W:=PairValue (Lower.Value W n)) (X:=X) (s:=s) event ∈ stock.trace)
  (pair_from_source originalBinding n data)) source

end Lower.SourceFamily.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
