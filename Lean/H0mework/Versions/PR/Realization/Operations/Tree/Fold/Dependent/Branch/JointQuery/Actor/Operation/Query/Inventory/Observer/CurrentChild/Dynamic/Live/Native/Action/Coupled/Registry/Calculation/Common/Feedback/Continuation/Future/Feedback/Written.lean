import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Future.Feedback.Next
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Future.Replay
namespace Ledger
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
variable (binding : ∀ t,X t → Expr W X t)
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr W X s)))
variable (frame : M.Frame (Value:=W) (Var:=X) (sort:=s))

theorem stock_generated {α : Type u} (prior : Option (RootedAccountedUnfolding α))
 (generated : RootedAccountedUnfolding α) (event : α) (present : event ∈ generated.trace) :
 event ∈ (Stock.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some old => exact (SourceHistoryCommon.parallel_right _ _ _).1 _ present

theorem pair_written (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (Source.pairWritten binding seed frame (Installed.Q.actualOccurrence frame)).trace) :
 event ∈ (Installed.pairStock binding seed frame).trace := stock_generated _ _ _ present

theorem original_paid (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (Original.Request.Inverse.paidWritten seed frame (Installed.Q.actualOccurrence frame)).trace) :
 event ∈ (Installed.pairStock binding seed frame).trace :=
 pair_written binding seed frame event (Read.original_events binding seed frame _ _ present)

theorem new_paid (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.result binding seed frame (Installed.Q.actualOccurrence frame)).2.1.2).trace) :
 event ∈ (Installed.pairStock binding seed frame).trace :=
 pair_written binding seed frame event (Read.paid_events binding seed frame _ _ present)

theorem new_replay (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.replayTrace binding seed frame (Installed.Q.actualOccurrence frame))).trace) :
 event ∈ (Installed.pairStock binding seed frame).trace :=
 pair_written binding seed frame event (Read.replay_events binding seed frame _ _ present)

theorem actual_pair_carried (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (Installed.pairStock binding seed frame).trace) :
 T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event ∈ (Move.pair binding seed frame).trace := by
 have mapped : T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event ∈
  ((Installed.pairStock binding seed frame).map (T.liftEvent (W:=PairValue W) (X:=X) (s:=s))).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem present
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ mapped

theorem actual_scalar_carried (event : PresentedRelationEventAt (Expr W X s))
 (present : event ∈ (Installed.scalarStock binding seed frame).trace) :
 T.liftEvent (W:=W) (X:=X) (s:=s) event ∈ (Move.scalar binding seed frame).trace := by
 have mapped : T.liftEvent (W:=W) (X:=X) (s:=s) event ∈
  ((Installed.scalarStock binding seed frame).map (T.liftEvent (W:=W) (X:=X) (s:=s))).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem present
 exact (SourceHistoryCommon.parallel_left _ _ _).1 _ mapped

theorem receiver_pair_inventory : (Move.receiver binding seed frame).pairInventory=some (Move.pair binding seed frame) := rfl

theorem receiver_scalar_inventory : (Move.receiver binding seed frame).inventory=some (Move.scalar binding seed frame) := rfl

theorem all_new_paid (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.result binding seed frame (Installed.Q.actualOccurrence frame)).2.1.2).trace) :
 T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event ∈ (Move.pair binding seed frame).trace :=
 actual_pair_carried binding seed frame event (new_paid binding seed frame event present)

theorem all_new_replay (event : PresentedRelationEventAt (Expr (PairValue W) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (Source.replayTrace binding seed frame (Installed.Q.actualOccurrence frame))).trace) :
 T.liftEvent (W:=PairValue W) (X:=X) (s:=s) event ∈ (Move.pair binding seed frame).trace :=
 actual_pair_carried binding seed frame event (new_replay binding seed frame event present)

end Ledger
end Future.Replay
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
