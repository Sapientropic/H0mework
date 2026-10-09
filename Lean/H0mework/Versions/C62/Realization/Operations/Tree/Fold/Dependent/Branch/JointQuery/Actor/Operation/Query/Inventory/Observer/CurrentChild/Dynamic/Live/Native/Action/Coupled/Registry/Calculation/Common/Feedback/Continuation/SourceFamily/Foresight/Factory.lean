import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Installation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight
variable {S : Type u} {W X : S → Type u} [∀ t, AddCommGroup (W t)] {s : S}
attribute [local instance] sourceGroups
variable (binding : ∀ t, X t → Expr W X t)
def factory : Lower.SourceFamily.Factory W X s :=
  {Lower.SourceFamily.Replay.factory (s := s) binding with
    datum := fun n seed frame => (Installed.configuration binding n seed).datum frame}

theorem factory_configuration (n : Nat) (seed : Lower.SourceFamily.Seed W X s n) :
    Lower.SourceFamily.cfg (factory (s := s) binding) n seed = Installed.configuration binding n seed := rfl

theorem factory_reader (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
    (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s))
    (index : Installed.OccurrenceIndex n frame) :
    ((Lower.SourceFamily.cfg (factory (s := s) binding) n seed).datum frame).reader index.2 =
      ((Lower.SourceFamily.cfg (Lower.SourceFamily.Replay.factory (s := s) binding) n seed).datum frame).reader index.2 := rfl

theorem factory_decoder (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
    (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s)) :
    ((Lower.SourceFamily.cfg (factory (s := s) binding) n seed).datum frame).nextEnvironmentRead =
      some (fun _ => Installed.sourceDecoder binding n seed frame) := rfl

theorem factory_raw (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
    (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s)) :
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
      (Lower.SourceFamily.cfg (factory (s := s) binding) n seed)).raw =
      Future.Replay.Source.raw (Future.Replay.Binding.at binding n) seed
        (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
        (Future.Replay.Installed.Q.actualOccurrence frame) :=
  congrArg (fun query => query.raw)
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_generated frame
      (Lower.SourceFamily.cfg (factory (s := s) binding) n seed))

theorem factory_fee (n : Nat) (seed : Lower.SourceFamily.Seed W X s n)
    (frame : M.Frame (Value := Lower.Value W n) (Var := X) (sort := s)) :
    2≤remaining (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame
      (Lower.SourceFamily.cfg (factory (s := s) binding) n seed)).raw.expression := by
  have source := factory_raw binding n seed frame
  have fee := Lower.SourceFamily.Effect.source_fee (Future.Replay.Binding.at binding n) seed
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
    (Future.Replay.Installed.Q.actualOccurrence frame)
  exact Eq.mpr (congrArg (fun raw => 2≤remaining raw.expression) source)
    (le_trans (by decide : 2≤3) fee)

theorem factory_written (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
    (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))
    (present : event ∈ (Future.Replay.Source.pairWritten (Future.Replay.Binding.at binding n)
      data.2 data.1 (Future.Replay.Installed.Q.actualOccurrence data.1)).trace) :
    T.liftEvent event ∈ (Lower.SourceFamily.pair (factory (s:=s) binding) n data).trace := by
  have source := Future.Replay.Ledger.pair_written (Future.Replay.Binding.at binding n)
    data.2 data.1 event present
  have mapped : T.liftEvent event ∈
      ((Future.Replay.Installed.pairStock (Future.Replay.Binding.at binding n) data.2 data.1).map T.liftEvent).trace := by
    rw [T.mapped_trace]
    exact List.mem_map_of_mem source
  exact (SourceHistoryCommon.parallel_left _ _ _).1 _ mapped

theorem factory_paid (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
    (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))
    (present : event ∈ (SourceOperationPaidRelations.exposure (Future.Replay.Source.result
      (Future.Replay.Binding.at binding n) data.2 data.1 (Future.Replay.Installed.Q.actualOccurrence data.1)).2.1.2).trace) :
    T.liftEvent event ∈ (Lower.SourceFamily.pair (factory (s:=s) binding) n data).trace :=
  factory_written binding n data event (Future.Replay.Read.paid_events
    (Future.Replay.Binding.at binding n) data.2 data.1 _ event present)
end Lower.SourceFamily.Foresight
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
