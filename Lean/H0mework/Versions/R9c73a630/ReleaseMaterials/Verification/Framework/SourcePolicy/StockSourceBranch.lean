import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Admission
import H0mework.Versions.V2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePolicyStockSourceBranch
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme originalProgramme)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next nextBorn)
end A
namespace Complete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion
  (receipt atReceipt receipt_next receipt_compiles)
end Complete
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix
  (receipt_paid_prefix)
end Prefix
namespace Registry
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry (query)
end Registry
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
  (face consumer state presentation targetAt target_root target_current original_first_successor
    birthProgram compiles_paid compiles_settled successor_valid)
end ST
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (root visit same_ledger)
end SO
namespace SA
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockAdmission
  (compiles target_current successor_valid)
end SA
variable {S : Type u} {W X : S → Type u} [∀ slot, AddCommGroup (W slot)] {s : S}
variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (start : Nat)

abbrev selected := Complete.atReceipt cfg initial start
abbrev paidFrame (offset : Fin (Complete.receipt cfg initial start).1) :=
  A.frames initial cfg (start + offset.val)

theorem actual_paid_compiles (offset : Fin (Complete.receipt cfg initial start).1) : type_of%
    (ST.compiles_paid (paidFrame initial cfg start offset) cfg
      (Prefix.receipt_paid_prefix cfg initial start offset).1
      (Prefix.receipt_paid_prefix cfg initial start offset).2.down) :=
  ST.compiles_paid _ _ _ (Prefix.receipt_paid_prefix cfg initial start offset).2.down

theorem actual_paid_native_next (offset : Fin (Complete.receipt cfg initial start).1) :
    A.next (paidFrame initial cfg start offset) cfg = (paidFrame initial cfg start offset).mathNext := by
  unfold A.next
  rw [(Prefix.receipt_paid_prefix cfg initial start offset).2.down]

theorem actual_paid_preserves (offset : Fin (Complete.receipt cfg initial start).1) : type_of%
    (ST.successor_valid (paidFrame initial cfg start offset) cfg
      (Registry.query (paidFrame initial cfg start offset) cfg)) :=
  ST.successor_valid _ _ _

theorem actual_settled_compiles : type_of% (ST.compiles_settled (selected initial cfg start) cfg
    (Complete.receipt cfg initial start).2.1 (Complete.receipt cfg initial start).2.2.2) :=
  ST.compiles_settled _ _ _ (Complete.receipt cfg initial start).2.2.2

theorem actual_settled_not_answered :
    (ST.state (selected initial cfg start) cfg).compileInquiry (Registry.query (selected initial cfg start) cfg) ≠
      .answered (ST.face (selected initial cfg start) cfg) (ST.consumer (selected initial cfg start) cfg) := by
  rw [actual_settled_compiles]
  intro impossible
  cases impossible

theorem actual_settled_literal_next : A.next (selected initial cfg start) cfg =
    A.nextBorn (selected initial cfg start) cfg := by
  unfold A.next
  rw [(Complete.receipt cfg initial start).2.2.2]

theorem actual_settled_preserves : type_of% (ST.successor_valid (selected initial cfg start) cfg
    (Registry.query (selected initial cfg start) cfg)) := ST.successor_valid _ _ _

variable (event : ExactTemporalCausalRootEventAt
  (SO.root (selected initial cfg start) cfg).toAuthoritativeRoot.toLedgerRoot
  (SO.visit (selected initial cfg start) cfg))

example : type_of% (ST.target_root (selected initial cfg start) cfg event) := ST.target_root _ _ _
example : type_of% (ST.target_current (selected initial cfg start) cfg event) := ST.target_current _ _ _
example : type_of% (ST.original_first_successor (selected initial cfg start) cfg event) :=
  ST.original_first_successor _ _ _

example : HEq (ST.targetAt (selected initial cfg start) cfg event).receipt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt
      (selected initial cfg start) cfg event).receipt := HEq.rfl
example : HEq (ST.targetAt (selected initial cfg start) cfg event).initialOldRow
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt
      (selected initial cfg start) cfg event).initialOldRow := HEq.rfl
example : HEq (ST.targetAt (selected initial cfg start) cfg event).initialBornRow
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.targetAt
      (selected initial cfg start) cfg event).initialBornRow := HEq.rfl
example : (A.nextBorn (selected initial cfg start) cfg).inventory =
    cfg.nextInventory (selected initial cfg start) := rfl
example : (A.nextBorn (selected initial cfg start) cfg).pairInventory =
    cfg.nextPairInventory (selected initial cfg start) := rfl
example : type_of% (SO.same_ledger (selected initial cfg start) cfg) := SO.same_ledger _ _
example : type_of% (Complete.receipt_compiles cfg initial start) := Complete.receipt_compiles _ _ _
example : type_of% (Complete.receipt_next cfg initial start) := Complete.receipt_next _ _ _

variable (scalar : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (SourceOperationScalarInventoryLift.PairValue W) cfg.LowVar s)))
variable (pair : RootedAccountedUnfolding (PresentedRelationEventAt
  (Expr (SourceOperationScalarInventoryLift.PairValue (SourceOperationScalarInventoryLift.PairValue W)) cfg.LowVar s)))
variable (receiverCfg : A.Programme
  (PhysicalValue := SourceOperationScalarInventoryLift.PairValue W) (PhysicalVar := cfg.LowVar) (sort := s))
example : type_of% (SA.compiles initial cfg scalar pair receiverCfg) := SA.compiles _ _ _ _ _
example : type_of% (SA.target_current initial cfg scalar pair receiverCfg
    ((SO.root initial cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit initial cfg))) :=
  SA.target_current _ _ _ _ _ _

#print axioms ST.target_current
#print axioms ST.successor_valid
#print axioms actual_paid_compiles
#print axioms actual_paid_native_next
#print axioms actual_settled_compiles
#print axioms actual_settled_not_answered
#print axioms actual_settled_literal_next
end SourcePolicyStockSourceBranch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
