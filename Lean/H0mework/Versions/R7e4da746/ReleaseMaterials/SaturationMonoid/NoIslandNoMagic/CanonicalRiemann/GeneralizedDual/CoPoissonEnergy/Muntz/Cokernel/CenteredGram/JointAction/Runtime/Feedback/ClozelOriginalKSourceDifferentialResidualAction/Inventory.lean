import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Factory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Stock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end Stock
namespace Native
export ActualCofinalSourceAction (bornStock bornPairStock selected paid_prefix_stocks whole_paid_in_born generated_joint_in_born)
end Native
namespace AN
export ActualNativeRelationTransport (paid new_relation_in_born new_relation_face new_cochain_face new_differential new_whole_recovery new_full_trace)
end AN
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance inventoryGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (grade : Nat)
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=L.Value W grade) (Var:=X) (sort:=()))

/-- Execution follows the original paid-state relation and actual update, preserving every residual syntax child. -/
def sourceResidualExecution := execution
 (sourceResidualEnvironment (A.epoch frame) (S.actualOccurrence frame))
 (sourceResidualCode (A.epoch frame) (S.actualOccurrence frame))

def sourceResidualPairExecution := execution
 (pairEnvironment (sourceResidualEnvironment (A.epoch frame) (S.actualOccurrence frame)) 0)
 (liftExpr (sourceResidualCode (A.epoch frame) (S.actualOccurrence frame)))

/-- These auxiliary words preserve both old callbacks; query-zero does not identify native source increment with zero. -/
def sourceResidualStockFactory (mother : SF.Factory W X ()) : SF.Factory W X () :=
 {mother with
  extraScalar:=fun n seed sourceFrame=>some (Stock.preserve (mother.extraScalar n seed sourceFrame)
   (SourceOperationPaidRelations.exposure (sourceResidualExecution n sourceFrame))),
  extraPair:=fun n seed sourceFrame=>some (Stock.preserve (mother.extraPair n seed sourceFrame)
   (SourceOperationPaidRelations.exposure (sourceResidualPairExecution n sourceFrame)))}

def sourceCompleteResidualFactory (mother : SF.Factory W X ()) :=
 sourceResidualFactory (sourceResidualStockFactory mother)

def sourceCompleteResidualPacket (mother : SF.Factory W X ())
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=())) := sourceResidualPacket (sourceResidualStockFactory mother) packet

private theorem source_right {α : Type} (prior : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) : event∈(Stock.preserve prior next).trace := by
 cases prior with
 | none=>exact present
 | some prior=>exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

variable (mother : SF.Factory W X ()) (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

theorem source_residual_scalar_nodes (event)
 (present : event∈(SourceOperationPaidRelations.exposure (sourceResidualExecution packet.1 packet.2.1.1)).trace) :
 event∈(Native.bornStock (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet)).trace := by
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(Stock.preserve (Native.selected (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet)).inventory _).trace
 rw [(Native.paid_prefix_stocks (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet) _ (Nat.le_refl _)).1]
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 apply SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock.scalar_legacy_preserved
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 exact source_right _ _ _ present

theorem source_residual_pair_nodes (event)
 (present : event∈(SourceOperationPaidRelations.exposure (sourceResidualPairExecution packet.1 packet.2.1.1)).trace) :
 event∈(Native.bornPairStock (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet)).trace := by
 change event∈(Stock.preserve (Native.selected (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet)).pairInventory _).trace
 rw [(Native.paid_prefix_stocks (sourceCompleteResidualFactory mother) (sourceCompleteResidualPacket mother packet) _ (Nat.le_refl _)).2]
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 exact source_right _ _ _ present

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
