import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Installation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryReceipt

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock
 (nativeAdmissionEvent native_seed_query_receipt)
abbrev admissionEvent := @nativeAdmissionEvent
namespace ReceiptLift
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (liftEvent liftedInventory priorPairInventory)
end ReceiptLift
namespace ReceiptMap
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (mapped_trace)
end ReceiptMap
section Receipt
variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
local instance receiptGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (factory : SF.Factory W X ()) (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

variable (code : Expr (PairValue W) X ())
variable (generated : factory=AI.withActualInput code (SF.defaultFactory W X ()))
variable (sourceFrame : A.M.Frame (Value:=L.Value W (AS.nativeAfterAdmission factory packet).1) (Var:=X) (sort:=()))

/-- The installed primary face consumes its supplied native seed as material, at this actual occurrence. -/
theorem native_seed_root_receipt
 (event) (belongs : event∈(AS.nativeAfterAdmission factory packet).2.1.2.trace) :
 event∈(actualRootRead code factory generated packet sourceFrame).1.1.1.1.2.1.trace := by
 exact Eq.mpr
  (congrArg (fun material => event∈material.1.1.1.1.2.1.trace)
   (actual_root_read code factory generated packet sourceFrame))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.supplied_seed_preserved
   (AS.nativeAfterAdmission factory packet).2.1.2 sourceFrame event belongs)

/-- The next Joint consumes every supplied event in its actual complete written inventory. -/
theorem native_seed_joint_receipt
 (event) (belongs : event∈(AS.nativeAfterAdmission factory packet).2.1.2.trace) :
 ReceiptLift.liftEvent event∈(actualWritten code factory generated packet sourceFrame).trace := by
 apply Eq.mpr
  (congrArg (fun inventory => ReceiptLift.liftEvent event∈inventory.trace)
   (actual_written code factory generated packet sourceFrame))
 apply SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.complete_written_preserves
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 have lifted : ReceiptLift.liftEvent event∈(ReceiptLift.liftedInventory
  (AS.nativeAfterAdmission factory packet).2.1.2 (A.epoch sourceFrame) (S.actualOccurrence sourceFrame)).trace := by
  rw [ReceiptLift.liftedInventory,ReceiptMap.mapped_trace]
  exact List.mem_map.mpr ⟨event,
   SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.supplied_seed_preserved
    (AS.nativeAfterAdmission factory packet).2.1.2 sourceFrame event belongs,rfl⟩
 unfold ReceiptLift.priorPairInventory
 cases (A.epoch sourceFrame).pairInventory with
 | none => exact lifted
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 _ lifted

/-- A configured source receipt is read by the newly installed primary Joint face. -/
theorem native_query_root_receipt
 (stock : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X ())))
 (written : packet.2.2.1.nextPairInventory packet.2.1.1=some stock)
 (event) (belongs : event∈stock.trace) :
 admissionEvent factory packet event∈
  (actualRootRead code factory generated packet sourceFrame).1.1.1.1.2.1.trace :=
 native_seed_root_receipt factory packet code generated sourceFrame _
  (native_seed_query_receipt factory packet stock written event belongs)
end Receipt
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
