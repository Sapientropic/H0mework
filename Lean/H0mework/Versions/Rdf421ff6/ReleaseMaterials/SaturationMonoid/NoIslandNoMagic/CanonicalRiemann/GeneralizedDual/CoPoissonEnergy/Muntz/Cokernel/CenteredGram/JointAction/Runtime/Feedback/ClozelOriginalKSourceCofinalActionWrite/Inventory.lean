import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Packet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Activation.QueryStock
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource.QueryStock (scalar_legacy_preserved legacyStock)
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
 (withCalculation codeAt actual_source_code actual_updated_total next_action_code next_actual_updated_total cofinal_source_code native_after_admission_code born_after_native_code)
end CF
namespace CM
export SourceFamilyActualCurrentMaterialEnvironmentUpdate (queryFactory reader reader_pair reader_paid_environment actual_action_isLeft)
end CM
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch Programme)
end A
namespace I
export SourceOperationInquiry.Context.Installation (rawAt nextRawAt materialAt)
end I
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionReader)
end R
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end S
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid nativeValue)
end WB
namespace SF
export OriginalKSourceFeedbackSuccessorAction.Mother.SF (Seed cfg)
end SF
namespace AP
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket nativeAfterAdmission bornAfterNative stockCfg write)
end AP
namespace Native
export ActualCofinalSourceAction (nativePacket selected receipt nativeValue sourceBorn receiver_ast receiver_input native_packet_actual)
end Native
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Frames
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (frames next)
end Frames
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input expression_eval)
end N
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (old_paid_const native_value updated_total)
end WB
namespace Native
export ActualCofinalSourceAction (old_event_in_born old_pair_event_in_born whole_paid_in_born generated_joint_in_born
 bornStock bornPairStock sourceLiftEvent sourceLiftPairEvent paid_prefix_stocks)
end Native
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (scalar pair)
end AS
namespace LowerStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.Stock (scalar)
end LowerStock
namespace SourceStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve physicalPrior)
end SourceStock
namespace Configured
export SourceGeneratedInquiryReceiptAction.Configured (lowWritten lowStock)
end Configured
namespace AN
export ActualNativeRelationTransport (paid)
end AN

private theorem source_preserve_right {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) :
 event∈(SourceStock.preserve old next).trace := by
 cases old with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem source_preserve_left {α : Type} (old next : RootedAccountedUnfolding α)
 (event : α) (present : event∈old.trace) :
 event∈(SourceStock.preserve (some old) next).trace :=
 (SourceHistoryCommon.parallel_left _ _ _).1 event present

variable {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
local instance sourceInventoryGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value W grade target) := L.groups W grade target
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (packet : AP.AdmissionPacket (W:=W) (X:=X) (s:=()))

/-- The original literal source calculation trace is paid before emission, then each source node enters the actual native born stock. -/
theorem source_literal_nodes_in_born (event)
 (present : event∈(SourceOperationPaidRelations.exposure
  (R.actualMaterial packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2)).state.2).trace) :
 event∈(Native.bornStock (sourceCofinalFactory literalCode factory)
  (sourceActionPacket literalCode factory packet)).trace := by
 have atWritten : event∈(Configured.lowWritten packet.2.1.1
  (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2)).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event present
 have atLower : event∈(LowerStock.scalar packet.2.1.1
  (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2) rfl).trace :=
  source_preserve_right _ _ _ atWritten
 have atReceiver : event∈(AS.scalar (sourceCofinalFactory literalCode factory) packet.1 packet.2.1
  (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2) rfl).trace :=
  scalar_legacy_preserved (sourceCofinalFactory literalCode factory) packet.1 packet.2.1
   (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2) rfl event
   (source_preserve_right _ _ _ atLower)
 apply SourceInventoryExecutionFeed.original_preserved
 change event∈(SourceStock.preserve (sourceNativeSelected literalCode factory packet).inventory _).trace
 rw [(Native.paid_prefix_stocks (sourceCofinalFactory literalCode factory)
  (sourceActionPacket literalCode factory packet) _ (Nat.le_refl _)).1]
 exact source_preserve_left _ _ _ atReceiver

/-- Every original scalar source node retains its complete typed lift in this new occurrence. -/
theorem source_prior_scalar_nodes_in_born
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (L.Value W packet.1) X ())))
 (actual : packet.2.1.1.inventory=some prior) (event) (present : event∈prior.trace) :
 Native.sourceLiftEvent (sourceActionPacket literalCode factory packet) event∈
 (Native.bornStock (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet)).trace :=
 Native.old_event_in_born (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet) prior actual event present

/-- Every original paired source word, including raw/odd/mean/inherited coordinates, passes the same native source lift. -/
theorem source_prior_pair_nodes_in_born
 (prior : RootedAccountedUnfolding (PresentedRelationEventAt (Expr (PairValue (L.Value W packet.1)) X ())))
 (actual : packet.2.1.1.pairInventory=some prior) (event) (present : event∈prior.trace) :
 Native.sourceLiftPairEvent (sourceActionPacket literalCode factory packet) event∈
 (Native.bornPairStock (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet)).trace :=
 Native.old_pair_event_in_born (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet) prior actual event present

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
