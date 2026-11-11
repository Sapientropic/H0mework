import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
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
variable {W X : Unit → Type} [∀ target, AddCommGroup (W target)]
local instance packetGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value W grade target) := L.groups W grade target
variable (literalCode : Expr (PairValue W) X ()) (factory : SF.Factory W X ())
variable (packet : AP.AdmissionPacket (W:=W) (X:=X) (s:=()))

/-- The source programme is installed on the original full frame and its own seed before native admission; neither is reconstructed from target values. -/
abbrev sourceActionPacket : AP.AdmissionPacket (W:=W) (X:=X) (s:=()) :=
 ⟨packet.1,packet.2.1,sourceCofinalCfg literalCode factory packet.1 packet.2.1.2,⟨rfl⟩⟩

abbrev sourceNativePacket := Native.nativePacket (sourceCofinalFactory literalCode factory)
 (sourceActionPacket literalCode factory packet)
abbrev sourceNativeSelected := Native.selected (sourceCofinalFactory literalCode factory)
 (sourceActionPacket literalCode factory packet)
abbrev sourceNativeReceipt := Native.receipt (sourceCofinalFactory literalCode factory)
 (sourceActionPacket literalCode factory packet)
abbrev sourceNativeBorn := Native.sourceBorn (sourceCofinalFactory literalCode factory)
 (sourceActionPacket literalCode factory packet)

/-- Actual source installation keeps the complete incoming frame and its scalar seed, with no value-based occurrence recognition. -/
theorem source_action_keeps_original_input :
 (sourceActionPacket literalCode factory packet).2.1=packet.2.1 := rfl

private theorem actual_receipt_raw_preserved
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.atReceipt cfg initial 0).rawRead=initial.rawRead := by
 apply Prefix.receipt_read cfg initial (fun stage => (Frames.frames initial cfg stage).rawRead)
 intro stage paid actual
 have next : Frames.frames initial cfg (stage+1)=(Frames.frames initial cfg stage).mathNext := by
  change Frames.next _ _=_
  unfold Frames.next
  rw [actual]
 exact (congrArg (fun candidate : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value:=Value) (Var:=Var) (sort:=()) => candidate.rawRead) next).trans rfl

/-- The actual native receipt endpoint is generated by this original source material's residual expression. -/
theorem source_native_receipt_value :
 (show PairValue (L.Value W packet.1) () from
  Native.nativeValue (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet))=
 (N.expression (R.actualMaterial packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2))).eval
  (N.input (R.actualMaterial packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2))).environment := by
 have paid := SourceOperationExecutionDebt.completed_value
  (sourceNativeSelected literalCode factory packet).event.state (sourceNativeReceipt literalCode factory packet).2.1
 change (show PairValue (L.Value W packet.1) () from
  Native.nativeValue (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet))=
  (sourceNativeSelected literalCode factory packet).rawRead.expression.eval
   (sourceNativeSelected literalCode factory packet).rawRead.environment at paid
 have unchanged : (sourceNativeSelected literalCode factory packet).rawRead=
  (sourceNativePacket literalCode factory packet).2.1.1.rawRead :=
  actual_receipt_raw_preserved (AP.stockCfg (sourceNativePacket literalCode factory packet).2.2.1)
   (sourceNativePacket literalCode factory packet).2.1.1
 exact paid.trans (congrArg (fun raw => raw.expression.eval raw.environment) unchanged)

/-- The real native endpoint and old paid source produce the source-code update consumed by the existing AS writer. -/
theorem source_native_actual_total :
 WB.oldPaid packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2)+
  (show PairValue (L.Value W packet.1) () from
  Native.nativeValue (sourceCofinalFactory literalCode factory) (sourceActionPacket literalCode factory packet))=
 (CF.codeAt literalCode packet.1).eval
  (N.input (R.actualMaterial packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2))).environment := by
 have native := (source_native_receipt_value literalCode factory packet).trans
  (WB.native_value packet.2.1.1 (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2)
   (AP.write (sourceCofinalFactory literalCode factory) packet.1 packet.2.1
    (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2) rfl)).symm
 exact (congrArg (fun value => WB.oldPaid packet.2.1.1
  (sourceCofinalCfg literalCode factory packet.1 packet.2.1.2)+value) native).trans
   (source_cofinal_actual_updated_total literalCode factory packet.1 packet.2.1.2 packet.2.1.1 _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
