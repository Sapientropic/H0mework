import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Trace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackSuccessorAction
 (sourceInitBornPacket actualNextSourceFrame sourceNextFrame sourceActualContinuation actualNestedSourceBinding
  sourceNextBase source_init_born_grade sourceActualCode sourceActualEnvironment sourceFeedbackNext sourceSlotsRead sourceRawSlots)
end Parent
namespace CurrentStock
export OriginalKBoundaryNativeSourceAction.Future (continuationFactory fromSourceSeed)
end CurrentStock
local instance receiptGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
namespace Complete
export OriginalKSourceFeedbackSuccessorAction.Complete (receipt atReceipt)
end Complete
namespace Receiver
export OriginalKSourceFeedbackSuccessorAction.Receiver (receiver)
end Receiver
namespace Shared
export OriginalKSourceFeedbackSuccessorAction.Shared (nextBorn)
end Shared
namespace Native
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (nativeEventValue)
end Native
namespace Environment
export OriginalKSourceFeedbackSuccessorAction.Environment (At active)
end Environment

private theorem actual_receipt_value {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=())) :
 Native.nativeEventValue (Complete.atReceipt cfg initial 0).event=(Complete.receipt cfg initial 0).2.1.1 := by
 have settled := (Complete.receipt cfg initial 0).2.2.2
 change RootGeneratedDebtActivationJointSource.mathAction (Complete.atReceipt cfg initial 0).event=Sum.inl (Complete.receipt cfg initial 0).2.1 at settled
 unfold Native.nativeEventValue
 rw [settled]

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance receiptBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1 target
local instance receiptNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) relative target

def continuationSourceReceipt := Complete.receipt (AS.stockCfg (continuationSourceStockEmitter t factory packet))
 (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
  (actualCurrentSourceBase t factory packet) rfl) 0

def continuationSourceSelected := Complete.atReceipt (AS.stockCfg (continuationSourceStockEmitter t factory packet))
 (Receiver.receiver (actualCurrentSourceFactory t factory packet) 0 (actualCurrentSourceData t factory packet)
  (actualCurrentSourceBase t factory packet) rfl) 0

def continuationSourceBorn := Shared.nextBorn (continuationSourceSelected t factory packet)
 (AS.stockCfg (continuationSourceStockEmitter t factory packet))

/-- This is the complete actual native source total, including its own inherited effect; no equality to the previous raw state is inferred. -/
def continuationSourceUpdatedTotal : PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () :=
 WB.oldPaid (actualCurrentSourceData t factory packet).1 (actualCurrentSourceBase t factory packet)+
 (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
  (continuationSourceReceipt t factory packet).2.1.1)

/-- The genuine receipt's settlement branch supplies the source action total; the existing born decoder then generates its new environment. -/
theorem continuation_actual_born_environment : Environment.At (continuationSourceBorn t factory packet)
 (continuationSourceWrite t factory packet (continuationSourceUpdatedTotal t factory packet)) := by
 intro current occurrence
 change continuationSourceWrite t factory packet
  (WB.oldPaid (actualCurrentSourceData t factory packet).1 (actualCurrentSourceBase t factory packet)+
   (show PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) () from
    Native.nativeEventValue (continuationSourceSelected t factory packet).event))=_
 exact congrArg (fun (sourceValue : PairValue (L.Value (L.Value (PairValue C.Value) (Parent.sourceInitBornPacket t factory packet).1) 0) ()) => continuationSourceWrite t factory packet
  (WB.oldPaid (actualCurrentSourceData t factory packet).1 (actualCurrentSourceBase t factory packet)+sourceValue))
  (actual_receipt_value _ _)
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackContinuationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
