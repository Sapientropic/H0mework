import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Packet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Trace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
local instance nextGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

local instance actualNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target

private def sourceExprPort (grade : Nat) (target : Unit) :=
 @Expr Unit (L.Value (PairValue C.Value) grade) C.Var (L.groups (PairValue C.Value) grade) target

/-- This cast follows the original whole packet's actual grade proof, including its group family. It identifies no source quantity or mathematical depth. -/
def actualNestedSourceBinding (target : Unit) (_name : C.Var target) :
 Expr (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) C.Var target := by
 cases target
 exact cast (congrArg (fun grade => sourceExprPort grade ()) (source_init_born_grade t factory packet)).symm
  (show sourceExprPort (packet.1+1) () from CF.codeAt sourceNextSlotsCode packet.1)

/-- Install source-tail action in the existing same-born continuation's dependent decoder. -/
def actualSourceNextFactory :=
 installedTraceFactory (actualNestedSourceBinding t factory packet) () (sourceActualContinuation t factory packet)

def actualSourceNextConfiguration := Mother.SF.cfg (actualSourceNextFactory t factory packet) 0
 (sourceInitBornPacket t factory packet).2.1.2

/-- The next datum executes the source action on the same supplied environment; calculation-reader installation alone is not used as a write claim. -/
theorem actual_source_next_decoder
 {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current (sourceInitBornPacket t factory packet).2.1.1.registered}
 (supplied : SourceOperationInquiry.Context.Installation.Occurrence (sourceInitBornPacket t factory packet).2.1.1 (current:=current))
 (queryPaid) :
 (((actualSourceNextConfiguration t factory packet).datum (sourceInitBornPacket t factory packet).2.1.1).nextEnvironmentReadAt.get (by rfl)) supplied queryPaid=
 SlotSource.physicalNext (actualNestedSourceBinding t factory packet) (sourceInitBornPacket t factory packet).2.1.1 supplied := rfl

/-- Its canonical born environment comes from this exact actual source decoder. -/
theorem actual_source_next_born_environment (bornCurrent)
 (occurrence : (SlotSource.Shared.nextBorn (sourceInitBornPacket t factory packet).2.1.1
  (actualSourceNextConfiguration t factory packet)).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 (SlotSource.Shared.nextBorn (sourceInitBornPacket t factory packet).2.1.1
  (actualSourceNextConfiguration t factory packet)).environment occurrence=
 SlotSource.physicalNext (actualNestedSourceBinding t factory packet) (sourceInitBornPacket t factory packet).2.1.1
  (SlotSource.Shared.actualOccurrence (sourceInitBornPacket t factory packet).2.1.1) :=
 source_decoder_born_environment (actualNestedSourceBinding t factory packet) (sourceActualContinuation t factory packet) 0
  (sourceInitBornPacket t factory packet).2.1.2 (sourceInitBornPacket t factory packet).2.1.1 _ occurrence
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
