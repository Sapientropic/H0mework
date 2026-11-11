import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalActionWrite.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackContinuationAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Parent
export OriginalKSourceFeedbackContinuationAction
 (actualCurrentSourceFactory actualCurrentSourceData actualCurrentSourceBase continuationSourceStockEmitter continuationSourceBorn)
end Parent
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (AdmissionPacket bornAfterNative receiver nextSeed localNativeReceipt)
end AS
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (collapseValue code_base_value)
end CF
local instance sourceWrittenGroups {W : Unit → Type} [∀ target,AddCommGroup (W target)]
 (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
private theorem actual_source_written_value
 {W X : Unit → Type} [∀ target,AddCommGroup (W target)]
 (literalCode : Expr (PairValue W) X ()) (sourceFactory : SF.Factory W X ())
 (incoming : AP.AdmissionPacket (W:=W) (X:=X) (s:=())) (name : X ()) :
 CF.collapseValue incoming.1
  (show PairValue (L.Value W incoming.1) () from
   (sourceNativeBorn literalCode sourceFactory incoming).2.1.1.activeEnvironment () name)=
 literalCode.eval (fun target variableName => CF.collapseValue incoming.1
  ((N.input (R.actualMaterial incoming.2.1.1
   (sourceCofinalCfg literalCode sourceFactory incoming.1 incoming.2.1.2))).environment target variableName)) := by
 rw [source_native_born_source_write]
 unfold sourceNativeActualWrite AP.write
 simp only [dite_true]
 exact CF.code_base_value literalCode incoming.1 _

private theorem source_received_read
 {W X : Unit → Type} [∀ target,AddCommGroup (W target)] {B : Type}
 (literalCode : Expr (PairValue W) X ()) (sourceFactory : SF.Factory W X ())
 (incoming : AP.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (reader : PairValue W () → B) (action : B → B) (name : X ())
 (sourceAction : ∀ environment : Env (PairValue W) X,
  reader (literalCode.eval environment)=action (reader (environment () name))) :
 reader (CF.collapseValue incoming.1
  (show PairValue (L.Value W incoming.1) () from
   (sourceNativeBorn literalCode sourceFactory incoming).2.1.1.activeEnvironment () name))=
 action (reader (CF.collapseValue incoming.1
  ((N.input (R.actualMaterial incoming.2.1.1
   (sourceCofinalCfg literalCode sourceFactory incoming.1 incoming.2.1.2))).environment () name))) :=
 (congrArg reader (actual_source_written_value literalCode sourceFactory incoming name)).trans
  (sourceAction _)

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance receivedCofinalBaseGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1 target
local instance receivedCofinalNestedGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) relative target

attribute [local irreducible] actualIncomingBornPacket

/-- The input belongs to the full current material update, including its registered native before/effect environment. -/
def actualCofinalInputPair :
 PairValue (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) () :=
 CF.collapseValue (actualIncomingBornPacket t factory packet).1
  ((N.input (R.actualMaterial (actualIncomingBornPacket t factory packet).2.1.1
   (sourceCofinalCfg (actualCofinalLiteralCode t factory packet) (actualCofinalMotherFactory t factory packet)
    (actualIncomingBornPacket t factory packet).1 (actualIncomingBornPacket t factory packet).2.1.2))).environment () ())

/-- The written source pair is read from the actual born environment and collapsed only through its generated graded carrier. -/
def actualCofinalWrittenPair :
 PairValue (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) () :=
 CF.collapseValue (actualIncomingBornPacket t factory packet).1
  (show PairValue (L.Value
   (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1)
   (actualIncomingBornPacket t factory packet).1) () from
   (actualCofinalBornPacket t factory packet).2.1.1.activeEnvironment () ())

def actualCofinalInputValue := OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet
 (actualCofinalInputPair t factory packet)
def actualCofinalReceivedValue := OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet
 (actualCofinalWrittenPair t factory packet)

def actualCofinalInputRaw := OriginalKSourceFeedbackSuccessorAction.sourceSlotsRead (actualCofinalInputValue t factory packet)
def actualCofinalReceivedRaw := OriginalKSourceFeedbackSuccessorAction.sourceSlotsRead (actualCofinalReceivedValue t factory packet)

/-- The actual receipt/write proof is instantiated at its generated dependent type. -/
theorem actual_cofinal_received_source_value : type_of%
 (source_received_read (actualCofinalLiteralCode t factory packet)
  (actualCofinalMotherFactory t factory packet) (actualIncomingBornPacket t factory packet)
  (OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet)
  OriginalKSourceFeedbackSuccessorAction.sourceSlotNext ()
  (actual_literal_current_environment_action t factory packet)) :=
 source_received_read (actualCofinalLiteralCode t factory packet)
  (actualCofinalMotherFactory t factory packet) (actualIncomingBornPacket t factory packet)
  (OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet)
  OriginalKSourceFeedbackSuccessorAction.sourceSlotNext ()
  (actual_literal_current_environment_action t factory packet)

/-- The actual whole source action feeds all four raw roles, before any observer fee is read. -/
theorem actual_cofinal_received_raw_source :
 actualCofinalReceivedRaw t factory packet=OriginalKSourceFeedbackSuccessorAction.sourceFeedbackNext
  (actualCofinalInputRaw t factory packet) := by
 unfold actualCofinalReceivedRaw actualCofinalReceivedValue actualCofinalWrittenPair
 unfold actualCofinalBornPacket
 rw [actual_cofinal_received_source_value]
 unfold OriginalKSourceFeedbackSuccessorAction.sourceSlotNext
 exact OriginalKSourceFeedbackSuccessorAction.source_slots_recover_raw _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalActionWrite
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
