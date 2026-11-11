import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace
namespace Parent
export OriginalKSourceCofinalActionWrite (actualCofinalLiteralCode actualCofinalMotherFactory actualIncomingBornPacket actual_literal_current_environment_action)
end Parent
namespace FAction
export OriginalKSourceFeedbackSuccessorAction (sourceSlotsRead sourceSlotNext source_slots_recover_raw sourceFeedbackNext source_feedback_whole_conserved)
end FAction
namespace RawAction
export OriginalKRawDualFeedbackSourceAction (plusFeedback minusFeedback source_feedback_norm)
end RawAction

local instance priceFamilyGroups {W : Unit→Type} [∀ target,AddCommGroup (W target)]
 (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n

private theorem cofinal_whole_read
 {W X : Unit→Type} [∀ target,AddCommGroup (W target)] {B : Type}
 (literalCode : Expr (PairValue W) X ()) (mother : SF.Factory W X ())
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (ordinal : Nat)
 (reader : PairValue W ()→B) (action : B→B) (name : X ())
 (sourceAction : ∀ environment : Env (PairValue W) X,
  reader (literalCode.eval environment)=action (reader (environment () name))) :
 reader (CF.collapseValue (cofinalSourcePacket literalCode mother initial cfg language ordinal).1
  (sourcePacketWholeTotal (Prior.sourceCofinalFactory literalCode mother)
   (cofinalSourcePacket literalCode mother initial cfg language ordinal)))=
 action (reader (CF.collapseValue (cofinalSourcePacket literalCode mother initial cfg language ordinal).1
  (cofinalSourceInput literalCode mother initial cfg language ordinal () name))) := by
 rw [source_cofinal_whole_total,cofinal_source_native_total_base]
 exact sourceAction _

private theorem born_literal_reader
 {W X : Unit→Type} [∀ target,AddCommGroup (W target)] {B : Type}
 (literalCode : Expr (PairValue W) X ()) (bornGrade : Nat)
 (reader : PairValue W ()→B) (action : B→B) (name : X ())
 (sourceAction : ∀ environment : Env (PairValue W) X,
  reader (literalCode.eval environment)=action (reader (environment () name)))
 (environment : Env (PairValue (L.Value W bornGrade)) X) :
 reader (CF.collapseValue bornGrade ((CF.codeAt literalCode bornGrade).eval environment))=
 action (reader (CF.collapseValue bornGrade (environment () name))) := by
 rw [CF.code_base_value]
 exact sourceAction _


open Complex BurnolPhysicalState OriginalKFullSourceRAction
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance sourceParentGroups (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1 target) :=
 L.groups (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1 target
local instance sourceParentNestedGroups (n : Nat) : ∀ target,AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) n target) :=
 L.groups (L.Value (PairValue C.Value) (OriginalKSourceFeedbackSuccessorAction.sourceInitBornPacket t factory packet).1) n

attribute [local irreducible] OriginalKSourceCofinalActionWrite.actualIncomingBornPacket

/-- The actual source-born carrier is restricted once, with the same original field reader. -/
def actualFutureReader := fun value=>
 OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet
  (CF.collapseValue ((Parent.actualIncomingBornPacket t factory packet).1+1) value)

def actualFutureFactory := sourceInstalledFactory (Parent.actualCofinalLiteralCode t factory packet)
 (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet)
def actualFutureInitial := sourceFutureInitial (Parent.actualCofinalLiteralCode t factory packet)
 (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet)
def actualFutureProgramme := sourceFutureProgramme (Parent.actualCofinalLiteralCode t factory packet)
 (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet)
def actualFutureLiteral := sourceBornLiteral (Parent.actualCofinalLiteralCode t factory packet)
 (Parent.actualIncomingBornPacket t factory packet)
def actualFutureMother := sourceBornMother (Parent.actualCofinalLiteralCode t factory packet)
 (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet)

/-- The same original action law is consumed after the genuine born-grade source restriction. -/
theorem actual_future_literal_read : type_of%
 (born_literal_reader (Parent.actualCofinalLiteralCode t factory packet)
  ((Parent.actualIncomingBornPacket t factory packet).1+1)
  (OriginalKSourceFeedbackContinuationAction.actualNativeTotalRead t factory packet)
  FAction.sourceSlotNext () (Parent.actual_literal_current_environment_action t factory packet)) :=
 born_literal_reader _ _ _ _ _ (Parent.actual_literal_current_environment_action t factory packet)

/-- Every actual runtime admission consumes the same source action on its own complete material input. -/
theorem actual_future_whole_read (ordinal : Nat) : type_of%
 (cofinal_whole_read (actualFutureLiteral t factory packet) (actualFutureMother t factory packet)
  (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl ordinal
  (actualFutureReader t factory packet) FAction.sourceSlotNext ()
  (actual_future_literal_read t factory packet)) :=
 cofinal_whole_read _ _ _ _ _ _ _ _ _ (actual_future_literal_read t factory packet)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
