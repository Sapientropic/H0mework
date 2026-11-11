import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Received
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance wholeGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade
variable (mother : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

/-- The source birth's actual whole decodes its material, registered residual and native endpoint before recovering this original source pair. -/
def sourceDifferentialWhole := Prior.sourcePacketWhole (sourceDifferentialFactory mother) (sourceDifferentialPacket mother packet)

def sourceDifferentialWholeTotal : PairValue (L.Value W packet.1) () := Prior.sourcePacketWholeTotal (sourceDifferentialFactory mother) (sourceDifferentialPacket mother packet)

def sourceRecoveredDifferential : PairValue (L.Value W packet.1) () :=
 sourceDifferentialWholeTotal mother packet-sourceDifferentialInheritedEffect mother packet

/-- Whole source_environment/source_expression and actual Trace/endpoint recover exactly the source pair after retaining its complete inherited effect. -/
theorem source_recovered_differential_material :
 sourceRecoveredDifferential mother packet=
 (sourceDifferentialMaterial mother packet).raw.eval (sourceDifferentialMaterial mother packet).environment := by
 unfold sourceRecoveredDifferential sourceDifferentialWholeTotal
 rw [Prior.source_packet_whole_total]
 change sourceDifferentialNativeTotal mother packet-sourceDifferentialInheritedEffect mother packet=_
 exact (congrArg (fun total=>total-sourceDifferentialInheritedEffect mother packet)
  (source_differential_native_two_fees mother packet)).trans (add_sub_cancel_right _ _)

/-- Every recovered foot is read from the same authoritative supplied material projection as the source constructor. -/
theorem source_recovered_differential_actual_change :
 sourceRecoveredDifferential mother packet=
 ((I.rawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).expression.eval
   (I.rawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).environment,
  (I.nextRawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).expression.eval
   (I.nextRawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).environment-
   (I.rawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).expression.eval
    (I.rawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)).environment) :=
 (source_recovered_differential_material mother packet).trans
 (source_raw_differential_actual_change
  (I.rawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1))
  (I.nextRawAt (A.epoch packet.2.1.1) (S.actualOccurrence packet.2.1.1)))

/-- The complete native source total includes both the mother differential and the actual inherited environment price. -/
theorem source_whole_differential_partition :
 sourceDifferentialWholeTotal mother packet=
 sourceRecoveredDifferential mother packet+sourceDifferentialInheritedEffect mother packet := by
 unfold sourceRecoveredDifferential
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
