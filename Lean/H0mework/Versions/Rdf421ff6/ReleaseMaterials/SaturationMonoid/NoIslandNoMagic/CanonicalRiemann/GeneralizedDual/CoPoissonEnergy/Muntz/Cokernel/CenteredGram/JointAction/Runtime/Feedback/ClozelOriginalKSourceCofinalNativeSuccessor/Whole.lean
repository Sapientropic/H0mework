import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
namespace AN
export ActualNativeRelationTransport (paid)
end AN
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (oldPaid)
end WB
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance wholePacketGroups (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
variable (fixedFactory : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

/-- This is the existing whole born from the real source packet and native receipt. -/
def sourcePacketWhole : Pay.BornWholeWrite (Native.selected fixedFactory packet)
 (Native.nativePacket fixedFactory packet).2.2.1 := Pay.bornWholeWrite _ _

def sourcePacketRegisteredValue : PairValue (L.Value W packet.1) () :=
 (Native.sourceBorn fixedFactory packet).2.1.1.registered.input.expression.eval
 (Native.sourceBorn fixedFactory packet).2.1.1.registered.input.environment

/-- The source receipt endpoint, not a target readout, supplies the native material endpoint. -/
theorem source_packet_material_endpoint :
 (AN.paid (Native.selected fixedFactory packet)).state.1=.const (Native.nativeValue fixedFactory packet) :=
 (Native.receipt fixedFactory packet).2.1.2.down

/-- Both source fields of the real whole are consumed to decode the actual material effect. -/
theorem source_packet_registered_effect :
 sourcePacketRegisteredValue fixedFactory packet=
 (AN.paid (Native.selected fixedFactory packet)).raw.effect
  (AN.paid (Native.selected fixedFactory packet)).environment
  (AN.paid (Native.selected fixedFactory packet)).increment :=
 OriginalKMaterialPhysicalStockSourceAction.whole_registered_native_effect _ _
 (sourcePacketWhole fixedFactory packet) _ (source_packet_material_endpoint fixedFactory packet)

private theorem endpoint_actual_update
 {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
 (frame : M.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (value : Value ()) (endpoint : (AN.paid frame).state.1=.const value) :
 value+(AN.paid frame).raw.effect (AN.paid frame).environment (AN.paid frame).increment=
 (AN.paid frame).raw.eval ((AN.paid frame).environment+(AN.paid frame).increment) := by
 have source:=(AN.paid frame).state.2.sound
 rw [endpoint] at source
 simp only [Expr.eval] at source
 rw [Expr.eval_update,source]

/-- The registered residual and receipt endpoint are distinct roles in the same actual material update. -/
theorem source_packet_material_update :
 Native.nativeValue fixedFactory packet+sourcePacketRegisteredValue fixedFactory packet=
 (show PairValue (L.Value W packet.1) () from
 (AN.paid (Native.selected fixedFactory packet)).raw.eval
 ((AN.paid (Native.selected fixedFactory packet)).environment+(AN.paid (Native.selected fixedFactory packet)).increment)) := by
 rw [source_packet_registered_effect]
 exact endpoint_actual_update _ _ (source_packet_material_endpoint fixedFactory packet)

def sourcePacketWholeTotal : PairValue (L.Value W packet.1) () :=
 WB.oldPaid packet.2.1.1 packet.2.2.1+
 ((show PairValue (L.Value W packet.1) () from (AN.paid (Native.selected fixedFactory packet)).raw.eval
 ((AN.paid (Native.selected fixedFactory packet)).environment+(AN.paid (Native.selected fixedFactory packet)).increment))-
 sourcePacketRegisteredValue fixedFactory packet)

/-- The complete whole material update recovers exactly the native source writer input. -/
theorem source_packet_whole_total :
 sourcePacketWholeTotal fixedFactory packet=WB.oldPaid packet.2.1.1 packet.2.2.1+Native.nativeValue fixedFactory packet := by
 unfold sourcePacketWholeTotal
 rw [←source_packet_material_update,add_sub_cancel_right]

/-- Every real source admission has the same whole material read before any fee is projected. -/
theorem source_cofinal_whole_total
 (literalCode : Expr (PairValue W) X ()) (mother : SF.Factory W X ())
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (ordinal : Nat) :
 sourcePacketWholeTotal (Prior.sourceCofinalFactory literalCode mother)
  (cofinalSourcePacket literalCode mother initial cfg language ordinal)=
 cofinalSourceNativeTotal literalCode mother initial cfg language ordinal :=
 source_packet_whole_total _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
