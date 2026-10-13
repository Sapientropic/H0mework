import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance finiteRootGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem packet_root_transport {Y Z : Unit → Type} (same : Y=Z)
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 HEq (SO.root (Transport.packetTransport same packet).2.1.1 (Transport.packetTransport same packet).2.2.1)
  (SO.root packet.2.1.1 packet.2.2.1) := by
 cases same
 exact HEq.rfl

private theorem packet_current_transport {Y Z : Unit → Type} (same : Y=Z)
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 SO.current (Transport.packetTransport same packet).2.1.1 (Transport.packetTransport same packet).2.2.1 =
 SO.current packet.2.1.1 packet.2.2.1 := by cases same; rfl

private theorem generated_root_at {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 HEq ((ST.birthProgram frame cfg).generate ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))).target.targetRoot
  (SO.root (Shared.nextBorn frame cfg) cfg) := heq_of_eq (ST.target_root frame cfg _)

private theorem generated_current_at {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 let birth := (ST.birthProgram frame cfg).generate ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))
 (⟨birth.target.TargetN,birth.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
 SO.current (Shared.nextBorn frame cfg) cfg :=
 congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent)) (ST.target_current frame cfg _)

variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (radius : ℝ) (source : Branches)

theorem finite_source_root : HEq (finiteBirthAt factory packet radius source).target.targetRoot
 (SO.root (finiteBornPacket factory packet radius source).2.1.1 (finiteBornPacket factory packet radius source).2.2.1) := by
 let native : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
  ⟨packet.1+1,⟨Receiver.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
  Receiver.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
  finiteEmitterStock factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source,⟨rfl⟩⟩
 have generated := generated_root_at (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))
 have born : (AP.bornAfterNative native).2.1.1 = Shared.nextBorn (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source)) := rfl
 have cfg : (AP.bornAfterNative native).2.2.1 = AS.stockCfg (finiteBaseAt factory packet radius source) := rfl
 have origin := packet_root_transport packet.2.2.2.down (AP.bornAfterNative native)
 rw [born,cfg] at origin
 unfold finiteBornPacket finiteNativePacket
 exact HEq.trans generated origin.symm

theorem finite_source_current :
 (⟨(finiteBirthAt factory packet radius source).target.TargetN,(finiteBirthAt factory packet radius source).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
 SO.current (finiteBornPacket factory packet radius source).2.1.1 (finiteBornPacket factory packet radius source).2.2.1 := by
 let native : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
  ⟨packet.1+1,⟨Receiver.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
  Receiver.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
  finiteEmitterStock factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source,⟨rfl⟩⟩
 have generated := generated_current_at (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))
 have origin := packet_current_transport packet.2.2.2.down (AP.bornAfterNative native)
 unfold finiteBornPacket finiteNativePacket
 exact generated.trans origin.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
