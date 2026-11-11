import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Packet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
namespace ST
export OriginalKBoundaryNextActualSourceDelta.ST (birthProgram target_root target_current)
end ST
namespace SO
export OriginalKBoundaryNextActualSourceDelta.SO (root current visit)
end SO
local instance wholeSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))

def sourceWholeAt : Pay.BornWholeWrite
 (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
 (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet) := Pay.bornWholeWrite _ _

def sourceBirthAt :=
 (ST.birthProgram (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
  (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet))).generate
 ((SO.root (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
   (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
   (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet))))

theorem source_whole_destination : type_of% (sourceBirthAt observation nontrivial half depth ordinal h H N producer packet).target.firstDestination_heq :=
 (sourceBirthAt observation nontrivial half depth ordinal h H N producer packet).target.firstDestination_heq

private theorem packet_root_transport {Y Z : Unit → Type} (same : Y=Z)
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 HEq (SO.root (Transport.packetTransport same packet).2.1.1 (Transport.packetTransport same packet).2.2.1)
  (SO.root packet.2.1.1 packet.2.2.1) := by cases same; exact HEq.rfl

private theorem packet_current_transport {Y Z : Unit → Type} (same : Y=Z)
 (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=Y) (s:=())) :
 SO.current (Transport.packetTransport same packet).2.1.1 (Transport.packetTransport same packet).2.2.1 =
 SO.current packet.2.1.1 packet.2.2.1 := by cases same; rfl

private theorem generated_root_at {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 HEq ((ST.birthProgram frame cfg).generate ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit frame cfg))).target.targetRoot (SO.root (Shared.nextBorn frame cfg) cfg) := heq_of_eq (ST.target_root frame cfg _)

private theorem generated_current_at {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=())) :
 let birth := (ST.birthProgram frame cfg).generate ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))
 (⟨birth.target.TargetN,birth.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) = SO.current (Shared.nextBorn frame cfg) cfg :=
 congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent)) (ST.target_current frame cfg _)

theorem source_born_root : HEq (sourceBirthAt observation nontrivial half depth ordinal h H N producer packet).target.targetRoot
 (SO.root (sourceBornPacket observation nontrivial half depth ordinal h H N producer packet).2.1.1
  (sourceBornPacket observation nontrivial half depth ordinal h H N producer packet).2.2.1) := by
 let native : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
  ⟨packet.1+1,⟨AS.receiver (fourFaceFactory producer)
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   AS.nextSeed (fourFaceFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   sourceBaseAt observation nontrivial half depth ordinal h H N producer packet,⟨rfl⟩⟩
 have generated := generated_root_at (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
  (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet))
 have born : (AP.bornAfterNative native).2.1.1 = Shared.nextBorn
  (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
  (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet)) := rfl
 have cfg : (AP.bornAfterNative native).2.2.1 = AS.stockCfg
  (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet) := rfl
 have origin := packet_root_transport packet.2.2.2.down (AP.bornAfterNative native)
 rw [born,cfg] at origin
 unfold sourceBornPacket sourceNativePacket
 exact HEq.trans generated origin.symm

theorem source_born_current :
 (⟨(sourceBirthAt observation nontrivial half depth ordinal h H N producer packet).target.TargetN,
   (sourceBirthAt observation nontrivial half depth ordinal h H N producer packet).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
 SO.current (sourceBornPacket observation nontrivial half depth ordinal h H N producer packet).2.1.1
  (sourceBornPacket observation nontrivial half depth ordinal h H N producer packet).2.2.1 := by
 let native : AP.AdmissionPacket (W:=PairValue C.Value) (X:=packet.2.2.1.LowVar) (s:=()) :=
  ⟨packet.1+1,⟨AS.receiver (fourFaceFactory producer)
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   AS.nextSeed (fourFaceFactory producer) packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   sourceBaseAt observation nontrivial half depth ordinal h H N producer packet,⟨rfl⟩⟩
 have generated := generated_current_at (sourceSelectedAt observation nontrivial half depth ordinal h H N producer packet)
  (AS.stockCfg (sourceBaseAt observation nontrivial half depth ordinal h H N producer packet))
 have origin := packet_current_transport packet.2.2.2.down (AP.bornAfterNative native)
 unfold sourceBornPacket sourceNativePacket
 exact generated.trans origin.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
