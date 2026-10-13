import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Root
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn)
end S
local instance actorCurrentGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem packet_current_transport {Y Z : Unit → Type} (same : Y = Z)
 (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := Y) (s := ())) :
 SO.current (T.packetTransport same packet).2.1.1 (T.packetTransport same packet).2.2.1 =
 SO.current packet.2.1.1 packet.2.2.1 := by cases same; rfl

private theorem generated_current_at
 {Value Var : Unit → Type} [∀ target,AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value := Value) (Var := Var) (sort := ()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ())) :
 let generated := (ST.birthProgram frame cfg).generate
  ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))
 (⟨generated.target.TargetN,generated.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
 SO.current (S.nextBorn frame cfg) cfg :=
 congrArg (fun current => (⟨_,current⟩ : AnyAuthoritativeRootCurrent)) (ST.target_current frame cfg _)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
variable (H N : ℝ)

theorem actor_actual_packet_current :
 (⟨(actorBirthAt observation nontrivial half producer packet H N).target.TargetN,
   (actorBirthAt observation nontrivial half producer packet H N).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
 SO.current (sourceActorBornPacket observation nontrivial half producer packet H N).2.1.1
  (sourceActorBornPacket observation nontrivial half producer packet H N).2.2.1 := by
 let native : AP.AdmissionPacket (W := PairValue C.Value) (X := packet.2.2.1.LowVar) (s := ()) :=
  let factory := D.actualSourceRActorFactory observation nontrivial half producer
  ⟨packet.1+1,⟨AS.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   AS.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   D.sourceEmitterActorBase observation nontrivial half factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N,⟨rfl⟩⟩
 have current := generated_current_at (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))
 have origin := packet_current_transport packet.2.2.2.down (AP.bornAfterNative native)
 unfold sourceActorBornPacket sourceActorNativePacket
 exact current.trans origin.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
