import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (root current)
end SO
local instance actorRootGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

private theorem source_packet_root_transport {Y Z : Unit → Type} (same : Y = Z)
 (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := Y) (s := ())) :
 HEq (SO.root (T.packetTransport same packet).2.1.1 (T.packetTransport same packet).2.2.1)
  (SO.root packet.2.1.1 packet.2.2.1) := by
 cases same
 exact HEq.rfl


private theorem born_target_root_at
 {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
 (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := Value) (Var := Var) (sort := ()))
 (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := Value) (PhysicalVar := Var) (sort := ())) :
 HEq ((ST.birthProgram frame cfg).generate
  ((SO.root frame cfg).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (SO.visit frame cfg))).target.targetRoot
 (SO.root (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn frame cfg) cfg) :=
 heq_of_eq (ST.target_root frame cfg _)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
variable (H N : ℝ)

theorem actor_source_root :
 HEq (actorBirthAt observation nontrivial half producer packet H N).target.targetRoot
 (SO.root (sourceActorBornPacket observation nontrivial half producer packet H N).2.1.1
  (sourceActorBornPacket observation nontrivial half producer packet H N).2.2.1) := by
 let native : AP.AdmissionPacket (W := PairValue C.Value) (X := packet.2.2.1.LowVar) (s := ()) :=
  let factory := D.actualSourceRActorFactory observation nontrivial half producer
  ⟨packet.1+1,⟨AS.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
   AS.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
   D.sourceEmitterActorBase observation nontrivial half factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N,⟨rfl⟩⟩
 have generated := born_target_root_at
  (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))
 have nativeBorn :
  (AP.bornAfterNative native).2.1.1 =
  SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.nextBorn
   (actorSelectedAt observation nontrivial half producer packet H N)
   (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N)) := rfl
 have nativeCfg : (AP.bornAfterNative native).2.2.1 =
  AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N) := rfl
 have origin := source_packet_root_transport packet.2.2.2.down (AP.bornAfterNative native)
 rw [nativeBorn,nativeCfg] at origin
 unfold sourceActorBornPacket sourceActorNativePacket
 exact HEq.trans generated origin.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
