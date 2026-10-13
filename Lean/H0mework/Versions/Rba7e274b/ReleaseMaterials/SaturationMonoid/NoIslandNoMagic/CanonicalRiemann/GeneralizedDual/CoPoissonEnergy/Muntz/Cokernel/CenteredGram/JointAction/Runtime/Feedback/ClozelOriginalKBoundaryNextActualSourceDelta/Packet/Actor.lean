import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Future.Kernel
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.ActorMaterial
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace AP
export ActualCofinalSourceAction.AS (AdmissionPacket bornAfterNative)
end AP
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (receiver nextSeed)
end AS
namespace T
export ActualCofinalSourceAction (packetTransport)
end T
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace L
export OriginalKFullSourceRAction.L (Value groups)
end L
namespace SF
export OriginalKWholePaNativeRankSourceUpdate.SourceFamily (Factory)
end SF
namespace D
export OriginalKWholePaNativeRankSourceUpdate
 (actualSourceRActorFactory sourceEmitterActorBase sourceActorStockCfg sourceActorStockBorn)
end D
local instance actorPacketGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
variable (H N : ℝ)

def sourceActorNativePacket : AP.AdmissionPacket
 (W := PairValue C.Value) (X := packet.2.2.1.LowVar) (s := ()) :=
 let factory := D.actualSourceRActorFactory observation nontrivial half producer
 ⟨packet.1+1,⟨AS.receiver factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down,
 AS.nextSeed factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down⟩,
 D.sourceEmitterActorBase observation nontrivial half factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N,⟨rfl⟩⟩

def sourceActorBornPacket : AP.AdmissionPacket
 (W := PairValue C.Value) (X := C.Var) (s := ()) :=
 T.packetTransport packet.2.2.2.down
  (AP.bornAfterNative (sourceActorNativePacket observation nontrivial half producer packet H N))

theorem source_actor_born_packet :
 HEq (sourceActorBornPacket observation nontrivial half producer packet H N).2.1.1
  (D.sourceActorStockBorn observation nontrivial half
   (D.actualSourceRActorFactory observation nontrivial half producer)
   packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N) := by
 unfold sourceActorBornPacket
 generalize same : packet.2.2.2.down = language
 have transport {Y Z : Unit → Type} (equal : Y = Z)
  (original : AP.AdmissionPacket (W := PairValue C.Value) (X := Y) (s := ())) :
  HEq (T.packetTransport equal original).2.1.1 original.2.1.1 := by
  cases equal
  exact HEq.rfl
 exact transport _ _

attribute [irreducible] sourceActorNativePacket sourceActorBornPacket

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
