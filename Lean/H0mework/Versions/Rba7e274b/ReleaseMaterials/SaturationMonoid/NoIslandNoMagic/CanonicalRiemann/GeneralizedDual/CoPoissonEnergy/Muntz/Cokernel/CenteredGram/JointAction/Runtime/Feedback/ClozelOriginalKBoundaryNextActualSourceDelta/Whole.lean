import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Packet.Actor
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace D
export OriginalKWholePaNativeRankSourceUpdate (sourceActorStockSelected)
end D
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget (birthProgram target_current target_root)
end ST
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (root visit)
end SO
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (stockCfg)
end AS
local instance actorWholeGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (producer : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
variable (H N : ℝ)

abbrev actorSelectedAt := D.sourceActorStockSelected observation nontrivial half
 (D.actualSourceRActorFactory observation nontrivial half producer)
 packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N

abbrev actorBaseAt := D.sourceEmitterActorBase observation nontrivial half
 (D.actualSourceRActorFactory observation nontrivial half producer)
 packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down H N

def actorWholeAt : Pay.BornWholeWrite
 (actorSelectedAt observation nontrivial half producer packet H N)
 (actorBaseAt observation nontrivial half producer packet H N) := Pay.bornWholeWrite _ _

def actorBirthAt :=
 (ST.birthProgram (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))).generate
 ((SO.root (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (actorSelectedAt observation nontrivial half producer packet H N)
   (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))))

theorem actor_whole_destination : type_of%
 (actorBirthAt observation nontrivial half producer packet H N).target.firstDestination_heq :=
 (actorBirthAt observation nontrivial half producer packet H N).target.firstDestination_heq

theorem actor_canonical_next : type_of%
 (ST.target_current (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))
  ((SO.root (actorSelectedAt observation nontrivial half producer packet H N)
  (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (actorSelectedAt observation nontrivial half producer packet H N)
   (AS.stockCfg (actorBaseAt observation nontrivial half producer packet H N))))) :=
 ST.target_current _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNextActualSourceDelta
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
