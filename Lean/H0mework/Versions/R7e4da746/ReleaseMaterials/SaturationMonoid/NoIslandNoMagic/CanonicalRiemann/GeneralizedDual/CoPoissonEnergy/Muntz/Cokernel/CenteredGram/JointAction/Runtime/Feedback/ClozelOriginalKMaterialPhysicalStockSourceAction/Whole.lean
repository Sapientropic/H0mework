import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Transition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Packet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
namespace ST
export OriginalKBoundaryNextActualSourceDelta.ST (birthProgram target_root target_current)
end ST
namespace SO
export OriginalKBoundaryNextActualSourceDelta.SO (root current visit)
end SO
local instance paWholeGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (N : ℕ)

abbrev physicalSelectedAt := physicalStockSelected factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N
abbrev physicalBaseAt := physicalStockEmitter factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down N

def physicalWholeAt : Pay.BornWholeWrite (physicalSelectedAt factory packet N) (physicalBaseAt factory packet N) :=
 Pay.bornWholeWrite _ _

def physicalBirthAt :=
 (ST.birthProgram (physicalSelectedAt factory packet N) (AS.stockCfg (physicalBaseAt factory packet N))).generate
 ((SO.root (physicalSelectedAt factory packet N) (AS.stockCfg (physicalBaseAt factory packet N))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (physicalSelectedAt factory packet N) (AS.stockCfg (physicalBaseAt factory packet N))))

theorem physical_whole_next : type_of% (ST.target_current (physicalSelectedAt factory packet N)
 (AS.stockCfg (physicalBaseAt factory packet N))
 ((SO.root (physicalSelectedAt factory packet N) (AS.stockCfg (physicalBaseAt factory packet N))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (physicalSelectedAt factory packet N) (AS.stockCfg (physicalBaseAt factory packet N))))) := ST.target_current _ _ _

theorem physical_whole_destination : type_of% (physicalBirthAt factory packet N).target.firstDestination_heq :=
 (physicalBirthAt factory packet N).target.firstDestination_heq

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
