import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Born
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Packet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
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
variable (source : D.SourceBranches)

abbrev paSelectedAt := paStockSelected factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source
abbrev paBaseAt := sourcePaEmitterStock factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down source

def paWholeAt : Pay.BornWholeWrite (paSelectedAt factory packet source) (paBaseAt factory packet source) :=
 Pay.bornWholeWrite _ _

def paBirthAt :=
 (ST.birthProgram (paSelectedAt factory packet source) (AS.stockCfg (paBaseAt factory packet source))).generate
 ((SO.root (paSelectedAt factory packet source) (AS.stockCfg (paBaseAt factory packet source))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (paSelectedAt factory packet source) (AS.stockCfg (paBaseAt factory packet source))))

theorem pa_whole_next : type_of% (ST.target_current (paSelectedAt factory packet source)
 (AS.stockCfg (paBaseAt factory packet source))
 ((SO.root (paSelectedAt factory packet source) (AS.stockCfg (paBaseAt factory packet source))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (paSelectedAt factory packet source) (AS.stockCfg (paBaseAt factory packet source))))) := ST.target_current _ _ _

theorem pa_whole_destination : type_of% (paBirthAt factory packet source).target.firstDestination_heq :=
 (paBirthAt factory packet source).target.firstDestination_heq

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPaWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
