import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Born
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Packet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
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
local instance residualWholeGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (radius : ℝ) (source residual : F.Branches)

abbrev residualSelectedAt := residualStockSelected factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual
abbrev residualBaseAt := residualEmitterStock factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source residual

def residualWholeAt : Pay.BornWholeWrite (residualSelectedAt factory packet radius source residual) (residualBaseAt factory packet radius source residual) :=
 Pay.bornWholeWrite _ _

def residualBirthAt :=
 (ST.birthProgram (residualSelectedAt factory packet radius source residual) (AS.stockCfg (residualBaseAt factory packet radius source residual))).generate
 ((SO.root (residualSelectedAt factory packet radius source residual) (AS.stockCfg (residualBaseAt factory packet radius source residual))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (residualSelectedAt factory packet radius source residual) (AS.stockCfg (residualBaseAt factory packet radius source residual))))

theorem residual_whole_next : type_of% (ST.target_current (residualSelectedAt factory packet radius source residual)
 (AS.stockCfg (residualBaseAt factory packet radius source residual))
 ((SO.root (residualSelectedAt factory packet radius source residual) (AS.stockCfg (residualBaseAt factory packet radius source residual))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (residualSelectedAt factory packet radius source residual) (AS.stockCfg (residualBaseAt factory packet radius source residual))))) := ST.target_current _ _ _

theorem residual_whole_destination : type_of% (residualBirthAt factory packet radius source residual).target.firstDestination_heq :=
 (residualBirthAt factory packet radius source residual).target.firstDestination_heq

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWindowInverseResidualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
