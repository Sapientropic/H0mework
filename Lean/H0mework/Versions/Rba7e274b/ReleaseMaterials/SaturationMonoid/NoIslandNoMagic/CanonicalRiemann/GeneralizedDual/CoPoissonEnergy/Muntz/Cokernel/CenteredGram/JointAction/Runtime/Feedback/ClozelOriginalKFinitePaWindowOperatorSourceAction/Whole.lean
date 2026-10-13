import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Born
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFinitePaWindowOperatorSourceAction.Packet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
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
local instance finiteWholeGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (radius : ℝ) (source : Branches)

abbrev finiteSelectedAt := finiteStockSelected factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source
abbrev finiteBaseAt := finiteEmitterStock factory packet.1 packet.2.1 packet.2.2.1 packet.2.2.2.down radius source

def finiteWholeAt : Pay.BornWholeWrite (finiteSelectedAt factory packet radius source) (finiteBaseAt factory packet radius source) :=
 Pay.bornWholeWrite _ _

def finiteBirthAt :=
 (ST.birthProgram (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))).generate
 ((SO.root (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))))

theorem finite_whole_next : type_of% (ST.target_current (finiteSelectedAt factory packet radius source)
 (AS.stockCfg (finiteBaseAt factory packet radius source))
 ((SO.root (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (finiteSelectedAt factory packet radius source) (AS.stockCfg (finiteBaseAt factory packet radius source))))) := ST.target_current _ _ _

theorem finite_whole_destination : type_of% (finiteBirthAt factory packet radius source).target.firstDestination_heq :=
 (finiteBirthAt factory packet radius source).target.firstDestination_heq

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFinitePaWindowOperatorSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
