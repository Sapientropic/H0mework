import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Next
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Whole
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace Pay
export SourceFamilyActualCurrentMaterialRootedEffect (BornWholeWrite bornWholeWrite)
end Pay
namespace ST
export OriginalKMaterialPhysicalStockSourceAction.ST (birthProgram target_root target_current)
end ST
namespace SO
export OriginalKMaterialPhysicalStockSourceAction.SO (root current visit)
end SO
local instance wholeGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
local instance sourceWholeGroups (relative : Nat) (target : Unit) : AddCommGroup
 (L.Value (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target) :=
 L.groups (L.Value (PairValue C.Value) (sourceInitBornPacket t factory packet).1) relative target

abbrev sourceNextFrame := (sourceInitBornPacket t factory packet).2.1.1
abbrev sourceNextBase := actualSourceNextConfiguration t factory packet

def actualSourceNextWhole : Pay.BornWholeWrite (sourceNextFrame t factory packet) (sourceNextBase t factory packet) :=
 Pay.bornWholeWrite _ _

def actualSourceNextBirth :=
 (ST.birthProgram (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))).generate
 ((SO.root (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (SO.visit (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))))

def actualNextSourceFrame := SlotSource.Shared.nextBorn (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))

/-- This is the actual whole birth's source environment, using its installed source decoder after complete inventory preservation. -/
theorem actual_whole_source_environment (bornCurrent)
 (occurrence : (actualNextSourceFrame t factory packet).old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt bornCurrent) :
 (actualNextSourceFrame t factory packet).environment occurrence=
 SlotSource.physicalNext (actualNestedSourceBinding t factory packet) (sourceNextFrame t factory packet)
  (SlotSource.Shared.actualOccurrence (sourceNextFrame t factory packet)) := rfl

theorem actual_source_whole_root : type_of%
 (ST.target_root (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))
  ((SO.root (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))))) := ST.target_root _ _ _

theorem actual_source_whole_current : type_of%
 (ST.target_current (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))
  ((SO.root (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (sourceNextFrame t factory packet) (AS.stockCfg (sourceNextBase t factory packet))))) := ST.target_current _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
