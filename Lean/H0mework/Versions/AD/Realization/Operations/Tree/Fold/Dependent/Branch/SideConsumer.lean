import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
abbrev actualData := generateAt root recognition code (some successor)
abbrev commonRaw := (actualData root recognition code successor).1
abbrev commonRead := CofinalHistorySettlement.RootGeneratedCofinalHistoryAt.generate
  (rootOccurrence:=RootedAccountedUnfolding.zero (commonRaw root recognition code successor).receipt.1)
  (seedOccurrence:=(commonRaw root recognition code successor).seed)
  (continuationOccurrence:=(commonRaw root recognition code successor).continuation)
abbrev evaluationTree := (actualData root recognition code successor).2.1
abbrev evaluationFace := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.generate
  (history:=commonRead root recognition code successor) (evaluatorOccurrence:=evaluationTree root recognition code successor)
abbrev evaluationDisposition := CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt.settleWithResidual
  (evaluationFace root recognition code successor)
abbrev actionPlan := (actualData root recognition code successor).2.2.1
abbrev sourceTree := (actualData root recognition code successor).2.2.2.1
abbrev targetTree := (actualData root recognition code successor).2.2.2.2

abbrev SourceDatum := Σ pairing : PairingAt recognition.material.parent (step root recognition code).sourceOccurrence,
  RawExposureAt (H:=H) recognition.material.parent (step root recognition code).sourceOccurrence pairing
abbrev TargetDatum := Σ pairing : PairingAt recognition.material.parent successor.targetOccurrence,
  RawExposureAt (H:=H) recognition.material.parent successor.targetOccurrence pairing

def sourceState (datum : SourceDatum root recognition code) :
    Σ original : SourceDatum root recognition code,
      SourceGeneratedIntegralEquivariantPerfectRealization.GeneratedJointState original.1 original.2.measurement original.2.jointAction :=
  ⟨datum,SourceGeneratedIntegralEquivariantPerfectRealization.generate datum.1 datum.2.measurement datum.2.jointAction⟩
def targetState (datum : TargetDatum root recognition code successor) :
    Σ original : TargetDatum root recognition code successor,
      SourceGeneratedIntegralEquivariantPerfectRealization.GeneratedJointState original.1 original.2.measurement original.2.jointAction :=
  ⟨datum,SourceGeneratedIntegralEquivariantPerfectRealization.generate datum.1 datum.2.measurement datum.2.jointAction⟩
def sourceStateTree := (sourceTree root recognition code successor).map (sourceState root recognition code)
def targetStateTree := (targetTree root recognition code successor).map (targetState root recognition code successor)

theorem common_read_generated : HEq (commonRead root recognition code successor)
    (SourceHistoryCommon.Root.common root (visit root code) recognition successor) := by
  rfl

theorem evaluation_read_generated : evaluationTree root recognition code successor =
    SourceHistoryCommon.Root.Evaluator.combine root (visit root code) recognition successor
      (SourceHistoryCommon.Root.Evaluator.source root (visit root code) recognition)
      (SourceHistoryCommon.Root.Evaluator.target root (visit root code) recognition successor) := rfl

theorem action_plan_generated : actionPlan root recognition code successor =
    SourceHistoryCommon.Root.Action.actualPlan root (visit root code) recognition successor := rfl

theorem source_exposure_inventory : (sourceTree root recognition code successor).map Sigma.fst =
    stepSourcePairingOccurrence (step root recognition code) := by
  change ((stepSourcePairingOccurrence (step root recognition code)).map _).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem target_exposure_inventory : (targetTree root recognition code successor).map Sigma.fst =
    stepTargetPairingOccurrence (step root recognition code) successor := by
  change ((stepTargetPairingOccurrence (step root recognition code) successor).map _).map Sigma.fst = _
  rw [RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _
theorem source_state_inventory : (sourceStateTree root recognition code successor).map Sigma.fst = sourceTree root recognition code successor := by
  rw [sourceStateTree,RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _

theorem target_state_inventory : (targetStateTree root recognition code successor).map Sigma.fst = targetTree root recognition code successor := by
  rw [targetStateTree,RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id _
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
