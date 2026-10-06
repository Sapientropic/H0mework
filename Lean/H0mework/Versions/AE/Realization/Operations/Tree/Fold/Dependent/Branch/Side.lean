import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Evaluator.Source
import H0mework.Versions.AE.Realization.Perfectification.Occurrence.Temporal.History.Common.Action.Source
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
abbrev visit := SourceTemporalMaterial.decode root.toAuthoritativeRoot.toLedgerRoot code
abbrev step := recognition.generateStepAt (visit root code)
abbrev SourceExposureTree := RootedAccountedUnfolding
  (Σ pairing : PairingAt recognition.material.parent (step root recognition code).sourceOccurrence,
    RawExposureAt (H:=H) recognition.material.parent (step root recognition code).sourceOccurrence pairing)
abbrev TargetExposureTree (successor : StepLedgerSuccessorAt (step root recognition code)) := RootedAccountedUnfolding
  (Σ pairing : PairingAt recognition.material.parent successor.targetOccurrence,
    RawExposureAt (H:=H) recognition.material.parent successor.targetOccurrence pairing)
def sourceExposureTree : SourceExposureTree root recognition code :=
  (stepSourcePairingOccurrence (step root recognition code)).map
    (fun pairing => ⟨pairing,stepSourceExposureAt (step root recognition code) pairing⟩)
def targetExposureTree (successor : StepLedgerSuccessorAt (step root recognition code)) : TargetExposureTree root recognition code successor :=
  (stepTargetPairingOccurrence (step root recognition code) successor).map
    (fun pairing => ⟨pairing,stepTargetExposureAt (step root recognition code) successor pairing⟩)
def DataAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) : Type u :=
  match selected with
  | none => SourceTemporalMaterial.Action.Receipt root
  | some successor => SourceHistoryCommon.Root.Raw root (visit root code) recognition successor ×
      SourceHistoryCommon.Root.Evaluator.Result root (visit root code) recognition successor ×
      SourceHistoryCommon.Root.Action.Plan root (visit root code) recognition successor ×
      SourceExposureTree root recognition code × TargetExposureTree root recognition code successor

def generateAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) : DataAt root recognition code selected :=
  match selected with
  | none => SourceTemporalMaterial.Action.receipt root code
  | some successor =>
      (SourceHistoryCommon.Root.combine root (visit root code) recognition successor
        (SourceHistoryCommon.Root.sourceRaw root (visit root code) recognition)
        (SourceHistoryCommon.Root.targetRaw root (visit root code) recognition successor),
      SourceHistoryCommon.Root.Evaluator.combine root (visit root code) recognition successor
        (SourceHistoryCommon.Root.Evaluator.source root (visit root code) recognition)
        (SourceHistoryCommon.Root.Evaluator.target root (visit root code) recognition successor),
      SourceHistoryCommon.Root.Action.combine root (visit root code) recognition successor
        (SourceHistoryCommon.Root.Action.sourceExposure root (visit root code) recognition)
        (SourceHistoryCommon.Root.Action.targetExposure root (visit root code) recognition successor),
        sourceExposureTree root recognition code,targetExposureTree root recognition code successor)
abbrev Data := DataAt root recognition code (stepSuccessor? (step root recognition code))
abbrev generate := generateAt root recognition code (stepSuccessor? (step root recognition code))
abbrev Packet := Σ code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot, Data root recognition code
def packet : Packet root recognition := ⟨code,generate root recognition code⟩
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
