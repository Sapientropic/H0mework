import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect CofinalHistoryTransition
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
def MapsAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) : Type (u+2) :=
  match selected with
  | none => ULift.{u+2} (SourceTemporalMaterial.Action.Receipt root)
  | some successor => ULift.{u+2}
      (((StepSourceHistory (step root recognition code)).CompletionCarrier →ₗ[ℤ] (commonRead root recognition code successor).CompletionCarrier) ×
      ((StepTargetHistory (step root recognition code) successor).CompletionCarrier →ₗ[ℤ] (commonRead root recognition code successor).CompletionCarrier))
def mapsAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) : MapsAt root recognition code selected :=
  match selected with
  | none => ⟨SourceTemporalMaterial.Action.receipt root code⟩
  | some successor => ⟨GeneratedTransition.completionMap _ _ (left root recognition code successor),
      GeneratedTransition.completionMap _ _ (right root recognition code successor)⟩
def packetMaps (packet : Packet root recognition) := mapsAt root recognition packet.1 (stepSuccessor? (step root recognition packet.1))
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
