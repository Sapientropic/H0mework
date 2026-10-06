import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Branch.Words
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Side
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (code : SourceTemporalMaterial.Code root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (step root recognition code))
variable (data : DataAt root recognition code (some successor))
def InverseAt (selected : ResidualDispositionOutcome (evaluationOf root recognition code successor data)) : Type u :=
  match selected with
  | .faithful _ _ _ => (historyOf root recognition code successor data).CompletionCarrier ≃+
      SourceHistoryCommon.Root.Evaluator.Value root (visit root code) recognition successor
  | .unsound _ _ => GeneratedRelationResidualCoordinateAt (evaluationOf root recognition code successor data)
  | .kernelResidual sound _ _ => GeneratedKernelResidualCoordinateAt (evaluationOf root recognition code successor data) sound
  | .coverageResidual sound _ _ => GeneratedCoverageResidualCoordinateAt (evaluationOf root recognition code successor data) sound

def inverse (selected : ResidualDispositionOutcome (evaluationOf root recognition code successor data)) :
    InverseAt root recognition code successor data selected := by
  cases selected with
  | faithful sound coverage proof => exact proof.canonicalQuotientAddEquiv
  | unsound falseProof coordinate => exact coordinate
  | kernelResidual sound falseProof coordinate => exact coordinate
  | coverageResidual sound falseProof coordinate => exact coordinate
abbrev generatedInverse := inverse root recognition code successor data (dispositionOf root recognition code successor data)

def FullInverseAt (selected : Option (StepLedgerSuccessorAt (step root recognition code)))
    (data : DataAt root recognition code selected) : Type (u+2) :=
  match selected with
  | none => ULift.{u+2} (SourceTemporalMaterial.Action.Receipt root)
  | some successor => ULift.{u+2} (InverseAt root recognition code successor data (dispositionOf root recognition code successor data))

def fullInverse (selected : Option (StepLedgerSuccessorAt (step root recognition code)))
    (data : DataAt root recognition code selected) : FullInverseAt root recognition code selected data :=
  match selected with
  | none => ⟨data⟩
  | some successor => ⟨generatedInverse root recognition code successor data⟩

def packetInverse (packet : Packet root recognition) := fullInverse root recognition packet.1
  (stepSuccessor? (step root recognition packet.1)) packet.2

def WordValueAt (selected : Option (StepLedgerSuccessorAt (step root recognition code))) : Type (u+2) :=
  match selected with
  | none => ULift.{u+2} (SourceTemporalMaterial.Action.Receipt root)
  | some successor => ULift.{u+2} (SourceHistoryCommon.Root.Evaluator.Value root (visit root code) recognition successor)

def wordEvaluation (selected : Option (StepLedgerSuccessorAt (step root recognition code)))
    (data : DataAt root recognition code selected) (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :
    WordValueAt root recognition code selected :=
  match selected with
  | none => ⟨data⟩
  | some successor => ⟨(evaluationOf root recognition code successor data).freeEvaluation word⟩
def packetWordEvaluation (packet : Packet root recognition) (word : SourceHistoryCommon.Root.G root recognition →₀ ℤ) :=
  wordEvaluation root recognition packet.1 (stepSuccessor? (step root recognition packet.1)) packet.2 word
end SourceOperationNative.Tree.Fold.Dependent.Branch.Side
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
