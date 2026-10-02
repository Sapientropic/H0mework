import H0mework.Realization.JointState.Transition
import H0mework.Versions.R2.Realization.JointState.StateController

/-!
# Root controller for dependent joint transitions

The source ledger compiler alone selects terminal or successor.  On a
successor, the current and target occurrence generate the history and joint
naturality disposition.  The wrapper reuses the existing whole ledger and
heterogeneous next; it accepts no target, map, branch, equation, ledger or
next from a caller.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointTransition

open CofinalHistorySettlement
open CofinalHistoryTransition
open RootLawDependentJointStateController

noncomputable section

universe u

abbrev StepLedgerSuccessorAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :=
  SourceNativeLedgerGeneratedSuccessorAt step.sourceOccurrence
    (root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
      step.sourceOccurrence)

def stepSuccessor?
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) : Option (StepLedgerSuccessorAt step) :=
  SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
      step.sourceOccurrence)

abbrev StepSourceHistory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :=
  recognition.material.parent.commonLaw.historyAt step.sourceOccurrence

abbrev StepTargetHistory
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :=
  recognition.material.parent.commonLaw.historyAt successor.targetOccurrence

def stepSourcePairing
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :
    (StepSourceHistory step).CompletionCarrier →ₗ[ℤ]
      Module.Dual ℤ (StepSourceHistory step).CompletionCarrier :=
  (recognition.material.parent.pairingAt step.sourceOccurrence).root

def stepTargetPairing
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    (StepTargetHistory step successor).CompletionCarrier →ₗ[ℤ]
      Module.Dual ℤ (StepTargetHistory step successor).CompletionCarrier :=
  (recognition.material.parent.pairingAt successor.targetOccurrence).root

def stepSourceExposure
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :=
  step.exposureAt (stepSourcePairing step)

def stepSourceExposureAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit)
    (pairing : PairingAt recognition.material.parent step.sourceOccurrence) :=
  recognition.material.exposureAt step.sourceOccurrence pairing

def stepTargetExposure
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :=
  recognition.material.exposureAt successor.targetOccurrence
    (stepTargetPairing step successor)

def stepSourcePairingOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :=
  recognition.material.parent.pairingAt step.sourceOccurrence

def stepTargetPairingOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :=
  recognition.material.parent.pairingAt successor.targetOccurrence

@[simp] theorem stepTargetPairingOccurrence_exact
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    stepTargetPairingOccurrence step successor =
      recognition.material.parent.pairingAt successor.targetOccurrence :=
  rfl

abbrev StepJointTransitionPayload
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :=
  Σ pairing : PairingAt recognition.material.parent step.sourceOccurrence,
    JointTransitionDispositionAt history pairing
      (stepTargetPairing step successor)
      (stepSourceExposureAt step pairing).sourceAction.carrierAction
      (stepTargetExposure step successor).sourceAction.carrierAction
      (stepSourceExposureAt step pairing).measurement
      (stepTargetExposure step successor).measurement
      (stepSourceExposureAt step pairing).hilbertEvolution
      (stepTargetExposure step successor).hilbertEvolution

def stepJointTransitionPayloadAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor))
    (pairing : PairingAt recognition.material.parent step.sourceOccurrence) :
    StepJointTransitionPayload step successor history :=
  ⟨pairing, settleJointTransition history pairing
    (stepTargetPairing step successor)
    (stepSourceExposureAt step pairing).sourceAction.carrierAction
    (stepTargetExposure step successor).sourceAction.carrierAction
    (stepSourceExposureAt step pairing).measurement
    (stepTargetExposure step successor).measurement
    (stepSourceExposureAt step pairing).hilbertEvolution
    (stepTargetExposure step successor).hilbertEvolution⟩

def stepJointTransitionOccurrence
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :
    RootedAccountedUnfolding
      (StepJointTransitionPayload step successor history) :=
  (stepSourcePairingOccurrence step).map
    (stepJointTransitionPayloadAt step successor history)

theorem stepJointTransitionOccurrence_rooted
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :
    (stepJointTransitionOccurrence step successor history).map Sigma.fst =
      stepSourcePairingOccurrence step := by
  rw [stepJointTransitionOccurrence, RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id (stepSourcePairingOccurrence step)

/-- The full source pairing tree receives a joint transition disposition;
the target pairing tree remains independently visible at the exact compiler
target occurrence. -/
structure GeneratedStepJointTransitionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    Type (u + 1) where
  history : GeneratedTransition (StepSourceHistory step)
    (StepTargetHistory step successor)
  jointFace : RootedAccountedUnfolding
    (StepJointTransitionPayload step successor history)
  joint_rooted : jointFace.map Sigma.fst = stepSourcePairingOccurrence step

def generateStepJointTransition
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (history : GeneratedTransition (StepSourceHistory step)
      (StepTargetHistory step successor)) :
    GeneratedStepJointTransitionAt step successor where
  history := history
  jointFace := stepJointTransitionOccurrence step successor history
  joint_rooted := stepJointTransitionOccurrence_rooted step successor history

inductive StepSuccessorDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    Type (u + 1)
  | generated
      (transition : GeneratedStepJointTransitionAt step successor)
  | generatorResidual
      (coordinate : GeneratorResidual (StepSourceHistory step)
        (StepTargetHistory step successor))
  | relationResidual
      (generatorCompatible :
        (StepSourceHistory step).generatorClosure ≤
          (StepTargetHistory step successor).generatorClosure)
      (coordinate : RelationResidual (StepSourceHistory step)
        (StepTargetHistory step successor) generatorCompatible)

noncomputable def settleStepSuccessor
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step) :
    StepSuccessorDispositionAt step successor :=
  match CofinalHistoryTransition.settle (StepSourceHistory step)
      (StepTargetHistory step successor) with
  | .generated history =>
      .generated (generateStepJointTransition step successor history)
  | .generatorResidual coordinate => .generatorResidual coordinate
  | .relationResidual compatible coordinate =>
      .relationResidual compatible coordinate

/-- Total temporal disposition.  The terminal/successor branch is read from
the compiler image, not chosen by a caller. -/
inductive StepDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) : Type (u + 1)
  | terminal (exact : stepSuccessor? step = none)
  | successor (next : StepLedgerSuccessorAt step)
      (exact : stepSuccessor? step = some next)
      (disposition : StepSuccessorDispositionAt step next)

noncomputable def settleStep
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) : StepDispositionAt step :=
  match exact : stepSuccessor? step with
  | none => .terminal exact
  | some successor => .successor successor exact
      (settleStepSuccessor step successor)

/-- The typed transition disposition, root ledger and heterogeneous next are
one controller readout. -/
theorem controllerMouth
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    {root : SourceNativeLivingRootClosure N V}
    {recognition : RecognitionAt H root}
    {visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot}
    (step : StepAt recognition visit) :
    Nonempty (StepDispositionAt step) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨⟨settleStep step⟩, step.wholeLedgerWriteBack_eq_root,
    step.nextCurrent_eq_root⟩

end

end RootLawDependentJointTransition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
