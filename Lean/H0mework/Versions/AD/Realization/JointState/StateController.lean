import H0mework.Versions.AD.Realization.JointState.StateExposure

/-!
# Root-controlled dependent joint-state admission

A private recognition-indexed step consumes the preinstalled raw exposure,
maps the parent's complete pairing occurrence to `GeneratedJointState`, and
inherits the parent cofinal-duality step's whole-ledger write-back and next.
No public constructor accepts a free joint state, disposition branch, ledger,
or next current.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointStateController

open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open SourceGeneratedIntegralEquivariantPerfectRealization

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact temporal step; its constructor is private and it can only be
generated from an installed recognition. -/
structure StepAt
    {root : SourceNativeLivingRootClosure N V}
    (recognition : RecognitionAt H root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 3) where
  private mk ::

namespace StepAt

variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : StepAt recognition visit :=
  ⟨⟩

def parentStep (_step : StepAt recognition visit) :
    RootGeneratedCofinalHistoryCochainDualityStepAt
      recognition.parentRecognition visit :=
  recognition.parentRecognition.generateStepAt visit

def sourceOccurrence (step : StepAt recognition visit) :=
  step.parentStep.sourceOccurrence

def exposureAt (step : StepAt recognition visit)
    (pairing : PairingAt recognition.material.parent
      step.sourceOccurrence) :
    RawExposureAt (H := H) recognition.material.parent
      step.sourceOccurrence pairing :=
  recognition.material.exposureAt step.sourceOccurrence pairing

abbrev JointStateAt (step : StepAt recognition visit)
    (pairing : PairingAt recognition.material.parent
      step.sourceOccurrence) :=
  GeneratedJointState pairing (step.exposureAt pairing).measurement
    (step.exposureAt pairing).jointAction

def generatedJointStateAt (step : StepAt recognition visit)
    (pairing : PairingAt recognition.material.parent
      step.sourceOccurrence) : step.JointStateAt pairing :=
  SourceGeneratedIntegralEquivariantPerfectRealization.generate pairing
    (step.exposureAt pairing).measurement
    (step.exposureAt pairing).jointAction

abbrev JointPayload (step : StepAt recognition visit) :=
  Σ pairing : PairingAt recognition.material.parent
      step.sourceOccurrence,
    step.JointStateAt pairing

def parentPairingOccurrence (step : StepAt recognition visit) :
    RootedAccountedUnfolding
      (PairingAt recognition.material.parent step.sourceOccurrence) :=
  recognition.material.parent.pairingAt step.sourceOccurrence

theorem parentPairingOccurrence_eq_parentStep
    (step : StepAt recognition visit) :
    HEq step.parentPairingOccurrence
      step.parentStep.pairingFace.actualPairing :=
  HEq.rfl

/-- The joint state is a dependent relabelling of the complete parent pairing
tree. -/
def jointOccurrence (step : StepAt recognition visit) :
    RootedAccountedUnfolding step.JointPayload :=
  step.parentPairingOccurrence.map fun pairing =>
    ⟨pairing, step.generatedJointStateAt pairing⟩

theorem jointOccurrence_projects_to_parent
    (step : StepAt recognition visit) :
    step.jointOccurrence.map Sigma.fst =
      step.parentPairingOccurrence := by
  rw [jointOccurrence, RootedAccountedUnfolding.map_map]
  change step.parentPairingOccurrence.map id =
    step.parentPairingOccurrence
  exact RootedAccountedUnfolding.map_id step.parentPairingOccurrence

@[simp] theorem jointOccurrence_root
    (step : StepAt recognition visit) :
    step.jointOccurrence.root =
      ⟨step.parentPairingOccurrence.root,
        step.generatedJointStateAt step.parentPairingOccurrence.root⟩ := by
  exact RootedAccountedUnfolding.root_map _
    step.parentPairingOccurrence

def rootJointState (step : StepAt recognition visit) :
    step.JointStateAt step.parentPairingOccurrence.root :=
  step.generatedJointStateAt step.parentPairingOccurrence.root

def wholeLedgerWriteBack (step : StepAt recognition visit) :=
  step.parentStep.wholeLedgerWriteBack

def nextCurrent (step : StepAt recognition visit) :=
  step.parentStep.nextCurrent

/-- Root authority reads the exact preinstalled combined exposure. -/
theorem installedJointState_factorizes
    (step : StepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed (.inr PUnit.unit))
        step.sourceOccurrence)
      (recognition.material.toProjectionLaw.outcomeAt
        (.inr PUnit.unit) step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence
    (.inr PUnit.unit)

/-- The same factorization reduced to the complete raw measurement/action
family. -/
theorem installedJointState_factorizes_to_raw
    (step : StepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed (.inr PUnit.unit))
        step.sourceOccurrence)
      ((.inl ⟨PUnit.unit,
          recognition.material.exposureAt step.sourceOccurrence⟩) :
        SourceNativeProjectionFiberAt
          recognition.material.toProjectionLaw
          (.inr PUnit.unit) step.sourceOccurrence) := by
  simpa only [RootLawJointStateExposure.joint_outcomeAt_eq] using
    step.installedJointState_factorizes

theorem wholeLedgerWriteBack_eq_root
    (step : StepAt recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        visit.current) :=
  step.parentStep.wholeLedgerWriteBack_eq_root

@[simp] theorem nextCurrent_eq_root
    (step : StepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.parentStep.nextCurrent_eq_root

/-- Exact controller mouth.  The only mathematical output is regenerated
from installed raw coordinates; the occurrence, installation, ledger and next
are jointly visible. -/
theorem controllerMouth (step : StepAt recognition visit) :
    step.rootJointState =
        SourceGeneratedIntegralEquivariantPerfectRealization.generate
          step.parentPairingOccurrence.root
          (step.exposureAt
            step.parentPairingOccurrence.root).measurement
          (step.exposureAt
            step.parentPairingOccurrence.root).jointAction ∧
      step.jointOccurrence.map Sigma.fst =
        step.parentPairingOccurrence ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed (.inr PUnit.unit))
          step.sourceOccurrence)
        (recognition.material.toProjectionLaw.outcomeAt
          (.inr PUnit.unit) step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨rfl, step.jointOccurrence_projects_to_parent,
    step.installedJointState_factorizes,
    step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

end StepAt

namespace RecognitionAt

variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : RecognitionAt H root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    StepAt recognition visit :=
  StepAt.generate

end RecognitionAt

end


end RootLawDependentJointStateController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
