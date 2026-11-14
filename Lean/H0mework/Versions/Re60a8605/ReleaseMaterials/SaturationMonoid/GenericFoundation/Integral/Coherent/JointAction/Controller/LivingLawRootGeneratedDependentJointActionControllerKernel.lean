import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Coherent.JointAction.Controller.LivingLawRootGeneratedDependentJointActionExposureKernel
import H0mework.Realization.JointState.StateController

/-!
# Root controller for a dependent joint-action occurrence

An installed three-face exposure reuses the existing joint-state step and its
parent pairing occurrence.  Every pairing node generates one canonical orbit
input, its minimal action-stable carrier and the single action `Omega` on that
carrier.  The complete input and Omega trees are dependent relabellings of the
same parent occurrence.

The step accepts no commuting square, covariance/residual verdict, branch,
ledger or next current.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootLawDependentJointActionController

open RootLawDependentJointStateController
open SourceGeneratedIntegralCoherentJointAction

noncomputable section

universe u

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H Q : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [AddCommGroup Q]

/-- The actual canonical action carried by one installed input.  The equality
locks it to the minimal-orbit constructor; this payload is not a branch bit. -/
structure GeneratedOmegaAt {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    (input : SourceGeneratedIntegralCoherentJointAction.Input I H Q) where
  private mk ::
  action : input.Carrier →ₗ[ℤ] input.Carrier
  action_eq : action = input.omega

namespace GeneratedOmegaAt

def generate {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    (input : SourceGeneratedIntegralCoherentJointAction.Input I H Q) :
    GeneratedOmegaAt input :=
  ⟨input.omega, rfl⟩

def carrier {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    {input : SourceGeneratedIntegralCoherentJointAction.Input I H Q}
    (_generated : GeneratedOmegaAt input) :=
  input.Carrier

def omega {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    {input : SourceGeneratedIntegralCoherentJointAction.Input I H Q}
    (generated : GeneratedOmegaAt input) : input.Carrier →ₗ[ℤ] input.Carrier :=
  generated.action

@[simp] theorem omega_eq {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    {input : SourceGeneratedIntegralCoherentJointAction.Input I H Q}
    (generated : GeneratedOmegaAt input) : generated.omega = input.omega :=
  generated.action_eq

/-- The generated carrier retains the existing minimality theorem. -/
theorem carrier_minimal {I H Q : Type u}
    [AddCommGroup I] [AddCommGroup H] [AddCommGroup Q]
    {input : SourceGeneratedIntegralCoherentJointAction.Input I H Q}
    (_generated : GeneratedOmegaAt input)
    (candidate : Submodule ℤ input.Ambient)
    (containsSeed : ∀ event, input.seed event ∈ candidate)
    (stable : ∀ state, state ∈ candidate →
      input.ambientAction state ∈ candidate) :
    input.carrier ≤ candidate :=
  input.carrier_minimal candidate containsSeed stable

end GeneratedOmegaAt

/-- Exact temporal step generated only from a fixed installed recognition. -/
structure StepAt
    {root : SourceNativeLivingRootClosure N V}
    (recognition : RecognitionAt H Q root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) : Type (u + 4) where
  private mk ::

namespace StepAt

variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : RecognitionAt H Q root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate : StepAt recognition visit :=
  ⟨⟩

/-- Existing root-controlled joint-state step; this is the sole source of
occurrence, pairing inventory, whole-ledger write-back and next current. -/
def parentStep (_step : StepAt recognition visit) :
    RootLawDependentJointStateController.StepAt
      recognition.existingRecognition visit :=
  recognition.existingRecognition.generateStepAt visit

def sourceOccurrence (step : StepAt recognition visit) :=
  step.parentStep.sourceOccurrence

/-- The same complete parent pairing occurrence, spelled with the new
material index so dependent maps elaborate without a cast. -/
def parentPairingOccurrence (step : StepAt recognition visit) :=
  recognition.material.existing.parent.pairingAt step.sourceOccurrence

theorem parentPairingOccurrence_eq_parentStep
    (step : StepAt recognition visit) :
    HEq step.parentPairingOccurrence
      step.parentStep.parentPairingOccurrence :=
  HEq.rfl

def jointInputAt (step : StepAt recognition visit)
    (pairing : PairingAt recognition.material.existing.parent
      step.sourceOccurrence) :=
  recognition.material.jointInputAt step.sourceOccurrence pairing

abbrev InputPayload (step : StepAt recognition visit) :=
  Sigma fun _pairing : PairingAt recognition.material.existing.parent
      step.sourceOccurrence =>
    SourceGeneratedIntegralCoherentJointAction.Input
      (CarrierAt recognition.material.existing.parent step.sourceOccurrence) H Q

/-- The complete pairing occurrence mapped into canonical joint-action inputs. -/
def inputOccurrence (step : StepAt recognition visit) :
    RootedAccountedUnfolding step.InputPayload :=
  step.parentPairingOccurrence.map fun pairing =>
    ⟨pairing, step.jointInputAt pairing⟩

theorem inputOccurrence_rooted (step : StepAt recognition visit) :
    step.inputOccurrence.map Sigma.fst = step.parentPairingOccurrence := by
  rw [inputOccurrence, RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id step.parentPairingOccurrence

abbrev OmegaPayload (step : StepAt recognition visit) :=
  Sigma fun pairing : PairingAt recognition.material.existing.parent
      step.sourceOccurrence =>
    GeneratedOmegaAt (step.jointInputAt pairing)

/-- Every input node generates its unique minimal-orbit `Omega`. -/
def omegaOccurrence (step : StepAt recognition visit) :
    RootedAccountedUnfolding step.OmegaPayload :=
  step.parentPairingOccurrence.map fun pairing =>
    ⟨pairing, GeneratedOmegaAt.generate (step.jointInputAt pairing)⟩

theorem omegaOccurrence_rooted (step : StepAt recognition visit) :
    step.omegaOccurrence.map Sigma.fst = step.parentPairingOccurrence := by
  rw [omegaOccurrence, RootedAccountedUnfolding.map_map]
  exact RootedAccountedUnfolding.map_id step.parentPairingOccurrence

def rootInput (step : StepAt recognition visit) :=
  step.jointInputAt step.parentPairingOccurrence.root

def rootOmega (step : StepAt recognition visit) :
    step.rootInput.Carrier →ₗ[ℤ] step.rootInput.Carrier :=
  (GeneratedOmegaAt.generate step.rootInput).omega

@[simp] theorem rootOmega_eq_generated (step : StepAt recognition visit) :
    step.rootOmega = step.rootInput.omega :=
  GeneratedOmegaAt.omega_eq _

/-- All three actions are projections of the one generated root `Omega`. -/
theorem rootOmega_three_faces (step : StepAt recognition visit) :
    step.rootInput.integralFace.comp step.rootOmega =
        step.rootInput.integralAction.comp step.rootInput.integralFace ∧
      step.rootInput.coherentFace.comp step.rootOmega =
        step.rootInput.coherentAction.comp step.rootInput.coherentFace ∧
      step.rootInput.measurementFace.comp step.rootOmega =
        step.rootInput.measurementAction.comp step.rootInput.measurementFace := by
  rw [step.rootOmega_eq_generated]
  exact ⟨step.rootInput.integralFace_omega,
    step.rootInput.coherentFace_omega,
    step.rootInput.measurementFace_omega⟩

def wholeLedgerWriteBack (step : StepAt recognition visit) :=
  step.parentStep.wholeLedgerWriteBack

def nextCurrent (step : StepAt recognition visit) :=
  step.parentStep.nextCurrent

/-- The three-face input family was already installed in the fixed root. -/
theorem installedJointAction_factorizes (step : StepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed (.inr PUnit.unit))
        step.sourceOccurrence)
      (recognition.material.toProjectionLaw.outcomeAt
        (.inr PUnit.unit) step.sourceOccurrence) :=
  recognition.installation.outcome_heq step.sourceOccurrence (.inr PUnit.unit)

theorem installedJointAction_factorizes_to_input
    (step : StepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed (.inr PUnit.unit))
        step.sourceOccurrence)
      ((.inl ⟨PUnit.unit,
          recognition.material.jointInputAt step.sourceOccurrence⟩) :
        SourceNativeProjectionFiberAt recognition.material.toProjectionLaw
          (.inr PUnit.unit) step.sourceOccurrence) := by
  simpa only [Material.joint_outcomeAt_eq] using
    step.installedJointAction_factorizes

theorem wholeLedgerWriteBack_eq_root (step : StepAt recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.parentStep.wholeLedgerWriteBack_eq_root

@[simp] theorem nextCurrent_eq_root (step : StepAt recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.parentStep.nextCurrent_eq_root

/-- Exact controller mouth. -/
theorem controllerMouth (step : StepAt recognition visit) :
    step.inputOccurrence.map Sigma.fst = step.parentPairingOccurrence ∧
      step.omegaOccurrence.map Sigma.fst = step.parentPairingOccurrence ∧
      step.rootOmega = step.rootInput.omega ∧
      (step.rootInput.integralFace.comp step.rootOmega =
        step.rootInput.integralAction.comp step.rootInput.integralFace ∧
       step.rootInput.coherentFace.comp step.rootOmega =
        step.rootInput.coherentAction.comp step.rootInput.coherentFace ∧
       step.rootInput.measurementFace.comp step.rootOmega =
        step.rootInput.measurementAction.comp step.rootInput.measurementFace) ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed (.inr PUnit.unit))
          step.sourceOccurrence)
        (recognition.material.toProjectionLaw.outcomeAt
          (.inr PUnit.unit) step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨step.inputOccurrence_rooted, step.omegaOccurrence_rooted,
    step.rootOmega_eq_generated, step.rootOmega_three_faces,
    step.installedJointAction_factorizes,
    step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

end StepAt

namespace RecognitionAt

def generateStepAt
    {root : SourceNativeLivingRootClosure N V}
    (recognition : RecognitionAt H Q root)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    StepAt recognition visit :=
  StepAt.generate

end RecognitionAt

end

end RootLawDependentJointActionController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
