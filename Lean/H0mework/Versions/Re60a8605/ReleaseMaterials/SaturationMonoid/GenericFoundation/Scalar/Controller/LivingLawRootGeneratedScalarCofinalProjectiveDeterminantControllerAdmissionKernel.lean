import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Controller.LivingLawRootGeneratedScalarCofinalProjectiveDeterminantSourceMaterialKernel

/-!
# Root-controlled scalar cofinal determinant admission

Only a source-installed scalar material law can generate this controller
step.  The step reconstructs data, compatibility, evaluation, and observation
from the exact parent source occurrence, reruns the generic determinant
settlement, and inherits the already admitted whole-ledger write-back and
generated next.  No public constructor accepts a free scalar face or result.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ScalarCofinalProjectiveDeterminantController

open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open CofinalHistoryCochainDuality.RootGeneratedCofinalHistoryCochainDualityStepAt
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarCofinalProjectiveDeterminantDisposition

noncomputable section

universe w r u d o

variable {N : WorldRelationNetwork.{w}} {V : Vocabulary.{w}}
variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {StageCarrier : ℕ → Type u}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable [∀ stage, Module R (StageCarrier stage)]
variable {DualTarget : Type d}
variable [AddCommGroup DualTarget] [Module R DualTarget]
variable {Observation : Type o}
variable [AddCommGroup Observation] [Module R Observation]

/-! ## Installed recognition -/

structure SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
    (root : SourceNativeLivingRootClosure N V) :
    Type (max w r u d o + 2) where
  private mk ::
  materialLaw : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
    (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
    (DualTarget := DualTarget) (Observation := Observation)
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    materialLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw

namespace SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt

variable {root : SourceNativeLivingRootClosure N V}

def create
    (materialLaw : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation)
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      materialLaw.toProjectionLaw
      root.toAuthoritativeRoot.source.projectionLaw) :
    SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) root :=
  ⟨materialLaw, installation⟩

def parentRecognition
    (recognition : SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) root) :
    SourceNativeCofinalHistoryCochainDualityRecognitionAt root :=
  SourceNativeCofinalHistoryCochainDualityRecognitionAt.create
    recognition.materialLaw.parent recognition.installation

end SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt

/-! ## Exact generated step -/

structure RootGeneratedScalarCofinalProjectiveDeterminantStepAt
    {root : SourceNativeLivingRootClosure N V}
    (recognition : SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    Type (max w r u d o + 2) where
  private mk ::

namespace RootGeneratedScalarCofinalProjectiveDeterminantStepAt

variable {root : SourceNativeLivingRootClosure N V}
variable {recognition :
  SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
    (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
    (DualTarget := DualTarget) (Observation := Observation) root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

def generate :
    RootGeneratedScalarCofinalProjectiveDeterminantStepAt recognition visit :=
  ⟨⟩

def parentStep
    (_step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    RootGeneratedCofinalHistoryCochainDualityStepAt
      recognition.parentRecognition visit :=
  recognition.parentRecognition.generateStepAt visit

def sourceOccurrence
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :=
  step.parentStep.sourceOccurrence

def data
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    Data (R := R) (Generator := Generator) (Carrier := StageCarrier) :=
  recognition.materialLaw.dataAt step.sourceOccurrence

theorem compatible
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) : step.data.Compatible :=
  recognition.materialLaw.compatibleAt step.sourceOccurrence

def scalarFace
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :=
  scalarFaceAt recognition.materialLaw.parent step.sourceOccurrence step.data

theorem calculation
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    Face.GeneratedCompatibilityCalculationAt step.scalarFace :=
  scalarCalculationAt recognition.materialLaw.parent
    step.sourceOccurrence step.data step.compatible

def evaluation
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    step.scalarFace.completion step.calculation →ₗ[R]
      Module.Dual R DualTarget :=
  recognition.materialLaw.evaluationAt step.sourceOccurrence

def observation
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    SourceGeneratedScalarCofinalExactEnvelope.Carrier
        step.scalarFace step.calculation step.evaluation →ₗ[R]
      Observation :=
  recognition.materialLaw.observationAt step.sourceOccurrence

abbrev DeterminantDisposition
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :=
  SourceGeneratedScalarCofinalProjectiveDeterminantDisposition.DeterminantDisposition
    step.scalarFace step.calculation step.evaluation step.observation

noncomputable def disposition
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) : step.DeterminantDisposition :=
  SourceGeneratedScalarCofinalProjectiveDeterminantDisposition.settle
    step.scalarFace step.calculation step.evaluation step.observation

def wholeLedgerWriteBack
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :=
  step.parentStep.wholeLedgerWriteBack

def nextCurrent
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :=
  step.parentStep.nextCurrent

theorem scalarFace_root_eq_parent
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    step.scalarFace.root = step.parentStep.commonStep.history.root :=
  scalarFaceAt_root_eq_parent recognition.materialLaw.parent
    step.sourceOccurrence step.data

/-- The source-installed scalar material factors through the root's existing
projection law at this exact source occurrence. -/
theorem installedScalar_factorizes
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit)
        step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  step.parentStep.installedDuality_factorizes

theorem wholeLedgerWriteBack_eq_root
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    HEq step.wholeLedgerWriteBack
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        visit.current) :=
  step.parentStep.wholeLedgerWriteBack_eq_root

@[simp] theorem nextCurrent_eq_root
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.parentStep.nextCurrent_eq_root

/-- Exact controller mouth.  The disposition is regenerated from installed
source material, and the same occurrence seal, ledger row, and next are
jointly visible. -/
theorem controllerMouth
    (step : RootGeneratedScalarCofinalProjectiveDeterminantStepAt
      recognition visit) :
    step.disposition =
        SourceGeneratedScalarCofinalProjectiveDeterminantDisposition.settle
          step.scalarFace step.calculation step.evaluation step.observation ∧
      step.scalarFace.root = step.parentStep.commonStep.history.root ∧
      HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.installation.embed PUnit.unit)
          step.sourceOccurrence)
        (recognition.materialLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨rfl, step.scalarFace_root_eq_parent, step.installedScalar_factorizes,
    step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

end RootGeneratedScalarCofinalProjectiveDeterminantStepAt

namespace SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt

variable {root : SourceNativeLivingRootClosure N V}

def generateStepAt
    (recognition : SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) root)
    (visit : SourceNativeTemporalVisitAt
      root.toAuthoritativeRoot.toLedgerRoot) :
    RootGeneratedScalarCofinalProjectiveDeterminantStepAt recognition visit :=
  RootGeneratedScalarCofinalProjectiveDeterminantStepAt.generate

end SourceNativeScalarCofinalProjectiveDeterminantRecognitionAt

end

end ScalarCofinalProjectiveDeterminantController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
