import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Coherent.PerfectRealization.Dependent.Action.LivingLawRootGeneratedDependentJointActionOccurrenceKernel
import H0mework.Versions.Rb81a4438.Realization.JointState.StateExposure

/-!
# Root-installed dependent joint-action exposure

The existing root-law joint-state exposure already owns the source action,
Hilbert measurement and coherent evolution at every occurrence/pairing node.
This component extension adds only a fixed detector carrier `Q` with its
occurrence/pairing-indexed action and read.  The five maps are assembled into
the canonical integral/coherent joint-action input before root recognition.

No commuting square, covariance verdict, residual-zero witness, branch,
ledger or next current enters this material law.
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
variable {source : SourceNativeLedgerSource N V}
variable {H Q : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] [AddCommGroup Q]

/-- Exact detector coordinates at one already existing pairing node. -/
structure DetectorExposureAt
    (existing : RootLawJointStateExposure H source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (_pairing : PairingAt existing.parent occurrence) where
  action : Q →ₗ[ℤ] Q
  read : CarrierAt existing.parent occurrence →ₗ[ℤ] Q

/-- Component extension of the existing joint-state material. -/
structure Material
    (H Q : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup Q]
    (source : SourceNativeLedgerSource N V) : Type (u + 2) where
  private mk ::
  existing : RootLawJointStateExposure H source
  detectorAt : {current : V.Current} →
    (occurrence : SourceOccurrenceAt (source := source) current) →
    (pairing : PairingAt existing.parent occurrence) →
      DetectorExposureAt (Q := Q) existing occurrence pairing

namespace Material

def create
    (existing : RootLawJointStateExposure H source)
    (detectorAt : {current : V.Current} →
      (occurrence : SourceOccurrenceAt (source := source) current) →
      (pairing : PairingAt existing.parent occurrence) →
        DetectorExposureAt (Q := Q) existing occurrence pairing) :
    Material H Q source :=
  ⟨existing, detectorAt⟩

/-- The old raw exposure and the detector coordinate become the five maps of
one source-generated orbit input. -/
def jointInputAt (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    SourceGeneratedIntegralCoherentJointAction.Input
      (CarrierAt material.existing.parent occurrence) H Q where
  integralAction :=
    (material.existing.exposureAt occurrence pairing).sourceAction.carrierAction
  coherentAction :=
    (material.existing.exposureAt occurrence pairing
      ).hilbertEvolution.toLinearMap.restrictScalars ℤ
  measurementAction := (material.detectorAt occurrence pairing).action
  coherentRead :=
    (material.existing.exposureAt occurrence pairing).measurement
  measurementRead := (material.detectorAt occurrence pairing).read

@[simp] theorem jointInputAt_integralAction
    (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    (material.jointInputAt occurrence pairing).integralAction =
      (material.existing.exposureAt occurrence pairing
        ).sourceAction.carrierAction :=
  rfl

@[simp] theorem jointInputAt_coherentAction
    (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    (material.jointInputAt occurrence pairing).coherentAction =
      (material.existing.exposureAt occurrence pairing
        ).hilbertEvolution.toLinearMap.restrictScalars ℤ :=
  rfl

@[simp] theorem jointInputAt_coherentRead
    (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    (material.jointInputAt occurrence pairing).coherentRead =
      (material.existing.exposureAt occurrence pairing).measurement :=
  rfl

@[simp] theorem jointInputAt_measurementAction
    (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    (material.jointInputAt occurrence pairing).measurementAction =
      (material.detectorAt occurrence pairing).action :=
  rfl

@[simp] theorem jointInputAt_measurementRead
    (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt material.existing.parent occurrence) :
    (material.jointInputAt occurrence pairing).measurementRead =
      (material.detectorAt occurrence pairing).read :=
  rfl

/-- The new inventory is a literal component extension of the old law. -/
def toProjectionLaw (material : Material H Q source) :
    SourceNativeProjectionLaw source where
  Projection := material.existing.toProjectionLaw.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl old => material.existing.toProjectionLaw.ActiveAt old occurrence
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl old => material.existing.toProjectionLaw.InactiveAt old occurrence
    | .inr _ => PEmpty
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl old => material.existing.toProjectionLaw.classify old occurrence
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl old =>
        material.existing.toProjectionLaw.PayloadAt old occurrence active
    | .inr _ =>
        (pairing : PairingAt material.existing.parent occurrence) →
          SourceGeneratedIntegralCoherentJointAction.Input
            (CarrierAt material.existing.parent occurrence) H Q
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl old =>
        material.existing.toProjectionLaw.project old occurrence active
    | .inr _ => material.jointInputAt occurrence

@[simp] theorem joint_outcomeAt_eq (material : Material H Q source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) :
    material.toProjectionLaw.outcomeAt (.inr PUnit.unit) occurrence =
      .inl ⟨PUnit.unit, material.jointInputAt occurrence⟩ :=
  rfl

/-- Existing joint-state coordinates remain a literal installed component. -/
def existingComponentInstallation (material : Material H Q source) :
    SourceNativeProjectionLaw.InstallationAt
      material.existing.toProjectionLaw material.toProjectionLaw where
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  outcome_heq := by
    intro current occurrence projection
    cases projection with
    | inl parent =>
        dsimp only [SourceNativeProjectionLaw.outcomeAt, toProjectionLaw,
          RootLawJointStateExposure.toProjectionLaw]
        cases material.existing.parent.toProjectionLaw.classify parent occurrence <;> rfl
    | inr joint => cases joint; rfl

end Material

/-- Recognition requires the three-face extension to be present in the fixed
root inventory before a temporal step can be generated. -/
structure RecognitionAt
    (H Q : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [AddCommGroup Q]
    (root : SourceNativeLivingRootClosure N V) : Type (u + 3) where
  private mk ::
  material : Material H Q root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    material.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw

namespace RecognitionAt

variable {root : SourceNativeLivingRootClosure N V}

def create
    (material : Material H Q root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      material.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw) :
    RecognitionAt H Q root :=
  ⟨material, installation⟩

/-- Forget only the new detector coordinate while retaining installation in
the same fixed root. -/
def existingRecognition (recognition : RecognitionAt H Q root) :
    RootLawDependentJointStateController.RecognitionAt H root :=
  RootLawDependentJointStateController.RecognitionAt.create
    recognition.material.existing
    (recognition.material.existingComponentInstallation.trans
      recognition.installation)

end RecognitionAt

end

end RootLawDependentJointActionController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
