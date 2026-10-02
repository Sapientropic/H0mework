import H0mework.Versions.R2.Realization.Faces.Perfectification
import H0mework.Realization.Coherent.PerfectRealization

/-!
# Root-law exposure for a dependent joint state

Before a temporal controller step exists, one fixed root inventory may expose
an occurrence-indexed Hilbert measurement, an evaluation-compatible
carrier/dual action, and a Hilbert isometry.  The projection payload contains
that complete raw family, not merely an occurrence seal.  It contains no
kernel compatibility, measurement covariance, residual verdict, radial-zero
equation, determinant, or terminal consumer.

The combined projection inventory includes the already admitted parent
cofinal-history/cochain/duality coordinate and the raw joint-state coordinate.
Recognition requires an existing `InstallationAt`; this kernel never widens a
root or calls `withProjectionCoface`.
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
variable {source : SourceNativeLedgerSource N V}
variable {H : Type u} [NormedAddCommGroup H]
variable [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev SourceOccurrenceAt (current : V.Current) :=
  source.source.toRootSource.actual.OccurrenceAt current

abbrev CarrierAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) :=
  (parent.commonLaw.historyAt occurrence).CompletionCarrier

abbrev PairingAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) :=
  CarrierAt parent occurrence →ₗ[ℤ]
    Module.Dual ℤ (CarrierAt parent occurrence)

/-- Exact raw coordinates at one node of the actual pairing tree. -/
structure RawExposureAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (pairing : PairingAt parent occurrence) : Type u where
  measurement : CarrierAt parent occurrence →ₗ[ℤ] H
  sourceAction :
    SourceGeneratedScalarEquivariantPerfectAction.ActionData pairing
  hilbertEvolution : H →ₗᵢ[ℂ] H

namespace RawExposureAt

def jointAction
    {parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source}
    {current : V.Current}
    {occurrence : SourceOccurrenceAt (source := source) current}
    {pairing : PairingAt parent occurrence}
    (exposure : RawExposureAt (H := H) parent occurrence pairing) :
    JointActionData (H := H) pairing where
  sourceAction := exposure.sourceAction
  coherentEvolution := exposure.hilbertEvolution

end RawExposureAt

/-- Root-law coordinate exposure fixed before recognition and temporal
generation. -/
structure RootLawJointStateExposure
    (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (source : SourceNativeLedgerSource N V) : Type (u + 2) where
  private mk ::
  parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source
  exposureAt : {current : V.Current} →
    (occurrence : SourceOccurrenceAt (source := source) current) →
    (pairing : PairingAt parent occurrence) →
      RawExposureAt (H := H) parent occurrence pairing

namespace RootLawJointStateExposure

def create
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    (exposureAt : {current : V.Current} →
      (occurrence : SourceOccurrenceAt (source := source) current) →
      (pairing : PairingAt parent occurrence) →
        RawExposureAt (H := H) parent occurrence pairing) :
    RootLawJointStateExposure H source :=
  ⟨parent, exposureAt⟩

/-- The fixed component inventory contains both the parent coordinate and the
complete occurrence-indexed raw joint family. -/
def toProjectionLaw (law : RootLawJointStateExposure H source) :
    SourceNativeProjectionLaw source where
  Projection := law.parent.toProjectionLaw.Projection ⊕ PUnit
  ActiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl parentProjection =>
        law.parent.toProjectionLaw.ActiveAt parentProjection occurrence
    | .inr _ => PUnit
  InactiveAt := fun projection {_current} occurrence =>
    match projection with
    | .inl parentProjection =>
        law.parent.toProjectionLaw.InactiveAt parentProjection occurrence
    | .inr _ => PEmpty
  classify := fun projection {_current} occurrence =>
    match projection with
    | .inl parentProjection =>
        law.parent.toProjectionLaw.classify parentProjection occurrence
    | .inr _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence active =>
    match projection with
    | .inl parentProjection =>
        law.parent.toProjectionLaw.PayloadAt parentProjection occurrence active
    | .inr _ =>
        (pairing : PairingAt law.parent occurrence) →
          RawExposureAt (H := H) law.parent occurrence pairing
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl parentProjection =>
        law.parent.toProjectionLaw.project parentProjection occurrence active
    | .inr _ => law.exposureAt occurrence

@[simp] theorem joint_outcomeAt_eq
    (law : RootLawJointStateExposure H source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) :
    law.toProjectionLaw.outcomeAt (.inr PUnit.unit) occurrence =
      .inl ⟨PUnit.unit, law.exposureAt occurrence⟩ :=
  rfl

/-- The parent projection is a literal component of the same preinstalled
inventory. -/
def parentComponentInstallation
    (law : RootLawJointStateExposure H source) :
    SourceNativeProjectionLaw.InstallationAt
      law.parent.toProjectionLaw law.toProjectionLaw where
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  outcome_heq := by
    intro current occurrence projection
    rfl

end RootLawJointStateExposure

/-- Recognition locks the complete combined exposure into the fixed root
projection inventory. -/
structure RecognitionAt
    (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (root : SourceNativeLivingRootClosure N V) : Type (u + 3) where
  private mk ::
  material : RootLawJointStateExposure H
    root.toAuthoritativeRoot.toLedgerRoot.source
  installation : SourceNativeProjectionLaw.InstallationAt
    material.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw

namespace RecognitionAt

variable {root : SourceNativeLivingRootClosure N V}

def create
    (material : RootLawJointStateExposure H
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      material.toProjectionLaw
      root.toAuthoritativeRoot.source.projectionLaw) :
    RecognitionAt H root :=
  ⟨material, installation⟩

def parentRecognition (recognition : RecognitionAt H root) :
    SourceNativeCofinalHistoryCochainDualityRecognitionAt root :=
  SourceNativeCofinalHistoryCochainDualityRecognitionAt.create
    recognition.material.parent
    (recognition.material.parentComponentInstallation.trans
      recognition.installation)

end RecognitionAt

end


end RootLawDependentJointStateController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
