import H0mework.Chemistry.LAlanineTrueFlowQuantitative.RuntimeParent
import H0mework.Chemistry.LAlanineTrueFlowQuantitative.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceSignedEvaluator IntervalParameterMap TrueTubeSource
open TrueFlowQuantitative WholeCellPartition
noncomputable section

/-- The complete conservation parent and the original numerical reports used by its actual bounds. -/
structure QuantitativeMaterial where
  parent : TrueFlowConservationRuntime.ConservationMaterial
  traceReports : Call → Pair
  seedWidthReport : Pair
  seedTransverseCeiling : ℚ
  parameterMeasure : ℚ

def generatedQuantitativeMaterial : QuantitativeMaterial where
  parent := quantitativeParentMaterial
  traceReports := callTracePair
  seedWidthReport := SourceCellGeometry.reportedBandWidth
  seedTransverseCeiling := seedTransverseUpper
  parameterMeasure := rationalBoxVolume fullLowerQ fullUpperQ

inductive QuantitativeProjection
  | material | certificate

def quantitativeProjectionLaw : SourceNativeProjectionLaw QuantitativeLedger where
  Projection := QuantitativeProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt QuantitativeLedger.source occurrence × QuantitativeMaterial
    | .certificate => PLift TrueFlowQuantitativeClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (QuantitativeLedger.ledgerCompiler.compile occurrence, generatedQuantitativeMaterial)
    | certificate => exact ⟨sourceGeneratedTrueFlowQuantitativeClosure⟩

def quantitativeAuthoritySource := QuantitativeBase.withProjectionCoface quantitativeProjectionLaw
def quantitativeComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt quantitativeProjectionLaw quantitativeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface QuantitativeBase quantitativeProjectionLaw
def quantitativeInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt QuantitativeBase.projectionLaw quantitativeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface QuantitativeBase quantitativeProjectionLaw

def quantitativeAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := quantitativeAuthoritySource
  emitted := TrueFlowConservationRuntime.conservationAuthoritativeRoot.emitted
  compiler_commutes := TrueFlowConservationRuntime.conservationAuthoritativeRoot.compiler_commutes

def quantitativeLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  quantitativeAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem quantitative_source_and_law_unchanged :
    quantitativeAuthoritySource.restructuringSource = QuantitativeBase.restructuringSource ∧
    quantitativeAuthoritySource.eventInventoryAdmission = QuantitativeBase.eventInventoryAdmission ∧
    quantitativeAuthoritySource.lawSurface = QuantitativeBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem quantitative_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    quantitativeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueFlowConservationRuntime.conservationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowQuantitativeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
