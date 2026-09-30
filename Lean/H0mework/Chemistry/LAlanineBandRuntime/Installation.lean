import H0mework.Chemistry.LAlanineBandRuntime.Parent
import H0mework.Chemistry.LAlanineBandSource.Closure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel SourceSignedEvaluator IntervalParameterMap WholeBandSource
noncomputable section

structure WholeBandMaterial where
  parent : TrueFlowQuantitativeRuntime.QuantitativeMaterial
  callBoxes : FullBandCall → Rectangle
  callReports : FullBandCall → FieldBox
  initialBoxes : FullBandCell → Direction → Step → Rectangle
  tubeBoxes : FullBandCell → Direction → Step → Rectangle
  endpointBoxes : FullBandCell → Direction → Step → Rectangle
  cellDomains : FullBandCell → Set Point
  cellSeeds : FullBandCell → Point → Point
  certifiedCalls : CertifiedCall → FullBandCall
  newInitialCache : WholeBandCache.Material
  newInitialMatrix : WholeBandMatrix.Rows

def generatedWholeBandMaterial : WholeBandMaterial where
  parent := wholeBandParentMaterial
  callBoxes := callBox
  callReports := recordedCallField
  initialBoxes := initialBox
  tubeBoxes := tubeBox
  endpointBoxes := endpointBox
  cellDomains := WholeBandGeometry.cellDomain
  cellSeeds := WholeBandGeometry.cellSeed
  certifiedCalls := certifiedCall
  newInitialCache := WholeBandCache.Call0.material
  newInitialMatrix := WholeBandCache.Call0.matrixRows

inductive WholeBandProjection
  | material | certificate

def wholeBandProjectionLaw : SourceNativeProjectionLaw WholeBandLedger where
  Projection := WholeBandProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeBandLedger.source occurrence × WholeBandMaterial
    | .certificate => PLift WholeBandSourceClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeBandLedger.ledgerCompiler.compile occurrence, generatedWholeBandMaterial)
    | certificate => exact ⟨sourceGeneratedWholeBandSourceClosure⟩

def wholeBandAuthoritySource := WholeBandBase.withProjectionCoface wholeBandProjectionLaw
def wholeBandComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt wholeBandProjectionLaw wholeBandAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBandBase wholeBandProjectionLaw
def wholeBandInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt WholeBandBase.projectionLaw wholeBandAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBandBase wholeBandProjectionLaw

def wholeBandAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeBandAuthoritySource
  emitted := TrueFlowQuantitativeRuntime.quantitativeAuthoritativeRoot.emitted
  compiler_commutes := TrueFlowQuantitativeRuntime.quantitativeAuthoritativeRoot.compiler_commutes

def wholeBandLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeBandAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeBand_source_and_law_unchanged :
    wholeBandAuthoritySource.restructuringSource = WholeBandBase.restructuringSource ∧
    wholeBandAuthoritySource.eventInventoryAdmission = WholeBandBase.eventInventoryAdmission ∧
    wholeBandAuthoritySource.lawSurface = WholeBandBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem wholeBand_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeBandAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueFlowQuantitativeRuntime.quantitativeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
