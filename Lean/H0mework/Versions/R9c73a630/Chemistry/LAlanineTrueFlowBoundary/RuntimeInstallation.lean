import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel TrueFlowBoundary TrueTubeWholeActual WholeCellBoundary
noncomputable section

/-- The complete geometry parent retains its actual tangents, areas and fluxes. -/
structure TrueBoundaryMaterial where
  parent : TrueFlowGeometryRuntime.GeometryMaterial
  localExtensions : BandPoint → Point → Point
  spatialFaces : Face → Set Point

def generatedTrueBoundaryMaterial : TrueBoundaryMaterial where
  parent := trueBoundaryParentMaterial
  localExtensions := localExtension
  spatialFaces := trueSpatialFace

inductive TrueBoundaryProjection
  | material | certificate

def trueBoundaryProjectionLaw : SourceNativeProjectionLaw TrueBoundaryLedger where
  Projection := TrueBoundaryProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt TrueBoundaryLedger.source occurrence × TrueBoundaryMaterial
    | .certificate => PLift TrueFlowBoundaryClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (TrueBoundaryLedger.ledgerCompiler.compile occurrence, generatedTrueBoundaryMaterial)
    | certificate => exact ⟨sourceGeneratedTrueFlowBoundaryClosure⟩

def trueBoundaryAuthoritySource := TrueBoundaryBase.withProjectionCoface trueBoundaryProjectionLaw
def trueBoundaryComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt trueBoundaryProjectionLaw trueBoundaryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface TrueBoundaryBase trueBoundaryProjectionLaw
def trueBoundaryInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt TrueBoundaryBase.projectionLaw trueBoundaryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface TrueBoundaryBase trueBoundaryProjectionLaw

def trueBoundaryAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := trueBoundaryAuthoritySource
  emitted := TrueFlowGeometryRuntime.geometryAuthoritativeRoot.emitted
  compiler_commutes := TrueFlowGeometryRuntime.geometryAuthoritativeRoot.compiler_commutes

def trueBoundaryLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  trueBoundaryAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem trueBoundary_source_and_law_unchanged :
    trueBoundaryAuthoritySource.restructuringSource = TrueBoundaryBase.restructuringSource ∧
    trueBoundaryAuthoritySource.eventInventoryAdmission = TrueBoundaryBase.eventInventoryAdmission ∧
    trueBoundaryAuthoritySource.lawSurface = TrueBoundaryBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem trueBoundary_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    trueBoundaryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueFlowGeometryRuntime.geometryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
