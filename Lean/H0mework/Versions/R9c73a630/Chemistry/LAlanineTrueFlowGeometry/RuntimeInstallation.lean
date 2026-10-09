import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open LAlanine40K2025.Root SourceGaussianModel TrueFlowGeometry TrueTubeWholeActual WholeCellPartition
noncomputable section

/-- Complete parent data, original transverse source and the actual invertible spatial geometry. -/
structure GeometryMaterial where
  parent : TrueFlowDifferentialRuntime.DifferentialMaterial
  normal : Point
  callLower : TrueTubeSource.Call → ℚ
  responseEquivs : BandPoint → Time → Point ≃L[ℝ] Point
  jacobianEquivs : BandPoint → Point ≃L[ℝ] Point
  planeRead : Point → ℝ
  spatialImage : Set Point
  derivative : Point → Point →L[ℝ] Point

def generatedGeometryMaterial : GeometryMaterial where
  parent := geometryParentMaterial
  normal := seedNormal
  callLower := callTransverseLower
  responseEquivs := initialFlowDerivativeEquiv
  jacobianEquivs := trueJacobianEquiv
  planeRead := planeCoordinate
  spatialImage := truePatch
  derivative := actualDerivative

inductive GeometryProjection
  | material | certificate

def geometryProjectionLaw : SourceNativeProjectionLaw GeometryLedger where
  Projection := GeometryProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt GeometryLedger.source occurrence × GeometryMaterial
    | .certificate => PLift TrueFlowGeometryClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (GeometryLedger.ledgerCompiler.compile occurrence, generatedGeometryMaterial)
    | certificate => exact ⟨sourceGeneratedTrueFlowGeometryClosure⟩

def geometryAuthoritySource := GeometryBase.withProjectionCoface geometryProjectionLaw
def geometryComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt geometryProjectionLaw geometryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface GeometryBase geometryProjectionLaw
def geometryInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt GeometryBase.projectionLaw geometryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface GeometryBase geometryProjectionLaw

def geometryAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := geometryAuthoritySource
  emitted := TrueFlowDifferentialRuntime.differentialAuthoritativeRoot.emitted
  compiler_commutes := TrueFlowDifferentialRuntime.differentialAuthoritativeRoot.compiler_commutes

def geometryLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  geometryAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem geometry_source_and_law_unchanged :
    geometryAuthoritySource.restructuringSource = GeometryBase.restructuringSource ∧
    geometryAuthoritySource.eventInventoryAdmission = GeometryBase.eventInventoryAdmission ∧
    geometryAuthoritySource.lawSurface = GeometryBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem geometry_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    geometryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueFlowDifferentialRuntime.differentialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
