import H0mework.Chemistry.LAlanineBoundary.RuntimeParent
import H0mework.Chemistry.LAlanineBoundary.SourceProducer

/-! Install the actual boundary coordinate before the original root emits its occurrence. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeCellPartition WholeCellBoundary
noncomputable section

structure BoundaryMaterial where
  parent : WholeCellRuntime.WholeCellMaterial
  sourceChart : Point → Point
  sourceJacobian : Point → Matrix (Fin 3) (Fin 3) ℝ
  gradient : Point → Point
  pullback : Point → Point
  faceDomains : Fin 3 → Set FacePoint
  parameters : Face → FacePoint → Point
  actualFaces : Face → Set Point
  tangents : Face → FacePoint → Fin 2 → Point
  areas : Face → FacePoint → Point
  faceFluxes : Face → FacePoint → ℝ
  faceIntegrals : Face → ℝ
  quarterFluxes : Quarter → ℝ
  totalFlux : ℝ

def generatedBoundaryMaterial : BoundaryMaterial where
  parent := boundaryParentMaterial
  sourceChart := chart
  sourceJacobian := chartJacobian
  gradient := ContinuousGradient.sourceGradient
  pullback := pulledFlux
  faceDomains := faceDomain
  parameters := faceParameter
  actualFaces := spatialFace
  tangents := WholeCellBoundary.Geometry.faceTangent
  areas := WholeCellBoundary.Geometry.orientedAreaVector
  faceFluxes := faceFlux
  faceIntegrals := faceIntegral
  quarterFluxes := quarterNetFlux
  totalFlux := netFlux

inductive BoundaryProjection
  | material | certificate

def boundaryProjectionLaw : SourceNativeProjectionLaw BoundaryLedger where
  Projection := BoundaryProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt BoundaryLedger.source occurrence × BoundaryMaterial
    | .certificate => PLift GradientBoundaryClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (BoundaryLedger.ledgerCompiler.compile occurrence, generatedBoundaryMaterial)
    | certificate => exact ⟨sourceGeneratedGradientBoundaryClosure⟩

def boundaryAuthoritySource := BoundaryBase.withProjectionCoface boundaryProjectionLaw
def boundaryComponentInstallation : SourceNativeProjectionLaw.InstallationAt boundaryProjectionLaw boundaryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface BoundaryBase boundaryProjectionLaw
def boundaryInheritedInstallation : SourceNativeProjectionLaw.InstallationAt BoundaryBase.projectionLaw boundaryAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface BoundaryBase boundaryProjectionLaw

def boundaryAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := boundaryAuthoritySource
  emitted := WholeCellRuntime.wholeAuthoritativeRoot.emitted
  compiler_commutes := WholeCellRuntime.wholeAuthoritativeRoot.compiler_commutes

def boundaryLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  boundaryAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem boundary_source_and_law_unchanged :
    boundaryAuthoritySource.restructuringSource = BoundaryBase.restructuringSource ∧
    boundaryAuthoritySource.eventInventoryAdmission = BoundaryBase.eventInventoryAdmission ∧
    boundaryAuthoritySource.lawSurface = BoundaryBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem boundary_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    boundaryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeCellRuntime.wholeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.BoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
