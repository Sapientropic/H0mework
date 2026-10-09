import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.SpatialRuntimeRuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.SpatialRuntimeSourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeBandActual WholeCellBoundary
open WholeBandCell0Spatial WholeBandCell0Boundary WholeBandCell0Conservation WholeBandCell0SpatialSource
open Set
noncomputable section

structure WholeBandCell0SpatialMaterial where
  parent : WholeBandCell0DifferentialRuntime.WholeBandCell0DifferentialMaterial
  image : Set Point
  derivative : Point → Point →L[ℝ] Point
  faceDomains : Fin 3 → Set FacePoint
  spatialFaces : Face → Set Point
  faceMaps : Face → FacePoint → Point
  faceDerivatives : (face : Face) → (p : FacePoint) → p ∈ faceDomains face.1 → FacePoint →L[ℝ] Point
  areas : (face : Face) → (p : FacePoint) → p ∈ faceDomains face.1 → Point
  fluxes : (face : Face) → (p : FacePoint) → p ∈ faceDomains face.1 → ℝ
  evolvingJacobian : Cell0Point → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  volumeRate : Cell0Point → ℝ → ℝ
  capFlux : Bool → FacePoint → ℝ
  laplacianPullback : Point → ℝ
  paidPair : Cell0Point ⊕ TrueTubeWholeActual.BandPoint → Point

def generatedWholeBandCell0SpatialMaterial : WholeBandCell0SpatialMaterial where
  parent := wholeBandCell0SpatialParentMaterial
  image := cell0_truePatch
  derivative := cell0_actualDerivative
  faceDomains := cell0_faceDomain
  spatialFaces := cell0_trueSpatialFace
  faceMaps := cell0_trueFaceMap
  faceDerivatives := cell0_trueFaceDerivative
  areas := cell0_trueOrientedArea
  fluxes := cell0_trueFaceFlux
  evolvingJacobian := cell0_evolvingJacobian
  volumeRate := cell0_signedVolumeRate
  capFlux := cell0_actualCapFlux
  laplacianPullback := cell0_actualLaplacianPullback
  paidPair := WholeBandCrossGeometry.paidPairMap

inductive WholeBandCell0SpatialProjection
  | material | certificate

def wholeBandCell0SpatialProjectionLaw : SourceNativeProjectionLaw WholeBandCell0SpatialLedger where
  Projection := WholeBandCell0SpatialProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeBandCell0SpatialLedger.source occurrence × WholeBandCell0SpatialMaterial
    | .certificate => PLift WholeBandCell0SpatialClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeBandCell0SpatialLedger.ledgerCompiler.compile occurrence, generatedWholeBandCell0SpatialMaterial)
    | certificate => exact ⟨sourceGeneratedWholeBandCell0SpatialClosure⟩

def wholeBandCell0SpatialAuthoritySource := WholeBandCell0SpatialBase.withProjectionCoface wholeBandCell0SpatialProjectionLaw
def wholeBandCell0SpatialComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt wholeBandCell0SpatialProjectionLaw wholeBandCell0SpatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBandCell0SpatialBase wholeBandCell0SpatialProjectionLaw
def wholeBandCell0SpatialInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt WholeBandCell0SpatialBase.projectionLaw wholeBandCell0SpatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBandCell0SpatialBase wholeBandCell0SpatialProjectionLaw

def wholeBandCell0SpatialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeBandCell0SpatialAuthoritySource
  emitted := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialAuthoritativeRoot.emitted
  compiler_commutes := WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialAuthoritativeRoot.compiler_commutes

def wholeBandCell0SpatialLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeBandCell0SpatialAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem wholeBandCell0Spatial_source_and_law_unchanged :
    wholeBandCell0SpatialAuthoritySource.restructuringSource = WholeBandCell0SpatialBase.restructuringSource ∧
    wholeBandCell0SpatialAuthoritySource.eventInventoryAdmission = WholeBandCell0SpatialBase.eventInventoryAdmission ∧
    wholeBandCell0SpatialAuthoritySource.lawSurface = WholeBandCell0SpatialBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem wholeBandCell0Spatial_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeBandCell0SpatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandCell0DifferentialRuntime.wholeBandCell0DifferentialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
