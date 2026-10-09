import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationRuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationSourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BandConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeBandActual WholeCellBoundary
open AdjacentConservation BandConservationSource MeasureTheory
open Set
open scoped ENNReal
noncomputable section

structure BandConservationMaterial where
  parent : AdjacentSpatialRuntime.AdjacentSpatialMaterial
  evolvingJacobians : Point → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  volumeRates : Point → ℝ → ℝ
  faceParameters : Face → FacePoint → Point
  faceMaps : Face → FacePoint → Point
  faceDerivatives : Face → FacePoint → (FacePoint →L[ℝ] Point)
  faceAreas : Face → FacePoint → Point
  faceFluxes : Face → FacePoint → ℝ
  spatialFaces : Face → Set Point
  laplacianPullback : Point → ℝ
  rightSeamMap : FacePoint → Point
  rightSeamDerivative : FacePoint → (FacePoint →L[ℝ] Point)
  rightSeamArea : FacePoint → Point
  rightSeamFlux : FacePoint → ℝ

def generatedBandConservationMaterial : BandConservationMaterial where
  parent := bandConservationParentMaterial
  evolvingJacobians := WholeBandConservation.evolvingJacobian 0
  volumeRates := WholeBandConservation.signedVolumeRate 0
  faceParameters := AdjacentConservation.faceParameter
  faceMaps := actualFaceMap
  faceDerivatives := actualFaceDerivative
  faceAreas := actualOrientedArea
  faceFluxes := actualFaceFlux
  spatialFaces := actualSpatialFace
  laplacianPullback := AdjacentConservation.laplacianPullback
  rightSeamMap := AdjacentConservation.rightSeamMap
  rightSeamDerivative := AdjacentConservation.rightSeamDerivative
  rightSeamArea := AdjacentConservation.rightSeamArea
  rightSeamFlux := AdjacentConservation.rightSeamFlux

inductive BandConservationProjection
  | material | certificate

def bandConservationProjectionLaw : SourceNativeProjectionLaw BandConservationLedger where
  Projection := BandConservationProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt BandConservationLedger.source occurrence × BandConservationMaterial
    | .certificate => PLift BandConservationClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (BandConservationLedger.ledgerCompiler.compile occurrence, generatedBandConservationMaterial)
    | certificate => exact ⟨sourceGeneratedBandConservationClosure⟩

def bandConservationAuthoritySource := BandConservationBase.withProjectionCoface bandConservationProjectionLaw
def bandConservationComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt bandConservationProjectionLaw bandConservationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface BandConservationBase bandConservationProjectionLaw
def bandConservationInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt BandConservationBase.projectionLaw bandConservationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface BandConservationBase bandConservationProjectionLaw

def bandConservationAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := bandConservationAuthoritySource
  emitted := AdjacentSpatialRuntime.adjacentSpatialAuthoritativeRoot.emitted
  compiler_commutes := AdjacentSpatialRuntime.adjacentSpatialAuthoritativeRoot.compiler_commutes

def bandConservationLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  bandConservationAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem bandConservation_source_and_law_unchanged :
    bandConservationAuthoritySource.restructuringSource = BandConservationBase.restructuringSource ∧
    bandConservationAuthoritySource.eventInventoryAdmission = BandConservationBase.eventInventoryAdmission ∧
    bandConservationAuthoritySource.lawSurface = BandConservationBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem bandConservation_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    bandConservationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      AdjacentSpatialRuntime.adjacentSpatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.BandConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
