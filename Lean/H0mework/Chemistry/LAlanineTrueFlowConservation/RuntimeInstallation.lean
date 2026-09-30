import H0mework.Chemistry.LAlanineTrueFlowConservation.RuntimeParent
import H0mework.Chemistry.LAlanineTrueFlowConservation.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel TrueFlowConservation TrueTubeWholeActual WholeCellBoundary
noncomputable section

/-- The complete boundary parent and its generated source volume current and canonical cap densities. -/
structure ConservationMaterial where
  parent : TrueFlowBoundaryRuntime.TrueBoundaryMaterial
  evolvingJacobians : BandPoint → ℝ → Matrix (Fin 3) (Fin 3) ℝ
  signedVolumeRates : BandPoint → ℝ → ℝ
  capFluxes : Bool → FacePoint → ℝ
  laplacianPullback : Point → ℝ

def generatedConservationMaterial : ConservationMaterial where
  parent := conservationParentMaterial
  evolvingJacobians := evolvingJacobian
  signedVolumeRates := signedVolumeRate
  capFluxes := actualCapFlux
  laplacianPullback := actualLaplacianPullback

inductive ConservationProjection
  | material | certificate

def conservationProjectionLaw : SourceNativeProjectionLaw ConservationLedger where
  Projection := ConservationProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt ConservationLedger.source occurrence × ConservationMaterial
    | .certificate => PLift TrueFlowConservationClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (ConservationLedger.ledgerCompiler.compile occurrence, generatedConservationMaterial)
    | certificate => exact ⟨sourceGeneratedTrueFlowConservationClosure⟩

def conservationAuthoritySource := ConservationBase.withProjectionCoface conservationProjectionLaw
def conservationComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt conservationProjectionLaw conservationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface ConservationBase conservationProjectionLaw
def conservationInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt ConservationBase.projectionLaw conservationAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface ConservationBase conservationProjectionLaw

def conservationAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := conservationAuthoritySource
  emitted := TrueFlowBoundaryRuntime.trueBoundaryAuthoritativeRoot.emitted
  compiler_commutes := TrueFlowBoundaryRuntime.trueBoundaryAuthoritativeRoot.compiler_commutes

def conservationLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  conservationAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem conservation_source_and_law_unchanged :
    conservationAuthoritySource.restructuringSource = ConservationBase.restructuringSource ∧
    conservationAuthoritySource.eventInventoryAdmission = ConservationBase.eventInventoryAdmission ∧
    conservationAuthoritySource.lawSurface = ConservationBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem conservation_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    conservationAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueFlowBoundaryRuntime.trueBoundaryAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowConservationRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
