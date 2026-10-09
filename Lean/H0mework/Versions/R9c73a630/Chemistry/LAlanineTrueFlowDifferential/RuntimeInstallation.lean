import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.LAlanineTrueFlowDifferential
open LAlanine40K2025.Root SourceGaussianModel TrueFlowDifferential TrueTubeWholeActual
open WholeCellBoundary WholeCellBoundary.Geometry
noncomputable section

/-- The whole original flow and its generated differential and actual face geometry. -/
structure DifferentialMaterial where
  parent : TrueTubeWholeRuntime.WholeTubeMaterial
  rawPaths : Point → Path
  responses : BandPoint → Space →L[ℝ] Path
  initialDerivatives : BandPoint → Time → Space →L[ℝ] Space
  parameterMap : Point → Point
  jacobians : BandPoint → Point →L[ℝ] Point
  faceMaps : Face → FacePoint → Point
  faceDerivatives : (face : Face) → (p : FacePoint) →
    p ∈ faceDomain face.1 → FacePoint →L[ℝ] Point
  faceTangents : (face : Face) → (p : FacePoint) → p ∈ faceDomain face.1 → Fin 2 → Point
  orientedAreas : (face : Face) → (p : FacePoint) → p ∈ faceDomain face.1 → Point
  faceFluxes : (face : Face) → (p : FacePoint) → p ∈ faceDomain face.1 → ℝ

def generatedDifferentialMaterial : DifferentialMaterial where
  parent := differentialParentMaterial
  rawPaths := rawPath
  responses := sourceResponse
  initialDerivatives := initialFlowDerivative
  parameterMap := trueParameterMap
  jacobians := trueJacobian
  faceMaps := trueFaceMap
  faceDerivatives := trueFaceDerivative
  faceTangents := trueFaceTangent
  orientedAreas := trueOrientedArea
  faceFluxes := trueFaceFlux

inductive DifferentialProjection
  | material | certificate

def differentialProjectionLaw : SourceNativeProjectionLaw DifferentialLedger where
  Projection := DifferentialProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt DifferentialLedger.source occurrence × DifferentialMaterial
    | .certificate => PLift TrueFlowDifferentialClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (DifferentialLedger.ledgerCompiler.compile occurrence, generatedDifferentialMaterial)
    | certificate => exact ⟨sourceGeneratedTrueFlowDifferentialClosure⟩

def differentialAuthoritySource := DifferentialBase.withProjectionCoface differentialProjectionLaw
def differentialComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt differentialProjectionLaw differentialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface DifferentialBase differentialProjectionLaw
def differentialInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt DifferentialBase.projectionLaw differentialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface DifferentialBase differentialProjectionLaw

def differentialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := differentialAuthoritySource
  emitted := TrueTubeWholeRuntime.wholeTubeAuthoritativeRoot.emitted
  compiler_commutes := TrueTubeWholeRuntime.wholeTubeAuthoritativeRoot.compiler_commutes

def differentialLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  differentialAuthoritativeRoot.toLivingWithoutFaithfulTerminal
    (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem differential_source_and_law_unchanged :
    differentialAuthoritySource.restructuringSource = DifferentialBase.restructuringSource ∧
    differentialAuthoritySource.eventInventoryAdmission = DifferentialBase.eventInventoryAdmission ∧
    differentialAuthoritySource.lawSurface = DifferentialBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem differential_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    differentialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      TrueTubeWholeRuntime.wholeTubeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferentialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
