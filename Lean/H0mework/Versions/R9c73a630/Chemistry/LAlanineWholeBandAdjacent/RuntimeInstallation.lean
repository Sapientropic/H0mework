import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.RuntimeParent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.SourceClosure

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel WholeBandActual WholeCellBoundary
open AdjacentFlow AdjacentSpatialSource MeasureTheory
open Set
open scoped ENNReal
noncomputable section

structure AdjacentSpatialMaterial where
  parent : WholeBandCell1Runtime.WholeBandCell1Material
  domain : Set Point
  parameterMap : Point → Point
  jacobians : Point → (Point →L[ℝ] Point)
  image : Set Point
  sourceSeam : Set Point
  actualSeam : Set Point
  volume : ℝ≥0∞
  laplacianIntegral : ℝ
  bilinearIntegrals : SourceGaussianModel.MultiIndex → SourceGaussianModel.MultiIndex → ℝ

def generatedAdjacentSpatialMaterial : AdjacentSpatialMaterial where
  parent := adjacentSpatialParentMaterial
  domain := jointDomain
  parameterMap := jointMap
  jacobians := jointJacobian
  image := jointImage
  sourceSeam := AdjacentFlow.sourceSeam
  actualSeam := AdjacentFlow.actualSeam
  volume := MeasureTheory.volume jointImage
  laplacianIntegral := ∫ x in jointImage, SourceGaussianModel.laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix x
  bilinearIntegrals := fun left right => ∫ x in jointImage, SourceGaussianModel.bilinear SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix left right x

inductive AdjacentSpatialProjection
  | material | certificate

def adjacentSpatialProjectionLaw : SourceNativeProjectionLaw AdjacentSpatialLedger where
  Projection := AdjacentSpatialProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt AdjacentSpatialLedger.source occurrence × AdjacentSpatialMaterial
    | .certificate => PLift AdjacentSpatialClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (AdjacentSpatialLedger.ledgerCompiler.compile occurrence, generatedAdjacentSpatialMaterial)
    | certificate => exact ⟨sourceGeneratedAdjacentSpatialClosure⟩

def adjacentSpatialAuthoritySource := AdjacentSpatialBase.withProjectionCoface adjacentSpatialProjectionLaw
def adjacentSpatialComponentInstallation :
    SourceNativeProjectionLaw.InstallationAt adjacentSpatialProjectionLaw adjacentSpatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface AdjacentSpatialBase adjacentSpatialProjectionLaw
def adjacentSpatialInheritedInstallation :
    SourceNativeProjectionLaw.InstallationAt AdjacentSpatialBase.projectionLaw adjacentSpatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface AdjacentSpatialBase adjacentSpatialProjectionLaw

def adjacentSpatialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := adjacentSpatialAuthoritySource
  emitted := WholeBandCell1Runtime.wholeBandCell1AuthoritativeRoot.emitted
  compiler_commutes := WholeBandCell1Runtime.wholeBandCell1AuthoritativeRoot.compiler_commutes

def adjacentSpatialLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  adjacentSpatialAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem adjacentSpatial_source_and_law_unchanged :
    adjacentSpatialAuthoritySource.restructuringSource = AdjacentSpatialBase.restructuringSource ∧
    adjacentSpatialAuthoritySource.eventInventoryAdmission = AdjacentSpatialBase.eventInventoryAdmission ∧
    adjacentSpatialAuthoritySource.lawSurface = AdjacentSpatialBase.lawSurface := ⟨rfl,rfl,rfl⟩

theorem adjacentSpatial_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    adjacentSpatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      WholeBandCell1Runtime.wholeBandCell1AuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.AdjacentSpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
