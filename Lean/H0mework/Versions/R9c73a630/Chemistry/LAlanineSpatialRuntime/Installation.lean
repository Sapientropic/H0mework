import H0mework.Versions.R9c73a630.Chemistry.LAlanineSpatialRuntime.Parent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.MatrixFinalConsumer
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousSpatialSupport.Volume

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel SourceSignedEvaluator
open SourceCellGeometry SourceRK4Replay SourceChart SourceSpatialSupport MeasureTheory
noncomputable section

def spatialSourceClosure : Prop :=
  SourceFieldMatrices.actualSpatialPatchClosure ∧
    spatialPatch ⊆ ContinuousGradient.sourceCube ∧
    IsCompact spatialPatch ∧ spatialPatch.Nonempty ∧
    Holds generatedVolumeInterval (volume.real spatialPatch) ∧
    0 < generatedVolumeInterval.1 ∧
    IntegrableOn (laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix) spatialPatch

theorem sourceGeneratedSpatialCertificate : spatialSourceClosure :=
  ⟨SourceFieldMatrices.sourceGeneratedActualSpatialPatch,
    spatialPatch_subset_sourceCube SourceFieldMatrices.all_actual_fields,
    spatialPatch_isCompact, spatialPatch_nonempty,
    spatialPatch_volume_enclosure SourceFieldMatrices.all_actual_fields,
    generatedVolume_lower_positive, spatialPatch_laplacian_integrable⟩

structure SpatialMaterial where
  parent : ContinuousRuntime.ContinuousBandMaterial
  rectangles : SourceRectangle.Field → Rectangle
  sourceFields : SourceRectangle.Field → IntervalParameterMap.FieldBox
  sourceAO : SourceRectangle.Field → SourceFields.LowJet → SourceFiniteData.Basis → Pair
  stageTrace : Fin 5 → IntervalParameterMap.JetBox
  parameterization : Point → Point
  parameterJacobian : Point → Point →L[ℝ] Point
  patch : Set Point
  laplacian : Point → ℝ
  integral : ℝ
  realVolume : ℝ
  jacobianInterval : Pair
  integralInterval : Pair
  volumeInterval : Pair

def generatedSpatialMaterial : SpatialMaterial where
  parent := spatialParentMaterial
  rectangles := SourceRectangle.actualBox
  sourceFields := recordedField
  sourceAO := SourceFields.AllFields.calculatedAO
  stageTrace := generatedStates
  parameterization := ContinuousParameterMap.parameterMap 0 4
  parameterJacobian := ContinuousParameterMap.parameterJacobian 0 4
  patch := spatialPatch
  laplacian := SourceGaussianModel.laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix
  integral := spatialLaplacianIntegral
  realVolume := volume.real spatialPatch
  jacobianInterval := generatedTargetDeterminant
  integralInterval := IntervalParameterMap.integralPair generatedTargetIntegrand cellLowerQ cellUpperQ
  volumeInterval := generatedVolumeInterval

inductive SpatialProjection
  | material | certificate

def spatialProjectionLaw : SourceNativeProjectionLaw SpatialLedger where
  Projection := SpatialProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt SpatialLedger.source occurrence × SpatialMaterial
    | .certificate => PLift spatialSourceClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (SpatialLedger.ledgerCompiler.compile occurrence, generatedSpatialMaterial)
    | certificate => exact ⟨sourceGeneratedSpatialCertificate⟩

def spatialAuthoritySource := SpatialBase.withProjectionCoface spatialProjectionLaw
def spatialComponentInstallation : SourceNativeProjectionLaw.InstallationAt spatialProjectionLaw spatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface SpatialBase spatialProjectionLaw
def spatialInheritedInstallation : SourceNativeProjectionLaw.InstallationAt SpatialBase.projectionLaw spatialAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface SpatialBase spatialProjectionLaw

def spatialAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := spatialAuthoritySource
  emitted := ContinuousRuntime.bandAuthoritativeRoot.emitted
  compiler_commutes := ContinuousRuntime.bandAuthoritativeRoot.compiler_commutes

def spatialLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  spatialAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem spatial_source_and_law_unchanged :
    spatialAuthoritySource.restructuringSource = SpatialBase.restructuringSource ∧
    spatialAuthoritySource.eventInventoryAdmission = SpatialBase.eventInventoryAdmission ∧
    spatialAuthoritySource.lawSurface = SpatialBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem spatial_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    spatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      ContinuousRuntime.bandAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
