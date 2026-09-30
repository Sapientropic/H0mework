import H0mework.Chemistry.LAlanineWholeCell.RuntimeParent
import H0mework.Chemistry.LAlanineWholeCell.SpatialProducer
import H0mework.Chemistry.LAlanineWholeCell.CacheComplete

/-! Install the full-cell calculation and its source-generated certificate on the same root coface. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel SourceSignedEvaluator
open WholeCellPartition WholeCellSpatial MeasureTheory
noncomputable section

/-- Complete source trace and every signed quarter remain alongside the entire inherited material. -/
structure WholeCellMaterial where
  parent : SpatialRuntime.SpatialMaterial
  sourceReceipt : String
  rectangles : WholeCellSource.Field → Rectangle
  sourceFields : WholeCellSource.Field → IntervalParameterMap.FieldBox
  sourceAO : WholeCellSource.Field → SourceFields.LowJet → SourceFiniteData.Basis → Pair
  sourceCalls : Quarter → Fin 17 → WholeCellSource.Field
  stageTrace : Quarter → Fin 5 → IntervalParameterMap.JetBox
  domain : Set Point
  quarterDomains : Quarter → Set Point
  parameterization : Point → Point
  parameterJacobian : Point → Point →L[ℝ] Point
  commonJacobian : IntervalParameterMap.MatrixPair
  patch : Set Point
  laplacian : Point → ℝ
  quarterIntegrals : Quarter → ℝ
  integral : ℝ
  realVolume : ℝ
  quarterIntegralIntervals : Quarter → Pair
  quarterVolumeIntervals : Quarter → Pair
  integralInterval : Pair
  volumeInterval : Pair

def generatedWholeCellMaterial : WholeCellMaterial where
  parent := wholeParentMaterial
  sourceReceipt := WholeCellSource.packetText
  rectangles := WholeCellSource.box
  sourceFields := WholeCellReplay.recordedField
  sourceAO := WholeCellCache.calculatedAO
  sourceCalls := WholeCellSource.fieldCall
  stageTrace := WholeCellReplay.generatedStates
  domain := fullDomain
  quarterDomains := quarterDomain
  parameterization := ContinuousParameterMap.parameterMap 0 4
  parameterJacobian := ContinuousParameterMap.parameterJacobian 0 4
  commonJacobian := WholeCellReplay.commonJacobian
  patch := fullPatch
  laplacian := SourceGaussianModel.laplacian SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix
  quarterIntegrals := quarterSignedIntegral
  integral := fullLaplacianIntegral
  realVolume := volume.real fullPatch
  quarterIntegralIntervals := quarterIntegralInterval
  quarterVolumeIntervals := quarterVolumeInterval
  integralInterval := fullIntegralInterval
  volumeInterval := fullVolumeInterval

inductive WholeCellProjection
  | material | certificate

def wholeProjectionLaw : SourceNativeProjectionLaw WholeLedger where
  Projection := WholeCellProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt WholeLedger.source occurrence × WholeCellMaterial
    | .certificate => PLift WholeCellClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (WholeLedger.ledgerCompiler.compile occurrence, generatedWholeCellMaterial)
    | certificate => exact ⟨sourceGeneratedWholeCellClosure⟩

def wholeAuthoritySource := WholeBase.withProjectionCoface wholeProjectionLaw
def wholeComponentInstallation : SourceNativeProjectionLaw.InstallationAt wholeProjectionLaw wholeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface WholeBase wholeProjectionLaw
def wholeInheritedInstallation : SourceNativeProjectionLaw.InstallationAt WholeBase.projectionLaw wholeAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface WholeBase wholeProjectionLaw

def wholeAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := wholeAuthoritySource
  emitted := SpatialRuntime.spatialAuthoritativeRoot.emitted
  compiler_commutes := SpatialRuntime.spatialAuthoritativeRoot.compiler_commutes

def wholeLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  wholeAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem whole_source_and_law_unchanged :
    wholeAuthoritySource.restructuringSource = WholeBase.restructuringSource ∧
    wholeAuthoritySource.eventInventoryAdmission = WholeBase.eventInventoryAdmission ∧
    wholeAuthoritySource.lawSurface = WholeBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem whole_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    wholeAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      SpatialRuntime.spatialAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.WholeCellRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
