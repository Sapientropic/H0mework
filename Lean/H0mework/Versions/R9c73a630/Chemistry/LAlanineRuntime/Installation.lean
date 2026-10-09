import H0mework.Versions.R9c73a630.Chemistry.LAlanineRuntime.Parent
import H0mework.Versions.R9c73a630.Chemistry.LAlanineFlow.Restart
import H0mework.Versions.R9c73a630.Chemistry.LAlanineParametric.BandFlow
import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.CellGeometry
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousMatrix.Regression
import H0mework.Versions.R2.Realization.Faces.ProjectionCoface

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.ContinuousRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open LAlanine40K2025.Root SourceGaussianModel
noncomputable section

def bandSourceClosure : Prop :=
  ContinuousFlow.sourceFlowClosure ∧ ContinuousBandFlow.bandFlowClosure ∧
    SourceCellGeometry.cellGeometryClosure ∧ SourceSignedMatrix.firstFieldClosure

theorem sourceGeneratedContinuousBand : bandSourceClosure :=
  ⟨ContinuousFlow.sourceGeneratedContinuousGradientFlow, ContinuousBandFlow.sourceGeneratedActualBandFlow,
    SourceCellGeometry.sourceGeneratedCellGeometry, SourceSignedMatrix.sourceGeneratedActualFirstField⟩

structure ContinuousBandMaterial where
  parent : Runtime.RefinementMaterial
  gradient : Point → Point
  hessian : Point → Fin 3 → Fin 3 → ℝ
  sourceFlow : ContinuousFlow.InitialPoint → ℝ → Point
  bandFlow : (run : Geometry.Data.RunIndex) → (segment : ContinuousSeed.Segment) →
    ContinuousBandFlow.SeedParameters segment → ℝ → Point
  flowWindow : ℝ
  firstRectangle : SourceSignedEvaluator.Rectangle
  firstGradient : Fin 3 → SourceSignedEvaluator.Pair
  firstHessian : Fin 3 → Fin 3 → SourceSignedEvaluator.Pair
  firstLaplacian : SourceSignedEvaluator.Pair
  certifiedField : SourceRectangle.Field
  remainingField : Fin 16 → SourceRectangle.Field
  initialJet : IntervalParameterMap.JetBox
  stepSize : SourceSignedEvaluator.Pair
  stepDerivative : IntervalParameterMap.VectorPair
  parameterDomain : Set Point
  rectangleSource : String
  allFieldSource : String

def generatedContinuousBandMaterial : ContinuousBandMaterial where
  parent := bandParentMaterial
  gradient := ContinuousGradient.sourceGradient
  hessian := ContinuousGradient.sourceHessian
  sourceFlow := ContinuousFlow.sourceFlow
  bandFlow := ContinuousBandFlow.generatedBandFlow
  flowWindow := ContinuousFlow.timeRadius
  firstRectangle := SourceRectangle.actualBox 0
  firstGradient := SourceSignedMatrix.sourceGradientBox
  firstHessian := SourceSignedMatrix.sourceHessianBox
  firstLaplacian := SourceSignedMatrix.sourceLaplacianBox
  certifiedField := 0
  remainingField := fun i => ⟨i.val + 1, by omega⟩
  initialJet := SourceCellGeometry.initialJetBox
  stepSize := SourceCellGeometry.stepSizeInterval
  stepDerivative := SourceCellGeometry.stepDerivativeInterval
  parameterDomain := SourceCellGeometry.cellDomain
  rectangleSource := SourceRectangle.rectangleText
  allFieldSource := SourceRectangle.fieldText

inductive ContinuousBandProjection
  | material | certificate

def bandProjectionLaw : SourceNativeProjectionLaw BandLedger where
  Projection := ContinuousBandProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ => match projection with
    | .material => SourceNativeLedgerEvolutionAt BandLedger.source occurrence × ContinuousBandMaterial
    | .certificate => PLift bandSourceClosure
  project := by
    intro projection current occurrence active
    cases projection with
    | material => exact (BandLedger.ledgerCompiler.compile occurrence, generatedContinuousBandMaterial)
    | certificate => exact ⟨sourceGeneratedContinuousBand⟩

def bandAuthoritySource := BandBase.withProjectionCoface bandProjectionLaw
def bandComponentInstallation : SourceNativeProjectionLaw.InstallationAt bandProjectionLaw bandAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface BandBase bandProjectionLaw
def bandInheritedInstallation : SourceNativeProjectionLaw.InstallationAt BandBase.projectionLaw bandAuthoritySource.projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface BandBase bandProjectionLaw

def bandAuthoritativeRoot : SourceNativeAuthoritativeRootClosure N Reentry.Runtime.ReentryV where
  source := bandAuthoritySource
  emitted := Runtime.refinementAuthoritativeRoot.emitted
  compiler_commutes := Runtime.refinementAuthoritativeRoot.compiler_commutes

def bandLivingRoot : SourceNativeLivingRootClosure N Reentry.Runtime.ReentryV :=
  bandAuthoritativeRoot.toLivingWithoutFaithfulTerminal (fun _ => ⟨fun terminal => nomatch terminal⟩)

theorem band_source_and_law_unchanged :
    bandAuthoritySource.restructuringSource = BandBase.restructuringSource ∧
    bandAuthoritySource.eventInventoryAdmission = BandBase.eventInventoryAdmission ∧
    bandAuthoritySource.lawSurface = BandBase.lawSurface := ⟨rfl, rfl, rfl⟩

theorem band_rootCompiler_unchanged (current : Reentry.Runtime.ReentryCurrent) :
    bandAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current =
      Runtime.refinementAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current := rfl

end
end LAlanine40K2025.BasinRefinement.ContinuousRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
