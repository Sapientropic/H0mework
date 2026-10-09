import H0mework.Versions.R9c73a630.Chemistry.LAlanineSpatialRuntime.Inventory

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.SpatialRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceSignedEvaluator MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem spatialRuntime_response (runtime : LivingRuntimeState spatialRuntimeProcess) :
    Reentry.Runtime.reentryResponse runtime.state.current = spatialParentResult := by
  have keeps : ∀ {state : spatialRuntimeProcess.State}, SourceNativeRuntimeReachableAt spatialRuntimeProcess state →
      Reentry.Runtime.reentryResponse state.current = spatialParentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem spatialRead_commutes_with_physicalOccurrence (runtime : LivingRuntimeState spatialRuntimeProcess) :
    spatialParentResult.nuclear.target = Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    spatialParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    spatialParentResult.clock = Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    spatialParentResult.nuclear.targetLedger = Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change spatialParentResult.nuclear.target = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    spatialParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    spatialParentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    spatialParentResult.nuclear.targetLedger = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [spatialRuntime_response]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem spatialRuntime_wholeLedger_same_occurrence (runtime : LivingRuntimeState spatialRuntimeProcess) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem spatialRuntime_complete_parent_preserved :
    generatedSpatialMaterial.parent = ContinuousRuntime.generatedContinuousBandMaterial ∧
    generatedSpatialMaterial.parent.parent = Runtime.generatedRefinementMaterial ∧
    spatialParentHistory = Reentry.Runtime.reentrySourceHistory ∧
    spatialParentResult.realized = Reentry.Source.targetRealized ∧
    spatialParentResult.realized = spatialParentResult.held + spatialParentResult.inheritedResidual +
      spatialParentResult.newNumericalResidual ∧
    ‖spatialParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl, spatialParent_error_and_memory⟩

theorem spatialRuntime_clock_preserved (runtime : LivingRuntimeState spatialRuntimeProcess) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [spatialRuntime_response]
  exact spatialParent_clock

theorem spatialRuntime_all_fields :
    type_of% (spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .certificate)) ∧
    SourceRK4Replay.SourceFieldLaw :=
  ⟨spatialRuntime_sourceCertificate.1, spatialRuntime_sourceCertificate.2.1.1⟩

theorem spatialRuntime_geometric_image :
    type_of% (spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .certificate)) ∧
    generatedSpatialMaterial.patch = generatedSpatialMaterial.parameterization '' SourceCellGeometry.cellDomain ∧
    generatedSpatialMaterial.patch ⊆ ContinuousGradient.sourceCube ∧
    IsCompact generatedSpatialMaterial.patch ∧ generatedSpatialMaterial.patch.Nonempty ∧
    Set.InjOn generatedSpatialMaterial.parameterization SourceCellGeometry.cellDomain := by
  rcases spatialRuntime_sourceCertificate with ⟨factor, core, support, compact, nonempty, _⟩
  exact ⟨factor, rfl, support, compact, nonempty, core.2.1⟩

theorem spatialRuntime_signed_volume :
    type_of% (spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .certificate)) ∧
    Holds generatedSpatialMaterial.volumeInterval generatedSpatialMaterial.realVolume ∧
    0 < generatedSpatialMaterial.volumeInterval.1 ∧
    0 < volume generatedSpatialMaterial.patch ∧
    ((-112 / 100000000000 : ℝ) < generatedSpatialMaterial.integral ∧
      generatedSpatialMaterial.integral < (-25 / 100000000000 : ℝ)) := by
  rcases spatialRuntime_sourceCertificate with ⟨factor, core, _, _, _, volumeBound, positive, _⟩
  exact ⟨factor, volumeBound, positive, core.2.2.2.2.2, core.2.2.2.2.1⟩

theorem spatialRuntime_density_and_integral :
    generatedSpatialMaterial.laplacian = generatedSpatialMaterial.parent.parent.laplacian ∧
    generatedSpatialMaterial.integral = ∫ x in generatedSpatialMaterial.patch, generatedSpatialMaterial.laplacian x ∧
    IntegrableOn generatedSpatialMaterial.laplacian generatedSpatialMaterial.patch :=
  ⟨rfl, rfl, spatialRuntime_sourceCertificate.2.2.2.2.2.2.2⟩

theorem spatialRuntime_actual_AO (field : SourceRectangle.Field) (jet : SourceFields.LowJet)
    (basis : SourceFiniteData.Basis) (x : Point)
    (inside : InRectangle (generatedSpatialMaterial.rectangles field) x) :
    type_of% (spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .material)) ∧
    Holds (generatedSpatialMaterial.sourceAO field jet basis)
      (orbital (SourceRectangle.source_terms basis) (SourceRectangle.multiindex (SourceFields.fullJet jet)) x) :=
  ⟨spatialRuntimeFace_factorizes spatialRuntimeSeed (.component .material),
    SourceFields.AllFields.calculatedAO_contains field jet basis x inside⟩

end
end LAlanine40K2025.BasinRefinement.SpatialRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
