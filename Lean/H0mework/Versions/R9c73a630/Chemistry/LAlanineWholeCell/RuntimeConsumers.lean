import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.RuntimeInventory

/-! Independent integral, volume, source-field and physical-next consumers read the installed certificate. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceSignedEvaluator WholeCellPartition WholeCellSpatial MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section

theorem wholeRuntime_response (runtime : LivingRuntimeState wholeRuntimeProcess) :
    Reentry.Runtime.reentryResponse runtime.state.current = wholeParentResult := by
  have keeps : ∀ {state : wholeRuntimeProcess.State}, SourceNativeRuntimeReachableAt wholeRuntimeProcess state →
      Reentry.Runtime.reentryResponse state.current = wholeParentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem wholeRead_commutes_with_physicalOccurrence (runtime : LivingRuntimeState wholeRuntimeProcess) :
    wholeParentResult.nuclear.target = Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    wholeParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    wholeParentResult.clock = Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    wholeParentResult.nuclear.targetLedger = Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change wholeParentResult.nuclear.target = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    wholeParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    wholeParentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    wholeParentResult.nuclear.targetLedger = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [wholeRuntime_response]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wholeRuntime_wholeLedger_same_occurrence (runtime : LivingRuntimeState wholeRuntimeProcess) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem wholeRuntime_complete_parent_preserved :
    generatedWholeCellMaterial.parent = SpatialRuntime.generatedSpatialMaterial ∧
    generatedWholeCellMaterial.parent.parent = ContinuousRuntime.generatedContinuousBandMaterial ∧
    wholeParentHistory = Reentry.Runtime.reentrySourceHistory ∧
    wholeParentResult.realized = Reentry.Source.targetRealized ∧
    wholeParentResult.realized = wholeParentResult.held + wholeParentResult.inheritedResidual +
      wholeParentResult.newNumericalResidual ∧
    ‖wholeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl, wholeParent_error_and_memory⟩

theorem wholeRuntime_clock_preserved (runtime : LivingRuntimeState wholeRuntimeProcess) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [wholeRuntime_response]
  exact wholeParent_clock

theorem wholeRuntime_all_fields :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧
    WholeCellReplay.SourceFieldLaw :=
  ⟨wholeRuntime_sourceCertificate.1, wholeRuntime_sourceCertificate.2.fields⟩

theorem wholeRuntime_full_coverage :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧
    generatedWholeCellMaterial.domain = ⋃ q : Quarter, generatedWholeCellMaterial.quarterDomains q ∧
    (∀ q : Quarter, (generatedWholeCellMaterial.quarterDomains q).Nonempty) ∧
    generatedWholeCellMaterial.integral = ∑ q : Quarter, generatedWholeCellMaterial.quarterIntegrals q :=
  ⟨wholeRuntime_sourceCertificate.1, wholeRuntime_sourceCertificate.2.coverage,
    wholeRuntime_sourceCertificate.2.quartersNonempty, wholeRuntime_sourceCertificate.2.signedPartition⟩

theorem wholeRuntime_geometric_image :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧
    generatedWholeCellMaterial.patch = generatedWholeCellMaterial.parameterization '' generatedWholeCellMaterial.domain ∧
    generatedWholeCellMaterial.patch ⊆ ContinuousGradient.sourceCube ∧
    IsCompact generatedWholeCellMaterial.patch ∧ generatedWholeCellMaterial.patch.Nonempty ∧
    Set.InjOn generatedWholeCellMaterial.parameterization generatedWholeCellMaterial.domain ∧
    generatedWholeCellMaterial.parent.patch ⊆ generatedWholeCellMaterial.patch :=
  ⟨wholeRuntime_sourceCertificate.1, rfl, wholeRuntime_sourceCertificate.2.sourceSupport,
    wholeRuntime_sourceCertificate.2.compact, wholeRuntime_sourceCertificate.2.nonempty,
    wholeRuntime_sourceCertificate.2.chart, wholeRuntime_sourceCertificate.2.oldPatchRetained⟩

theorem wholeRuntime_signed_volume :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧
    Holds generatedWholeCellMaterial.volumeInterval generatedWholeCellMaterial.realVolume ∧
    ((293 / 10000000000 : ℝ) < generatedWholeCellMaterial.realVolume ∧
      generatedWholeCellMaterial.realVolume < (741 / 10000000000 : ℝ)) ∧
    Holds generatedWholeCellMaterial.integralInterval generatedWholeCellMaterial.integral ∧
    ((-623 / 10000000000 : ℝ) < generatedWholeCellMaterial.integral ∧
      generatedWholeCellMaterial.integral < (-39 / 10000000000 : ℝ)) :=
  ⟨wholeRuntime_sourceCertificate.1, wholeRuntime_sourceCertificate.2.volumeEnclosure,
    wholeRuntime_sourceCertificate.2.volumeStrict, wholeRuntime_sourceCertificate.2.signedEnclosure,
    wholeRuntime_sourceCertificate.2.signedStrict⟩

theorem wholeRuntime_quarter_enclosures (q : Quarter) :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .certificate)) ∧
    Holds (generatedWholeCellMaterial.quarterIntegralIntervals q)
      (generatedWholeCellMaterial.quarterIntegrals q) ∧
    Holds (generatedWholeCellMaterial.quarterVolumeIntervals q)
      (∫ p in generatedWholeCellMaterial.quarterDomains q, (ContinuousParameterMap.jacobianMatrix 0 4 p).det) := by
  refine ⟨wholeRuntime_sourceCertificate.1,
    WholeCellReplay.quarter_integral_from_source_fields wholeRuntime_sourceCertificate.2.fields q, ?_⟩
  exact IntervalParameterMap.integralPair_contains _ _ _ (fun axis => (quarter_ordered q axis).le)
    (fun p => (ContinuousParameterMap.jacobianMatrix 0 4 p).det)
    (ContinuousParameterMap.jacobianDet_contDiff 0 4).continuous
    (WholeCellReplay.final_jacobian_contains wholeRuntime_sourceCertificate.2.fields q)

theorem wholeRuntime_density_and_integral :
    generatedWholeCellMaterial.laplacian = generatedWholeCellMaterial.parent.laplacian ∧
    generatedWholeCellMaterial.integral = ∫ x in generatedWholeCellMaterial.patch, generatedWholeCellMaterial.laplacian x ∧
    IntegrableOn generatedWholeCellMaterial.laplacian generatedWholeCellMaterial.patch :=
  ⟨rfl, rfl, wholeRuntime_sourceCertificate.2.integrable⟩

theorem wholeRuntime_actual_AO (field : WholeCellSource.Field) (jet : SourceFields.LowJet)
    (basis : SourceFiniteData.Basis) (x : Point)
    (inside : InRectangle (generatedWholeCellMaterial.rectangles field) x) :
    type_of% (wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .material)) ∧
    Holds (generatedWholeCellMaterial.sourceAO field jet basis)
      (orbital (SourceRectangle.source_terms basis) (SourceRectangle.multiindex (SourceFields.fullJet jet)) x) :=
  ⟨wholeRuntimeFace_factorizes wholeRuntimeSeed (.component .material),
    WholeCellCache.calculatedAO_contains field jet basis x inside⟩

theorem wholeRuntime_source_trace_retained :
    generatedWholeCellMaterial.sourceReceipt = WholeCellSource.packetText ∧
    generatedWholeCellMaterial.stageTrace = WholeCellReplay.generatedStates ∧
    generatedWholeCellMaterial.sourceCalls = WholeCellSource.fieldCall := ⟨rfl, rfl, rfl⟩

end
end LAlanine40K2025.BasinRefinement.WholeCellRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
