import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.RuntimeInventory

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel SourceSignedEvaluator TrueTubeActual TrueTubeTrace TrueTubeSource Set
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section

theorem tubeRuntime_response (runtime : LivingRuntimeState tubeRuntimeProcess) :
    Reentry.Runtime.reentryResponse runtime.state.current = tubeParentResult := by
  have keeps : ∀ {state : tubeRuntimeProcess.State}, SourceNativeRuntimeReachableAt tubeRuntimeProcess state →
      Reentry.Runtime.reentryResponse state.current = tubeParentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem tubeRead_commutes_with_physicalOccurrence (runtime : LivingRuntimeState tubeRuntimeProcess) :
    tubeParentResult.nuclear.target = Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    tubeParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    tubeParentResult.clock = Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    tubeParentResult.nuclear.targetLedger = Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change tubeParentResult.nuclear.target = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    tubeParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    tubeParentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    tubeParentResult.nuclear.targetLedger = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [tubeRuntime_response]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem tubeRuntime_wholeLedger_same_occurrence (runtime : LivingRuntimeState tubeRuntimeProcess) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem tubeRuntime_complete_parent_preserved :
    generatedTrueTubeMaterial.parent = BoundaryRuntime.generatedBoundaryMaterial ∧
    generatedTrueTubeMaterial.parent.parent = WholeCellRuntime.generatedWholeCellMaterial ∧
    tubeParentHistory = Reentry.Runtime.reentrySourceHistory ∧
    tubeParentResult.realized = Reentry.Source.targetRealized ∧
    tubeParentResult.realized = tubeParentResult.held + tubeParentResult.inheritedResidual +
      tubeParentResult.newNumericalResidual ∧
    ‖tubeParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl, tubeParent_error_and_memory⟩

theorem tubeRuntime_clock_preserved (runtime : LivingRuntimeState tubeRuntimeProcess) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [tubeRuntime_response]
  exact tubeParent_clock

theorem tubeRuntime_actual_flow :
    type_of% (tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial, generatedTrueTubeMaterial.firstCurves d initial 0 = initial.val ∧
      (∀ t ∈ Icc 0 (generatedTrueTubeMaterial.stepSize : ℝ),
        HasDerivWithinAt (generatedTrueTubeMaterial.firstCurves d initial)
          (signedGradient (generatedTrueTubeMaterial.signs d) (generatedTrueTubeMaterial.firstCurves d initial t))
          (Icc 0 (generatedTrueTubeMaterial.stepSize : ℝ)) t ∧
        InRectangle (generatedTrueTubeMaterial.tubeBoxes d 0) (generatedTrueTubeMaterial.firstCurves d initial t)) ∧
      InRectangle (generatedTrueTubeMaterial.endpointBoxes d 0) (generatedTrueTubeMaterial.firstCurves d initial stepSize) ∧
      InRectangle (generatedTrueTubeMaterial.initialBoxes d 1) (generatedTrueTubeMaterial.firstCurves d initial stepSize)) :=
  ⟨tubeRuntime_sourceCertificate.1, tubeRuntime_sourceCertificate.2.actualFlow⟩

theorem tubeRuntime_generated_target :
    type_of% (tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate)) ∧
    (∀ d initial, (generatedTrueTubeMaterial.firstTargets d initial).val =
      generatedTrueTubeMaterial.firstCurves d initial generatedTrueTubeMaterial.stepSize) :=
  ⟨tubeRuntime_sourceCertificate.1, tubeRuntime_sourceCertificate.2.targetGenerated⟩

theorem tubeRuntime_same_source_and_finite_map :
    type_of% (tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate)) ∧
    type_of% TrueTubeChecks.complete_source_joins ∧
    type_of% firstCurve_same_finite_initial ∧ type_of% TrueTubeError.actual_defect_norm_le :=
  ⟨tubeRuntime_sourceCertificate.1, tubeRuntime_sourceCertificate.2.joins,
    tubeRuntime_sourceCertificate.2.finiteInitial, tubeRuntime_sourceCertificate.2.finiteDefect⟩

theorem tubeRuntime_positive_source :
    type_of% (tubeRuntimeFace_factorizes tubeRuntimeSeed (.component .certificate)) ∧
    type_of% TrueTubeMatrix.sourceGeneratedInitialTubeFields ∧ type_of% actual_seed_initial :=
  ⟨tubeRuntime_sourceCertificate.1, tubeRuntime_sourceCertificate.2.fields,
    tubeRuntime_sourceCertificate.2.sourceInitial⟩

end
end LAlanine40K2025.BasinRefinement.TrueTubeRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
