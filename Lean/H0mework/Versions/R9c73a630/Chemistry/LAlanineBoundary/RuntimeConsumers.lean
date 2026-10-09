import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.RuntimeInventory

/-! Actual geometry and flux are read through the fixed facade and its original next. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.BoundaryRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGaussianModel WholeCellPartition WholeCellBoundary Set MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator
noncomputable section

theorem boundaryRuntime_response (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    Reentry.Runtime.reentryResponse runtime.state.current = boundaryParentResult := by
  have keeps : ∀ {state : boundaryRuntimeProcess.State}, SourceNativeRuntimeReachableAt boundaryRuntimeProcess state →
      Reentry.Runtime.reentryResponse state.current = boundaryParentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem boundaryRead_commutes_with_physicalOccurrence (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    boundaryParentResult.nuclear.target = Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    boundaryParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    boundaryParentResult.clock = Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    boundaryParentResult.nuclear.targetLedger = Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change boundaryParentResult.nuclear.target = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    boundaryParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    boundaryParentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    boundaryParentResult.nuclear.targetLedger = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [boundaryRuntime_response]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem boundaryRuntime_wholeLedger_same_occurrence (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem boundaryRuntime_complete_parent_preserved :
    generatedBoundaryMaterial.parent = WholeCellRuntime.generatedWholeCellMaterial ∧
    generatedBoundaryMaterial.parent.parent = SpatialRuntime.generatedSpatialMaterial ∧
    boundaryParentHistory = Reentry.Runtime.reentrySourceHistory ∧
    boundaryParentResult.realized = Reentry.Source.targetRealized ∧
    boundaryParentResult.realized = boundaryParentResult.held + boundaryParentResult.inheritedResidual +
      boundaryParentResult.newNumericalResidual ∧
    ‖boundaryParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  ⟨rfl, rfl, rfl, rfl, boundaryParent_error_and_memory⟩

theorem boundaryRuntime_clock_preserved (runtime : LivingRuntimeState boundaryRuntimeProcess) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [boundaryRuntime_response]
  exact boundaryParent_clock

theorem boundaryRuntime_actual_faces :
    type_of% (boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate)) ∧
    frontier generatedBoundaryMaterial.parent.patch = ⋃ face : Face, generatedBoundaryMaterial.actualFaces face ∧
    (∀ face : Face, ∃ p ∈ generatedBoundaryMaterial.actualFaces face,
      p ∈ frontier generatedBoundaryMaterial.parent.patch) :=
  ⟨boundaryRuntime_sourceCertificate.1, boundaryRuntime_sourceCertificate.2.boundary,
    boundaryRuntime_sourceCertificate.2.nonemptyFaces⟩

theorem boundaryRuntime_actual_area :
    type_of% (boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate)) ∧
    type_of% WholeCellBoundary.Geometry.faceTangent_is_actual_derivative ∧
    type_of% WholeCellBoundary.Geometry.orientedAreaVector_eq_cross ∧
    type_of% WholeCellBoundary.Geometry.orientedAreaVector_nonzero ∧
    (∀ face p, generatedBoundaryMaterial.faceFluxes face p =
      generatedBoundaryMaterial.gradient (generatedBoundaryMaterial.sourceChart (generatedBoundaryMaterial.parameters face p))
        ⬝ᵥ generatedBoundaryMaterial.areas face p) :=
  ⟨boundaryRuntime_sourceCertificate.1, boundaryRuntime_sourceCertificate.2.actualTangents,
    boundaryRuntime_sourceCertificate.2.actualArea, boundaryRuntime_sourceCertificate.2.nonzeroArea,
    boundaryRuntime_sourceCertificate.2.gradientFlux⟩

theorem boundaryRuntime_gradient_flux :
    type_of% (boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate)) ∧
    generatedBoundaryMaterial.totalFlux = generatedBoundaryMaterial.parent.integral ∧
    generatedBoundaryMaterial.totalFlux = ∑ q : Quarter, generatedBoundaryMaterial.quarterFluxes q ∧
    ((-623 / 10000000000 : ℝ) < generatedBoundaryMaterial.totalFlux ∧
      generatedBoundaryMaterial.totalFlux < (-39 / 10000000000 : ℝ)) ∧
    (∃ face : Face, generatedBoundaryMaterial.faceIntegrals face < 0) :=
  ⟨boundaryRuntime_sourceCertificate.1, boundaryRuntime_sourceCertificate.2.spatialIntegral,
    boundaryRuntime_sourceCertificate.2.quarterSum, boundaryRuntime_sourceCertificate.2.strict,
    boundaryRuntime_sourceCertificate.2.negativeFace⟩

theorem boundaryRuntime_quarter_and_seams :
    type_of% (boundaryRuntimeFace_factorizes boundaryRuntimeSeed (.component .certificate)) ∧
    (∀ q : Quarter, generatedBoundaryMaterial.quarterFluxes q = generatedBoundaryMaterial.parent.quarterIntegrals q) ∧
    type_of% all_three_seams_cancel :=
  ⟨boundaryRuntime_sourceCertificate.1, boundaryRuntime_sourceCertificate.2.quarterIntegrals,
    boundaryRuntime_sourceCertificate.2.seamCancellation⟩

end
end LAlanine40K2025.BasinRefinement.BoundaryRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
