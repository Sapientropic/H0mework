import H0mework.Versions.R9c73a630.Chemistry.LAlanineRefinementRuntime.RefinementRuntime

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open scoped Matrix Matrix.Norms.L2Operator
open scoped Topology Interval
noncomputable section

theorem refinementRuntime_response (runtime : LivingRuntimeState refinementRuntimeProcess) :
    Reentry.Runtime.reentryResponse runtime.state.current = refinementParentResult := by
  have keeps : ∀ {state : refinementRuntimeProcess.State}, SourceNativeRuntimeReachableAt refinementRuntimeProcess state →
      Reentry.Runtime.reentryResponse state.current = refinementParentResult := by
    intro state reachable
    induction reachable with
    | initial => rfl
    | step prior kept => exact kept
  exact keeps runtime.reachable

theorem refinementRead_commutes_with_physicalOccurrence (runtime : LivingRuntimeState refinementRuntimeProcess) :
    generatedRefinementMaterial.parent.parent.parent.physical.nuclear.target =
      Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    generatedRefinementMaterial.parent.parent.parent.physical.realized =
      (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    generatedRefinementMaterial.parent.parent.parent.physical.clock =
      Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    generatedRefinementMaterial.parent.parent.parent.physical.nuclear.targetLedger =
      Reentry.Runtime.reentryCurrentLedger runtime.tick.next.state.current := by
  change refinementParentResult.nuclear.target = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.target ∧
    refinementParentResult.realized = (Reentry.Runtime.reentryResponse runtime.state.current).realized ∧
    refinementParentResult.clock = (Reentry.Runtime.reentryResponse runtime.state.current).clock ∧
    refinementParentResult.nuclear.targetLedger = (Reentry.Runtime.reentryResponse runtime.state.current).nuclear.targetLedger
  rw [refinementRuntime_response]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem refinementRuntime_parent_material_installed (runtime : LivingRuntimeState refinementRuntimeProcess) :
    type_of% (refinementRuntimeFace_factorizes runtime (.inherited (.component .material))) ∧
    refinementRuntimeFacade.readoutAt runtime (.inherited (.component .material)) =
      (.inl ⟨PUnit.unit, (BasinPartition.Runtime.BasinLedger.ledgerCompiler.compile runtime.emittedOccurrence,
        generatedRefinementMaterial.parent)⟩ :
        SourceNativeProjectionFiberAt RefinementBase.projectionLaw (.component .material) runtime.emittedOccurrence) :=
  ⟨refinementRuntimeFace_factorizes runtime (.inherited (.component .material)), rfl⟩

theorem refinementRuntime_clock_preserved (runtime : LivingRuntimeState refinementRuntimeProcess) :
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 3 * Propagation.Producer.nativeClockStep := by
  change (Reentry.Runtime.reentryResponse runtime.state.current).clock = _
  rw [refinementRuntime_response]
  exact refinementParent_clock

theorem refinementRuntime_full_state_and_error :
    generatedRefinementMaterial.parent.parent.parent.physical.realized = Reentry.Source.targetRealized ∧
    generatedRefinementMaterial.parent.parent.parent.physical.realized =
      generatedRefinementMaterial.parent.parent.parent.physical.held +
      generatedRefinementMaterial.parent.parent.parent.physical.inheritedResidual +
      generatedRefinementMaterial.parent.parent.parent.physical.newNumericalResidual ∧
    ‖generatedRefinementMaterial.parent.parent.parent.physical.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  ⟨rfl, refinementParent_error_and_memory⟩

theorem refinementRuntime_parent_account_preserved :
    generatedRefinementMaterial.parent = BasinPartition.Runtime.generatedBasinMaterial := rfl

theorem refinementRuntime_actual_geometry :
    generatedRefinementMaterial.geometry = Geometry.Source.runs ∧
    generatedRefinementMaterial.centre = Geometry.Source.center ∧
    generatedRefinementMaterial.lowerBracket = Geometry.Source.lower ∧
    generatedRefinementMaterial.upperBracket = Geometry.Source.upper :=
  ⟨rfl, continuousField_same_geometry, rfl, rfl⟩

theorem refinementRuntime_continuous_refinement :
    type_of% (refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate)) ∧
    SourceLaplaceProducer.sourceLaplaceClosure :=
  ⟨refinementRuntime_sourceCertificate.1, refinementRuntime_sourceCertificate.2.2.1⟩

theorem refinementRuntime_signed_geometry :
    type_of% (refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate)) ∧
    Geometry.refinementClosure :=
  ⟨refinementRuntime_sourceCertificate.1, refinementRuntime_sourceCertificate.2.1⟩

theorem refinementRuntime_density_laplacian_exact :
    type_of% (refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate)) ∧
    type_of% (SourceGaussianModel.density_laplacian_exact SourceFiniteData.sourceTerms SourceFiniteData.densityMatrix) :=
  ⟨refinementRuntime_sourceCertificate.1, refinementRuntime_sourceCertificate.2.2.2.2⟩

theorem refinementRuntime_integral_convergence (point : SourceGaussianModel.Point) (axis : Fin 3)
    (transverse : SourceLaplaceProducer.TransverseInside point axis) :
    type_of% (refinementRuntimeFace_factorizes refinementRuntimeSeed (.component .certificate)) ∧
    Filter.Tendsto
      (fun n : Nat => trapezoidal_integral
        (fun t => generatedRefinementMaterial.laplacian (Function.update point axis t)) n
        (SourceLaplaceProducer.lower axis) (SourceLaplaceProducer.upper axis)) Filter.atTop
      (𝓝 (∫ t in SourceLaplaceProducer.lower axis..SourceLaplaceProducer.upper axis,
        generatedRefinementMaterial.laplacian (Function.update point axis t))) := by
  have source := refinementRuntime_continuous_refinement.2
  exact ⟨refinementRuntime_continuous_refinement.1, source.2.2.2.2.2.2 point axis transverse⟩

theorem refinementRuntime_no_extra_MD (runtime : LivingRuntimeState refinementRuntimeProcess) :
    Reentry.Runtime.reentryFrame runtime.tick.next.tick.next.state.current =
      Reentry.Runtime.reentryFrame runtime.tick.next.state.current ∧
    Reentry.Runtime.reentryPhysicalTime runtime.tick.next.tick.next.state.current =
      Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current ∧
    IsEmpty (Reentry.Runtime.ReentryV.NativeWriteAt runtime.tick.next.state.current) :=
  ⟨rfl, rfl, ⟨fun write => nomatch write⟩⟩

end
end LAlanine40K2025.BasinRefinement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
