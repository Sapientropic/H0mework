import H0mework.Chemistry.LAlanineRefinementRuntime.Consumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

theorem refinementRuntime_physical_state_not_erased :
    ∃ i j, (generatedRefinementMaterial.parent.parent.parent.physical.realized i j).im ≠ 0 :=
  BasinPartition.Runtime.basinRuntime_physical_state_not_erased

theorem refinementRuntime_no_fourth_clock :
    ¬∃ runtime : LivingRuntimeState refinementRuntimeProcess,
      Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 4 * Propagation.Producer.nativeClockStep := by
  rintro ⟨runtime, advanced⟩
  rw [refinementRuntime_clock_preserved] at advanced
  have positive := Propagation.Producer.nativeClockStep_positive
  linarith

theorem refinementRuntime_wholeLedger_same_occurrence (runtime : LivingRuntimeState refinementRuntimeProcess) :
    runtime.tick.generated.wholeLedgerWriteBack =
      Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.state.current := rfl

theorem refinementRuntime_same_actual_next :
    refinementRuntimeAfterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

theorem refinementRuntime_no_mixed_band_erasure (r : Geometry.Data.RunIndex) :
    ¬∃ atom : Geometry.Data.Bucket, ∀ other : Geometry.Data.Bucket, other ≠ atom →
      (Geometry.Source.domain r 1).counts[other.val]! = 0 :=
  Geometry.Incidence.mixedBand_cannotBeUnanimous r

theorem refinementRuntime_no_zero_error_premise (axis : Fin 3) (panels : Nat) (positive : 0 < panels) :
    0 < SourceLaplaceProducer.errorBudget axis panels ∧
    SourceLaplaceProducer.errorBudget axis (2 * panels) < SourceLaplaceProducer.errorBudget axis panels :=
  ⟨SourceLaplaceProducer.errorBudget_positive axis panels positive,
    SourceLaplaceProducer.actual_doubling_strict axis panels positive⟩

theorem refinementRuntime_actual_slice_admitted (axis : Fin 3) :
    SourceLaplaceProducer.TransverseInside (fun j => (generatedRefinementMaterial.centre j : ℝ)) axis := by
  intro other _
  change |(SourceFiniteData.boxCentre other : ℝ) - (SourceFiniteData.boxCentre other : ℝ)| ≤
    (SourceFiniteData.boxRadius : ℝ)
  rw [sub_self, abs_zero]
  exact_mod_cast SourceFiniteChecks.radius_nonnegative

theorem sourceGeneratedPhysicalBasinRefinementNext :
    type_of% refinementRuntime_sourceCertificate ∧
    type_of% refinementParent_installed ∧ type_of% refinementParent_actual ∧
    type_of% continuousField_same_geometry ∧
    type_of% refinement_source_and_law_unchanged ∧
    type_of% refinementRuntime_seed_same_occurrence ∧ type_of% refinementRuntime_afterFirst_same_visit ∧
    type_of% refinementRuntime_same_actual_next ∧
    type_of% refinementRuntime_full_state_and_error ∧ type_of% refinementRuntime_parent_account_preserved ∧
    type_of% refinementRuntime_actual_geometry ∧ type_of% refinementRuntime_continuous_refinement ∧
    type_of% refinementRuntime_signed_geometry ∧ type_of% refinementRuntime_density_laplacian_exact ∧
    type_of% refinementRuntime_integral_convergence ∧
    type_of% refinementRuntime_physical_state_not_erased ∧ type_of% refinementRuntime_no_fourth_clock ∧
    type_of% refinementRuntime_no_mixed_band_erasure ∧ type_of% refinementRuntime_no_zero_error_premise ∧
    type_of% refinementRuntime_actual_slice_admitted ∧
    (∀ current, type_of% (refinement_rootCompiler_unchanged current)) ∧
    (∀ runtime, type_of% (refinementRuntime_generated_same_next runtime)) ∧
    (∀ runtime face, type_of% (refinementRuntimeFace_factorizes runtime face)) ∧
    (∀ runtime, type_of% (refinementRuntime_material_installed runtime)) ∧
    (∀ runtime face, type_of% (refinementRuntime_original_eighteen_faces runtime face)) ∧
    (∀ runtime, type_of% (refinementRead_commutes_with_physicalOccurrence runtime)) ∧
    (∀ runtime, type_of% (refinementRuntime_parent_material_installed runtime)) ∧
    (∀ runtime, type_of% (refinementRuntime_clock_preserved runtime)) ∧
    (∀ runtime, type_of% (refinementRuntime_no_extra_MD runtime)) ∧
    (∀ runtime, type_of% (refinementRuntime_wholeLedger_same_occurrence runtime)) :=
  ⟨refinementRuntime_sourceCertificate, refinementParent_installed, refinementParent_actual,
    continuousField_same_geometry, refinement_source_and_law_unchanged,
    refinementRuntime_seed_same_occurrence, refinementRuntime_afterFirst_same_visit,
    refinementRuntime_same_actual_next, refinementRuntime_full_state_and_error,
    refinementRuntime_parent_account_preserved, refinementRuntime_actual_geometry,
    refinementRuntime_continuous_refinement, refinementRuntime_signed_geometry, refinementRuntime_density_laplacian_exact,
    refinementRuntime_integral_convergence, refinementRuntime_physical_state_not_erased,
    refinementRuntime_no_fourth_clock, refinementRuntime_no_mixed_band_erasure,
    refinementRuntime_no_zero_error_premise, refinementRuntime_actual_slice_admitted, refinement_rootCompiler_unchanged,
    refinementRuntime_generated_same_next, refinementRuntimeFace_factorizes,
    refinementRuntime_material_installed, refinementRuntime_original_eighteen_faces,
    refinementRead_commutes_with_physicalOccurrence, refinementRuntime_parent_material_installed,
    refinementRuntime_clock_preserved, refinementRuntime_no_extra_MD, refinementRuntime_wholeLedger_same_occurrence⟩

end
end LAlanine40K2025.BasinRefinement.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
