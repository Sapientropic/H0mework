import H0mework.Chemistry.LAlanineRuntime.Consumers

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.ContinuousRuntime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

def bandRuntimeAfterSecond := bandRuntimeAfterFirst.tick.next
def bandRuntimeAfterThird := bandRuntimeAfterSecond.tick.next

theorem bandRuntime_physical_state_not_erased :
    ∃ i j, (generatedContinuousBandMaterial.parent.parent.parent.parent.physical.realized i j).im ≠ 0 :=
  Runtime.refinementRuntime_physical_state_not_erased

theorem bandRuntime_no_fourth_clock :
    ¬∃ runtime : LivingRuntimeState bandRuntimeProcess,
      Reentry.Runtime.reentryPhysicalTime runtime.tick.next.state.current = 4 * Propagation.Producer.nativeClockStep := by
  rintro ⟨runtime, advanced⟩
  rw [bandRuntime_clock_preserved] at advanced
  have positive := Propagation.Producer.nativeClockStep_positive
  linarith

theorem bandRuntime_same_actual_next :
    bandRuntimeAfterFirst.current.visit = Reentry.Runtime.generatedReentryAction.target.targetVisit := rfl

theorem bandRuntime_no_mixed_band_erasure (run : Geometry.Data.RunIndex) :
    ¬∃ atom : Geometry.Data.Bucket, ∀ other : Geometry.Data.Bucket, other ≠ atom →
      (Geometry.Source.domain run 1).counts[other.val]! = 0 := Runtime.refinementRuntime_no_mixed_band_erasure run

theorem bandRuntime_actual_positive_consumer :
    type_of% (bandRuntimeFace_factorizes bandRuntimeSeed (.component .certificate)) ∧
    ∃ point : SourceGaussianModel.Point,
      SourceSignedEvaluator.InRectangle generatedContinuousBandMaterial.firstRectangle point ∧
      generatedContinuousBandMaterial.gradient point ≠ 0 ∧
      generatedContinuousBandMaterial.parent.laplacian point < (-16 / 100 : ℝ) := by
  have inside := SourceSignedMatrix.sourceWitness_in_rectangle
  exact ⟨bandRuntime_actual_first_field.1, SourceSignedMatrix.sourceWitness, inside,
    (bandRuntime_first_field_nonzero_negative _ inside).2⟩

theorem bandRuntime_zero_gradient_rejected :
    ¬ (∀ point, SourceSignedEvaluator.InRectangle generatedContinuousBandMaterial.firstRectangle point →
      generatedContinuousBandMaterial.gradient point = 0) := SourceSignedMatrix.zeroed_response_rejected

theorem bandRuntime_three_clocks :
    Reentry.Runtime.reentryPhysicalTime bandRuntimeAfterFirst.state.current = 3 * Propagation.Producer.nativeClockStep ∧
    Reentry.Runtime.reentryPhysicalTime bandRuntimeAfterSecond.state.current = 3 * Propagation.Producer.nativeClockStep ∧
    Reentry.Runtime.reentryPhysicalTime bandRuntimeAfterThird.state.current = 3 * Propagation.Producer.nativeClockStep :=
  ⟨bandRuntime_clock_preserved bandRuntimeSeed, bandRuntime_clock_preserved bandRuntimeAfterFirst,
    bandRuntime_clock_preserved bandRuntimeAfterSecond⟩

theorem bandRuntime_three_frames :
    Reentry.Runtime.reentryFrame bandRuntimeAfterFirst.state.current = Reentry.Source.stepReadout.nuclear.target ∧
    Reentry.Runtime.reentryFrame bandRuntimeAfterSecond.state.current = Reentry.Source.stepReadout.nuclear.target ∧
    Reentry.Runtime.reentryFrame bandRuntimeAfterThird.state.current = Reentry.Source.stepReadout.nuclear.target := ⟨rfl, rfl, rfl⟩

theorem bandRuntime_three_readouts (face : ContinuousBandFace) :
    type_of% (bandRuntimeFace_factorizes bandRuntimeSeed face) ∧
    type_of% (bandRuntimeFace_factorizes bandRuntimeAfterFirst face) ∧
    type_of% (bandRuntimeFace_factorizes bandRuntimeAfterSecond face) :=
  ⟨bandRuntimeFace_factorizes bandRuntimeSeed face, bandRuntimeFace_factorizes bandRuntimeAfterFirst face,
    bandRuntimeFace_factorizes bandRuntimeAfterSecond face⟩

theorem bandRuntime_run0_source_epsilon :
    Geometry.Source.epsilon 0 = (7378697629483821 / 73786976294838206464 : ℚ) ∧
    0 < Geometry.Source.epsilon 0 := by decide +kernel

theorem sourceGeneratedPhysicalContinuousBandNext :
    type_of% bandRuntime_sourceCertificate ∧ type_of% bandParent_installed ∧ type_of% bandParent_actual ∧
    type_of% band_source_and_law_unchanged ∧ type_of% bandRuntime_seed_same_occurrence ∧
    type_of% bandRuntime_afterFirst_same_visit ∧ type_of% bandRuntime_same_actual_next ∧
    type_of% bandRuntime_full_state_and_error ∧ type_of% bandRuntime_complete_parent_preserved ∧
    type_of% bandRuntime_density_gradient_same_source ∧ type_of% bandRuntime_true_flow ∧
    type_of% bandRuntime_actual_band_flow ∧ type_of% bandRuntime_whole_initial_jet ∧
    type_of% bandRuntime_actual_first_field ∧ type_of% bandRuntime_first_field_nonzero_negative ∧
    type_of% bandRuntime_complete_source_receipt ∧ type_of% bandRuntime_remaining_fields_exact ∧
    type_of% bandRuntime_physical_state_not_erased ∧ type_of% bandRuntime_no_fourth_clock ∧
    type_of% bandRuntime_no_mixed_band_erasure ∧ type_of% bandRuntime_actual_positive_consumer ∧
    type_of% bandRuntime_zero_gradient_rejected ∧ type_of% bandRuntime_three_clocks ∧
    type_of% bandRuntime_three_frames ∧ type_of% bandRuntime_three_readouts ∧
    type_of% bandRuntime_run0_source_epsilon ∧ type_of% bandFace_at_index ∧ type_of% bandFace_index_at ∧
    (∀ current, type_of% (band_rootCompiler_unchanged current)) ∧
    (∀ runtime, type_of% (bandRuntime_generated_same_next runtime)) ∧
    (∀ runtime face, type_of% (bandRuntimeFace_factorizes runtime face)) ∧
    (∀ runtime, type_of% (bandRuntime_material_installed runtime)) ∧
    (∀ runtime face, type_of% (bandRuntime_original_twenty_faces runtime face)) ∧
    (∀ runtime, type_of% (bandRead_commutes_with_physicalOccurrence runtime)) ∧
    (∀ runtime, type_of% (bandRuntime_parent_material_installed runtime)) ∧
    (∀ runtime, type_of% (bandRuntime_clock_preserved runtime)) ∧
    (∀ runtime, type_of% (bandRuntime_no_extra_MD runtime)) ∧
    (∀ runtime, type_of% (bandRuntime_wholeLedger_same_occurrence runtime)) :=
  ⟨bandRuntime_sourceCertificate, bandParent_installed, bandParent_actual, band_source_and_law_unchanged,
    bandRuntime_seed_same_occurrence, bandRuntime_afterFirst_same_visit, bandRuntime_same_actual_next,
    bandRuntime_full_state_and_error, bandRuntime_complete_parent_preserved, bandRuntime_density_gradient_same_source,
    bandRuntime_true_flow, bandRuntime_actual_band_flow, bandRuntime_whole_initial_jet, bandRuntime_actual_first_field,
    bandRuntime_first_field_nonzero_negative, bandRuntime_complete_source_receipt, bandRuntime_remaining_fields_exact,
    bandRuntime_physical_state_not_erased, bandRuntime_no_fourth_clock, bandRuntime_no_mixed_band_erasure,
    bandRuntime_actual_positive_consumer, bandRuntime_zero_gradient_rejected, bandRuntime_three_clocks,
    bandRuntime_three_frames, bandRuntime_three_readouts, bandRuntime_run0_source_epsilon, bandFace_at_index,
    bandFace_index_at, band_rootCompiler_unchanged, bandRuntime_generated_same_next, bandRuntimeFace_factorizes,
    bandRuntime_material_installed, bandRuntime_original_twenty_faces, bandRead_commutes_with_physicalOccurrence,
    bandRuntime_parent_material_installed, bandRuntime_clock_preserved, bandRuntime_no_extra_MD,
    bandRuntime_wholeLedger_same_occurrence⟩

end
end LAlanine40K2025.BasinRefinement.ContinuousRuntime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
