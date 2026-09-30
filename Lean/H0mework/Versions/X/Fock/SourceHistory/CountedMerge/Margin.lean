import H0mework.Versions.X.Fock.SourceHistory.CountedPosterior.Margin

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedMerge

open SourceRetainedReceiver (At residual)
open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Fine Coarse : Type*} [DecidableEq Fine] [DecidableEq Coarse]

private theorem merged_small (runtime : LivingRuntimeState process) (frame : At runtime Fine)
    (read : Nat → Fine) (forget : Fine → Coarse) (coarse : Coarse)
    (native : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime))
    (keys : frame.keys = SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val))
    (small : ∀ key, ‖residual runtime frame key‖ < SourcePosteriorStability.threshold runtime) :
    let merged := SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget
    ‖((merged.native coarse).1 : ℂ) • residual runtime merged coarse‖ < 1 / 2 := by
  dsimp only
  let merged : At runtime Coarse := SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget
  let count : Nat := (merged.native coarse).1
  have count_eq : SourceConditionalNativeMerge.inventoryCount frame.keys forget
      (inventoryBound runtime) frame.native coarse = count := rfl
  with_reducible change ‖(count : ℂ) • residual runtime merged coarse‖ < 1 / 2
  by_cases empty : count = 0
  · simp only [empty, Nat.cast_zero, zero_smul, norm_zero]
    norm_num
  have positive : 0 < ∑ key ∈ frame.keys, if forget key = coarse then (frame.native key).1 else 0 :=
    Nat.pos_of_ne_zero empty
  obtain ⟨witness, inside, witnessPositive⟩ := Finset.sum_pos_iff.mp positive
  have selected : forget witness = coarse := by
    by_contra different
    simp only [if_neg different, lt_self_iff_false] at witnessPositive
  have witnessCount : 0 < (frame.native witness).1 := by
    simpa only [if_pos selected] using witnessPositive
  have counted : (count : ℂ) • residual runtime merged coarse =
      ∑ key ∈ frame.keys, if forget key = coarse then
        ((frame.native key).1 : ℂ) • residual runtime frame key else 0 := by
    rw [SourceRetainedCoarsening.residual_merge, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro key _
    by_cases same : forget key = coarse
    · rw [SourceRetainedCoarsening.weight, if_pos same, if_pos same, smul_smul]
      congr 1
      simp only [Rat.cast_div, Rat.cast_natCast]
      rw [count_eq]
      have nonzero : (count : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr empty
      field_simp
    · simp only [SourceRetainedCoarsening.weight, if_neg same, Rat.cast_zero, zero_smul, smul_zero]
  have countSum : (count : ℝ) =
      ∑ key ∈ frame.keys, if forget key = coarse then ((frame.native key).1 : ℝ) else 0 := by
    change ((∑ key ∈ frame.keys, if forget key = coarse then (frame.native key).1 else 0 : Nat) : ℝ) = _
    push_cast
    rfl
  have count_le : count ≤ inventoryBound runtime + 1 := by
    change ((SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val frame forget).native coarse).1 ≤ _
    rw [SourceRetainedCoarsening.native_source _ _ frame read forget native keys,
      SourceConditionalNativePosterior.count_fibre]
    simpa only [Fintype.card_fin] using
      (Finset.card_le_univ (SourceUniformFibreVariance.fibre (inventoryBound runtime)
        (fun actor => (forget ∘ read) actor.val) coarse))
  calc
    ‖(count : ℂ) • residual runtime merged coarse‖ =
        ‖∑ key ∈ frame.keys, if forget key = coarse then
          ((frame.native key).1 : ℂ) • residual runtime frame key else 0‖ := congrArg norm counted
    _ ≤ ∑ key ∈ frame.keys, ‖if forget key = coarse then
          ((frame.native key).1 : ℂ) • residual runtime frame key else 0‖ := norm_sum_le _ _
    _ = ∑ key ∈ frame.keys, if forget key = coarse then
          ((frame.native key).1 : ℝ) * ‖residual runtime frame key‖ else 0 := by
      apply Finset.sum_congr rfl
      intro key _
      by_cases same : forget key = coarse <;>
        simp only [same, ↓reduceIte, norm_zero, norm_smul, Complex.norm_natCast]
    _ < ∑ key ∈ frame.keys, if forget key = coarse then
          ((frame.native key).1 : ℝ) * SourcePosteriorStability.threshold runtime else 0 := by
      apply Finset.sum_lt_sum
      · intro key _
        by_cases same : forget key = coarse
        · simp only [if_pos same]
          exact mul_le_mul_of_nonneg_left (small key).le (Nat.cast_nonneg _)
        · simp only [if_neg same, le_refl]
      · refine ⟨witness, inside, ?_⟩
        simp only [if_pos selected]
        exact mul_lt_mul_of_pos_left (small witness) (by exact_mod_cast witnessCount)
    _ = (count : ℝ) * SourcePosteriorStability.threshold runtime := by
      rw [countSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro key _
      split_ifs <;> simp only [zero_mul]
    _ ≤ (inventoryBound runtime + 1 : ℝ) * SourcePosteriorStability.threshold runtime :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast count_le)
        (SourcePosteriorStability.threshold_positive runtime).le
    _ = 1 / 2 := by
      rw [SourcePosteriorStability.threshold]
      have nonzero : (inventoryBound runtime + 1 : ℝ) ≠ 0 := by positivity
      field_simp

theorem initial_half_margin (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Fine)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (forget : Fine → Coarse) (coarse : Coarse) :
    let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    let merged : At runtime Coarse := SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val initial forget
    ‖((merged.native coarse).1 : ℂ) • residual runtime merged coarse‖ < 1 / 2 := by
  dsimp only
  let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  have native := SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  with_reducible apply merged_small runtime initial read forget coarse native rfl
  intro key
  have estimate := SourceRetainedReceiver.start_bound runtime nonunit read samples key budgets
  have strict := lt_of_le_of_lt estimate
    (SourceReceivedKeyInventory.extended_budgets runtime nonunit read samples budgets key)
  have squared : ‖residual runtime initial key‖ ^ 2 < SourcePosteriorStability.threshold runtime ^ 2 := by
    with_reducible exact strict
  have positive := SourcePosteriorStability.threshold_positive runtime
  nlinarith [norm_nonneg (residual runtime initial key)]

theorem trajectory_half_margin (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0)
    (read : Nat → Fine)
    (samples : {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1))
    (budgets : ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (samples key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime read key.val)) < SourcePosteriorStability.threshold runtime ^ 2)
    (forget : Fine → Coarse) (coarse : Coarse) (steps : Nat) :
    let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
      (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
    let current : At (runtime.advance steps) Fine := SourceRetainedReceiver.trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps
    let merged : At (runtime.advance steps) Coarse := SourceRetainedCoarsening.merge (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val current forget
    ‖((merged.native coarse).1 : ℂ) • residual (runtime.advance steps) merged coarse‖ < 1 / 2 := by
  dsimp only
  let initial : At runtime Fine := SourceRetainedReceiver.start (inventoryBound runtime) (maximumIndex runtime).val nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => read actor.val)) samples
  have native := SourceRetainedReceiver.start_native runtime nonunit read samples budgets
  have coarseNative := SourceRetainedCoarsening.native_source (inventoryBound runtime) (maximumIndex runtime).val
    initial read forget native rfl
  have initialSmall :
      ‖(((SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val initial forget).native coarse).1 : ℂ) •
        residual runtime (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val initial forget) coarse‖ < 1 / 2 := by
    with_reducible exact (initial_half_margin runtime nonunit read samples budgets forget coarse)
  let advanced : At (runtime.advance steps) Coarse := SourceRetainedReceiver.trajectory runtime
    (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val initial forget)
    (fun offset => forget (read (inventoryBound runtime + offset + 1))) steps
  have paid : ‖((advanced.native coarse).1 : ℂ) • residual (runtime.advance steps) advanced coarse‖ < 1 / 2 := by
    have carried := SourceCountedPosterior.trajectory_half_margin runtime
      (SourceRetainedCoarsening.merge (inventoryBound runtime) (maximumIndex runtime).val initial forget)
      (forget ∘ read) coarse coarseNative initialSmall steps
    simp only [Function.comp_apply] at carried
    with_reducible exact carried
  have same : SourceRetainedCoarsening.merge (inventoryBound (runtime.advance steps))
      (maximumIndex (runtime.advance steps)).val
      (SourceRetainedReceiver.trajectory runtime initial (fun offset => read (inventoryBound runtime + offset + 1)) steps)
      forget = advanced := by
    with_reducible exact (SourceRetainedCoarsening.merge_trajectory runtime initial read forget native rfl steps)
  with_reducible exact (congrArg (fun frame : At (runtime.advance steps) Coarse =>
    ‖((frame.native coarse).1 : ℂ) • residual (runtime.advance steps) frame coarse‖ < 1 / 2) same).mpr paid

end
end SourceCountedMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
