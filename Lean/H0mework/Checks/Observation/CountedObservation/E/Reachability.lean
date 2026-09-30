import H0mework.Fock.SourceHistory.CountedObservation.Material

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CountedSourceReachabilityControl

open SourceGeneratedAcquisitionContinuation
open SourceCopyCurrentCoordinates (maximumIndex)
open SourceConditionalNativeObservers (clockRead)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def actualKeys (runtime : LivingRuntimeState process) : List (ℤ × ℤ) :=
  (List.finRange (inventoryBound runtime + 1)).map (fun actor => clockRead 0 actor.val)

theorem actual_inventory (runtime : LivingRuntimeState process) :
    (actualKeys runtime).toFinset = SourceUniformFibreVariance.outputs (inventoryBound runtime)
      (fun actor => clockRead 0 actor.val) := by
  ext key
  simp [actualKeys, SourceUniformFibreVariance.outputs]

def exactSamples (runtime : LivingRuntimeState process) :
    {key // key ∈ SourceUniformFibreVariance.outputs (inventoryBound runtime) (fun actor => clockRead 0 actor.val)} →
      SourceRationalWindowReadout.Samples (inventoryBound runtime) ((maximumIndex runtime).val + 1) :=
  fun key phase => SourceFiniteObserverCalculation.posteriorCalculate
    (inventoryBound runtime) ((maximumIndex runtime).val + 1) 0 phase.val (clockRead 0) key.val

theorem exact_budgets (runtime : LivingRuntimeState process) (nonunit : (maximumIndex runtime).val ≠ 0) :
    ∀ key, SourceWindowPrecision.gain runtime (maximumIndex runtime) nonunit 0 *
      SourceWindowPrecision.sampleEnergy runtime (maximumIndex runtime)
        (SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (exactSamples runtime key) -
          SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
            (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val)) <
      SourcePosteriorStability.threshold runtime ^ 2 := by
  intro key
  have same : SourceRationalWindowReadout.embed runtime (maximumIndex runtime) 0 (exactSamples runtime key) =
      SourceCopyTemporalBoundary.recordedPrefix runtime (maximumIndex runtime) 0 ((maximumIndex runtime).val + 1)
        (SourceConditionalNativePosterior.decoder runtime (clockRead 0) key.val) :=
    SourceRationalWindowReadout.posterior_samples runtime (maximumIndex runtime) 0 (clockRead 0) key.val
  rw [same, sub_self]
  simp only [SourceWindowPrecision.sampleEnergy, Pi.zero_apply, norm_zero,
    zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  exact sq_pos_of_pos (SourcePosteriorStability.threshold_positive runtime)

theorem actual_nonunit : (maximumIndex (runtimeAt 3)).val ≠ 0 := by
  rw [SourceCopyCurrentCoordinates.maximum_index_val, inventory_bound, runtimeAt_state]
  decide

def initial : SourceRetainedReceiver.At (runtimeAt 3) (ℤ × ℤ) :=
  SourceRetainedReceiver.start (inventoryBound (runtimeAt 3)) (maximumIndex (runtimeAt 3)).val actual_nonunit
    (SourceUniformFibreVariance.outputs (inventoryBound (runtimeAt 3)) (fun actor => clockRead 0 actor.val))
    (exactSamples (runtimeAt 3))

theorem initial_inventory_nonempty : (actualKeys (runtimeAt 3)).toFinset.Nonempty := by
  rw [actual_inventory]
  refine ⟨clockRead 0 0, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨0, Nat.zero_lt_succ _⟩, Finset.mem_univ _, rfl⟩

theorem received_at_every_step (steps : Nat) :
    SourceCountedObservation.Simulates (inventoryBound ((runtimeAt 3).advance steps))
      (maximumIndex ((runtimeAt 3).advance steps)).val
      (SourceCountedObservation.run (inventoryBound (runtimeAt 3))
        (fun offset => clockRead 0 (inventoryBound (runtimeAt 3) + offset + 1))
        (SourceCountedObservation.fromInventory (inventoryBound (runtimeAt 3))
          (maximumIndex (runtimeAt 3)).val (actualKeys (runtimeAt 3)) initial) steps)
      (SourceRetainedReceiver.trajectory (runtimeAt 3) initial
        (fun offset => clockRead 0 (inventoryBound (runtimeAt 3) + offset + 1)) steps) :=
  SourceCountedObservation.received_simulates (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps

theorem posterior_at_every_step (steps : Nat) (key : ℤ × ℤ) :
    type_of% (SourceCountedPosterior.continued_source (runtimeAt 3) actual_nonunit (clockRead 0)
      (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
      (exact_budgets (runtimeAt 3) actual_nonunit) steps key) :=
  SourceCountedPosterior.continued_source (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps key

theorem autonomous_next_at_every_step (steps : Nat) :
    type_of% (SourceCountedAdvance.continued_next (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps) :=
  SourceCountedAdvance.continued_next (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps

#print axioms autonomous_next_at_every_step

theorem autonomous_model_at_every_step (steps : Nat) (key : ℤ × ℤ) :
    type_of% (SourceCountedAdvance.continued_model (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps key) :=
  SourceCountedAdvance.continued_model (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps key

#print axioms autonomous_model_at_every_step

theorem autonomous_field_at_every_step (steps depth : Nat) :
    type_of% (SourceCountedAdvance.continued_next_field (runtimeAt 3) actual_nonunit
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps depth) :=
  SourceCountedAdvance.continued_next_field (runtimeAt 3) actual_nonunit
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps depth

#print axioms autonomous_field_at_every_step

theorem coarse_posterior_at_every_step (steps : Nat) (key : ZMod 2) :
    type_of% (SourceCountedMerge.continued_source (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) SourceConditionalNativeMerge.forgetClock steps key) :=
  SourceCountedMerge.continued_source (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) SourceConditionalNativeMerge.forgetClock steps key

#print axioms coarse_posterior_at_every_step

theorem coarse_next_model_at_every_step (steps : Nat) (key : ZMod 2) :
    type_of% (SourceCountedMerge.continued_next_model (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) SourceConditionalNativeMerge.forgetClock steps key) :=
  SourceCountedMerge.continued_next_model (runtimeAt 3) actual_nonunit (clockRead 0)
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) SourceConditionalNativeMerge.forgetClock steps key

#print axioms coarse_next_model_at_every_step

theorem coarse_original_field_at_every_step (steps depth : Nat) :
    type_of% (SourceCountedMerge.continued_next_field (runtimeAt 3) actual_nonunit
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps depth) :=
  SourceCountedMerge.continued_next_field (runtimeAt 3) actual_nonunit
    (actualKeys (runtimeAt 3)) (actual_inventory (runtimeAt 3)) (exactSamples (runtimeAt 3))
    (exact_budgets (runtimeAt 3) actual_nonunit) steps depth

#print axioms coarse_original_field_at_every_step

#print axioms posterior_at_every_step

#print axioms actual_inventory
#print axioms exact_budgets
#print axioms actual_nonunit
#print axioms initial_inventory_nonempty
#print axioms received_at_every_step

end
end CountedSourceReachabilityControl
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
