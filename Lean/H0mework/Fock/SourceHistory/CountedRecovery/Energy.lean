import H0mework.Fock.SourceHistory.CountedObservation.Field

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCountedRecovery

open SourceGeneratedAcquisitionContinuation
open SourceConditionalModel (Actors)
open SourceRetainedReceiver (At next value residual)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
variable {Key : Type*} [DecidableEq Key]

def error (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key) : ℝ :=
  ∑ actor : Actors runtime, ‖SourceConditionalInventory.values (inventoryBound runtime) actor -
    value runtime frame (read actor.val)‖ ^ 2

def residualMass (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key) : ℝ :=
  ∑ actor : Actors runtime, ‖residual runtime frame (read actor.val)‖ ^ 2

theorem decomposition (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    error runtime frame read = SourceConditionalNativeBirth.total runtime read + residualMass runtime frame read := by
  rw [error, SourceConditionalNativeBirth.total_decomposition, residualMass]
  apply congrArg (fun amount : ℝ => SourceConditionalNativeBirth.total runtime read + amount)
  apply Finset.sum_congr rfl
  intro actor _
  rw [SourceRetainedReceiver.residual, SourceRetainedReceiver.model_source runtime frame read _ source]
  exact congrArg (fun x : ℝ => x ^ 2) (norm_sub_rev _ _)

omit [DecidableEq Key] in
private theorem sum_append (runtime : LivingRuntimeState process) (read : Nat → Key) (cost : Key → ℝ) :
    (∑ actor : Actors runtime.tick.next, cost (read actor.val)) =
      (∑ actor : Actors runtime, cost (read actor.val)) + cost (read (inventoryBound runtime + 1)) := by
  change (∑ actor : Fin (inventoryBound runtime.tick.next + 1), cost (read actor.val)) = _
  rw [SourceActualImageStep.next_bound, Fin.sum_univ_castSucc]
  rfl

private theorem remaining_energy (count : Nat) (energy : ℝ) :
    (count : ℝ) * (((SourceStableReceivedCount.contraction count : ℝ) ^ 2 - 1) * energy) +
      (energy + ((SourceStableReceivedCount.contraction count : ℝ) ^ 2 - 1) * energy) =
        -((count : ℝ) / (count + 1) * energy) := by
  dsimp only [SourceStableReceivedCount.contraction]
  push_cast
  have nonzero : (count : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem residual_mass_next (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    residualMass runtime.tick.next (next runtime frame (read runtime.tick.next.state)) read =
      residualMass runtime frame read -
        ((frame.native (read runtime.tick.next.state)).1 : ℝ) /
          ((frame.native (read runtime.tick.next.state)).1 + 1) *
            ‖residual runtime frame (read runtime.tick.next.state)‖ ^ 2 := by
  let bornKey := read runtime.tick.next.state
  let count := (frame.native bornKey).1
  let factor := (SourceStableReceivedCount.contraction count : ℝ)
  let energy := fun key : Key => ‖residual runtime frame key‖ ^ 2
  have receipt : read (inventoryBound runtime + 1) = bornKey :=
    (congrArg read ((inventory_bound runtime.tick.next).symm.trans (SourceActualImageStep.next_bound runtime))).symm
  have count_sum : (count : ℝ) = ∑ actor : Actors runtime, if read actor.val = bornKey then 1 else 0 := by
    have actual := congrArg (fun amount : Nat => (amount : ℝ))
      (SourceConditionalNativePosterior.count_sum read (inventoryBound runtime) bornKey)
    push_cast at actual
    simpa only [count, source] using actual
  have action (key : Key) :
      ‖residual runtime.tick.next (next runtime frame (read runtime.tick.next.state)) key‖ ^ 2 =
        energy key + if key = bornKey then (factor ^ 2 - 1) * energy bornKey else 0 := by
    rw [SourceRetainedReceiver.residual_energy runtime frame read key source]
    by_cases selected : key = bornKey
    · subst key
      simp only [bornKey, energy, factor, count, ↓reduceIte]
      ring
    · simp only [show key ≠ read runtime.tick.next.state from selected, if_neg selected, add_zero]
      rfl
  have selected_sum :
      (∑ actor : Actors runtime, if read actor.val = bornKey then (factor ^ 2 - 1) * energy bornKey else 0) =
        (count : ℝ) * ((factor ^ 2 - 1) * energy bornKey) := by
    rw [count_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro actor _
    split_ifs <;> simp
  rw [residualMass, sum_append runtime read
    (fun key => ‖residual runtime.tick.next (next runtime frame (read runtime.tick.next.state)) key‖ ^ 2), receipt]
  simp_rw [action]
  rw [Finset.sum_add_distrib, selected_sum]
  simp only [↓reduceIte]
  rw [add_assoc, remaining_energy count (energy bornKey), ← sub_eq_add_neg]
  dsimp only [residualMass, energy, count, bornKey]

theorem error_update (runtime : LivingRuntimeState process) (frame : At runtime Key) (read : Nat → Key)
    (source : frame.native = SourceConditionalNativeObservers.generate read (inventoryBound runtime)) :
    error runtime.tick.next (next runtime frame (read runtime.tick.next.state)) read =
      error runtime frame read + SourceConditionalNativeBirth.innovation runtime read -
        ((frame.native (read runtime.tick.next.state)).1 : ℝ) /
          ((frame.native (read runtime.tick.next.state)).1 + 1) *
            ‖residual runtime frame (read runtime.tick.next.state)‖ ^ 2 := by
  rw [decomposition runtime.tick.next _ read (SourceRetainedReceiver.next_native runtime frame read source),
    decomposition runtime frame read source, SourceConditionalNativeBirth.minimum_update,
    residual_mass_next runtime frame read source]
  ring

end
end SourceCountedRecovery
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
