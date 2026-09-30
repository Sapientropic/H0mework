import H0mework.Fock.HistoryConditional.InventoryBirth

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalInventory

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem mean_original (runtime : LivingRuntimeState process) (depth : Nat) (value : Field parity)
    (supported : value ∈ ((historyPMF (inventoryBound runtime)).map (observation (inventoryBound runtime) depth)).support) :
    SourceVectorMoment.mean (conditional (inventoryBound runtime) depth value supported) (values (inventoryBound runtime)) =
      SourceConditionalVector.realizeModel runtime
        (SourceConditionalVector.estimate runtime (SourceConditionalModel.dynamicRead runtime depth) value
          (by simpa only [observation_original] using supported)) := by
  have paid := SourceConditionalVector.mean_source runtime (observation (inventoryBound runtime) depth) value supported
  apply Eq.trans ?_ paid.symm
  apply congrArg (SourceVectorMoment.mean (conditional (inventoryBound runtime) depth value supported))
  funext i
  exact (SourceConditionalVector.actor_material runtime i).symm

def recoveryError (bound depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) : ℝ :=
  ∑ i, (historyPMF bound i).toReal * ‖values bound i - decoder (observation bound depth i)‖ ^ 2

theorem recovery_error_original (runtime : LivingRuntimeState process) (depth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) :
    recoveryError (inventoryBound runtime) depth decoder = SourceConditionalVector.dynamicError runtime depth decoder := by
  simp only [recoveryError, SourceConditionalVector.dynamicError, values_original, observation_original]

theorem runtime_bound (bound : Nat) : inventoryBound (runtimeAt bound) = bound := by
  rw [inventory_bound, runtimeAt_state]

theorem recovery_error_at (bound depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    recoveryError bound depth decoder = SourceConditionalVector.dynamicError (runtimeAt bound) depth decoder := by
  have paid := recovery_error_original (runtimeAt bound) depth decoder
  rw [runtime_bound] at paid
  exact paid

theorem recovery_error_append (bound depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    ((bound + 2 : Nat) : ℝ) * recoveryError (bound + 1) depth decoder =
      ((bound + 1 : Nat) : ℝ) * recoveryError bound depth decoder +
        ‖born bound - decoder (bornObservation bound depth)‖ ^ 2 := by
  change ((bound + 1 + 1 : Nat) : ℝ) * recoveryError (bound + 1) depth decoder = _
  rw [recoveryError, recoveryError, sum_count, sum_count, Fin.sum_univ_castSucc]
  simp only [values_retained, observation_retained, born, bornObservation]

theorem original_error_append (bound depth : Nat) (decoder : Field parity → SourceJointClockGraph.Carrier) :
    ((bound + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError (runtimeAt (bound + 1)) depth decoder =
      ((bound + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicError (runtimeAt bound) depth decoder +
        ‖born bound - decoder (bornObservation bound depth)‖ ^ 2 := by
  rw [← recovery_error_at, ← recovery_error_at, recovery_error_append]

theorem minimum_append (bound depth : Nat) :
    let decoder := SourceConditionalVector.vectorDecoder (runtimeAt (bound + 1)) (SourceConditionalModel.dynamicRead (runtimeAt (bound + 1)) depth)
    ((bound + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt (bound + 1)) depth =
      ((bound + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicError (runtimeAt bound) depth decoder +
        ‖born bound - decoder (bornObservation bound depth)‖ ^ 2 := by
  dsimp only
  have paid := original_error_append bound depth
    (SourceConditionalVector.vectorDecoder (runtimeAt (bound + 1)) (SourceConditionalModel.dynamicRead (runtimeAt (bound + 1)) depth))
  rw [SourceConditionalVector.dynamic_attains] at paid
  exact paid

theorem total_minimum_nondecreasing (bound depth : Nat) :
    ((bound + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt bound) depth ≤
      ((bound + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance (runtimeAt (bound + 1)) depth := by
  rw [minimum_append]
  exact (mul_le_mul_of_nonneg_left (SourceConditionalVector.dynamic_optimal (runtimeAt bound) depth _)
    (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right (sq_nonneg _))

theorem next_runtime (runtime : LivingRuntimeState process) :
    runtimeAt (inventoryBound runtime + 1) = runtime.tick.next := by
  have paid := congrArg (fun source : LivingRuntimeState process => source.tick.next) (SourceConditionalModel.original_runtime runtime)
  exact paid

theorem born_current (runtime : LivingRuntimeState process) :
    born (inventoryBound runtime) = SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next := by
  rw [born_material, next_runtime]

theorem current_error_append (runtime : LivingRuntimeState process) (depth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) :
    ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime.tick.next depth decoder =
      ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicError runtime depth decoder +
        ‖SourceCopyNativeModelStep.sourceValue runtime.tick.next.tick.next -
          decoder (bornObservation (inventoryBound runtime) depth)‖ ^ 2 := by
  have paid := original_error_append (inventoryBound runtime) depth decoder
  rw [next_runtime runtime, SourceConditionalModel.original_runtime runtime, born_current] at paid
  exact paid

theorem current_total_minimum (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 1 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime depth ≤
      ((inventoryBound runtime + 2 : Nat) : ℝ) * SourceConditionalVector.dynamicVariance runtime.tick.next depth := by
  have paid := total_minimum_nondecreasing (inventoryBound runtime) depth
  rw [next_runtime runtime, SourceConditionalModel.original_runtime runtime] at paid
  exact paid

end
end SourceConditionalInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
