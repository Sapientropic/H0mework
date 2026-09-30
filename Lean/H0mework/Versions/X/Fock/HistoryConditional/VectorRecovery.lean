import H0mework.Versions.X.Fock.HistoryConditional.VectorLoss
import H0mework.Probability.Source.MomentAverage

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalVector

open SourceConditionalModel (Actors NextModel nextRead dynamicRead fullRead full_supported positive)
open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
open scoped Classical

def vectorDecoder (runtime : LivingRuntimeState process) {Observed : Type*}
    (read : Actors runtime → Observed) (value : Observed) : SourceJointClockGraph.Carrier :=
  if supported : value ∈ ((historyPMF (inventoryBound runtime)).map read).support then
    realizeModel runtime (estimate runtime read value supported) else 0

theorem decoder_at (runtime : LivingRuntimeState process) (depth : Nat) (index : Actors runtime) :
    vectorDecoder runtime (dynamicRead runtime depth) (dynamicRead runtime depth index) =
      realizeModel runtime (dynamicEstimate runtime depth index) := by
  rw [vectorDecoder, dif_pos (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index))]
  rfl

def dynamicVariance (runtime : LivingRuntimeState process) (depth : Nat) : ℝ :=
  ∑ i : Actors runtime, (historyPMF (inventoryBound runtime) i).toReal *
    ∑ j : Actors runtime,
      (posterior runtime (dynamicRead runtime depth) (dynamicRead runtime depth i)
        (SourceWeightedRecovery.observed_supported _ _ i (positive runtime i)) j).toReal *
      ‖remaining runtime (dynamicRead runtime depth) (dynamicRead runtime depth i)
        (SourceWeightedRecovery.observed_supported _ _ i (positive runtime i)) j‖ ^ 2

theorem dynamic_error_decomposition (runtime : LivingRuntimeState process) (depth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) :
    dynamicError runtime depth decoder = dynamicVariance runtime depth +
      ∑ i : Actors runtime, (historyPMF (inventoryBound runtime) i).toReal *
        ‖realizeModel runtime (dynamicEstimate runtime depth i) - decoder (dynamicRead runtime depth i)‖ ^ 2 := by
  have paid := SourceVectorMoment.conditional_error (historyPMF (inventoryBound runtime))
    (dynamicRead runtime depth) (positive runtime) (SourceJointClockGraph.action ∘ actor runtime) decoder
  simpa only [dynamicError, dynamicVariance, SourceVectorMoment.variance, SourceVectorMoment.error,
    remaining, mean_source, Function.comp_apply, realized_next, dynamicEstimate] using paid

theorem dynamic_attains (runtime : LivingRuntimeState process) (depth : Nat) :
    dynamicError runtime depth (vectorDecoder runtime (dynamicRead runtime depth)) = dynamicVariance runtime depth := by
  rw [dynamic_error_decomposition]
  simp only [decoder_at, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, Finset.sum_const_zero, add_zero]

theorem dynamic_optimal (runtime : LivingRuntimeState process) (depth : Nat)
    (decoder : Field parity → SourceJointClockGraph.Carrier) : dynamicVariance runtime depth ≤ dynamicError runtime depth decoder := by
  rw [dynamic_error_decomposition]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))

theorem dynamic_variance_lower (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    3 / (inventoryBound runtime + 1 : ℝ) ≤ dynamicVariance runtime depth := by
  have paid := dynamic_error_lower runtime enough depth (vectorDecoder runtime (dynamicRead runtime depth))
  rw [dynamic_attains] at paid
  exact paid

theorem full_recovers (runtime : LivingRuntimeState process) (index : Actors runtime) :
    realizeModel runtime (estimate runtime (fullRead runtime) (fullRead runtime index) (full_supported runtime index)) =
      SourceCopyNativeModelStep.sourceValue ((history runtimeSeed (inventoryBound runtime)).stageAt index).next := by
  rw [full_clock_original, SourceConditionalModel.model_recovers, realized_next, actor_material]

theorem full_remaining_zero (runtime : LivingRuntimeState process) (index : Actors runtime) :
    remaining runtime (fullRead runtime) (fullRead runtime index) (full_supported runtime index) index = 0 := by
  rw [remaining, full_recovers, actor_material, sub_self]

theorem mean_energy (runtime : LivingRuntimeState process) {Observed : Type*} (read : Actors runtime → Observed)
    (value : Observed) (supported : value ∈ ((historyPMF (inventoryBound runtime)).map read).support) :
    ‖realizeModel runtime (estimate runtime read value supported)‖ ^ 2 =
      ‖SourceVectorMoment.mean (posterior runtime read value supported) (actor runtime)‖ ^ 2 + 1 +
      2 * (SourceJointClockGraph.clock (SourceVectorMoment.mean (posterior runtime read value supported) (actor runtime))).re := by
  rw [mean_action, SourceJointClockGraph.action_energy]
  have mass := SourceVectorMoment.mass_const (posterior runtime read value supported) (actor runtime) 1 (actor_mass runtime)
  change SourceMassCompletion.massRead (SourceJointClockGraph.joint
    (SourceVectorMoment.mean (posterior runtime read value supported) (actor runtime))) = 1 at mass
  rw [mass]
  simp [inner]

end
end SourceConditionalVector
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
