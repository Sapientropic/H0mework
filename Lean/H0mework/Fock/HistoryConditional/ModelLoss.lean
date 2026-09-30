import H0mework.Fock.HistoryConditional.ModelDynamic
import H0mework.Probability.Recovery.Collision

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open SourceWeightedRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem clock_difference (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    clockRead runtime (nextRead runtime (0 : Actors runtime)) - clockRead runtime (nextRead runtime (two runtime enough)) = -2 := by
  rw [clock_source, clock_source]
  norm_num [two]

theorem original_error_lower (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime)
    (depth : Nat) (decoder : Field parity → ℂ) :
    2 / ((inventoryBound runtime + 1 : Nat) : ℝ) ≤
      SourceWeightedRecovery.Runtime.Actor.History.rawTerminalError parity runtimeSeed (inventoryBound runtime) depth
        (clockRead runtime ∘ nextRead runtime) decoder := by
  have paid := equal_weight_pair_lower_bound (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
    (clockRead runtime ∘ nextRead runtime) decoder (0 : Actors runtime) (two runtime enough)
    (two_ne_zero runtime enough).symm (dynamic_same runtime enough depth)
    (by rw [historyPMF_apply, historyPMF_apply])
  simp only [Function.comp_apply] at paid
  rw [clock_difference, historyPMF_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast] at paid
  norm_num at paid
  convert paid using 1
  · push_cast
    ring
  · rfl

theorem original_error_positive (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime)
    (depth : Nat) (decoder : Field parity → ℂ) :
    0 < SourceWeightedRecovery.Runtime.Actor.History.rawTerminalError parity runtimeSeed (inventoryBound runtime) depth
      (clockRead runtime ∘ nextRead runtime) decoder :=
  lt_of_lt_of_le (div_pos (by norm_num) (Nat.cast_pos.mpr (Nat.succ_pos _)))
    (original_error_lower runtime enough depth decoder)

theorem original_conditional_error (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : NextModel runtime → ℂ) (decoder : Field parity → ℂ) :
    SourceWeightedRecovery.Runtime.Actor.History.rawTerminalError parity runtimeSeed (inventoryBound runtime) depth
      (decode ∘ nextRead runtime) decoder =
      (∑ index, (historyPMF (inventoryBound runtime) index).toReal *
        SourceConditionalNext.variance (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
          (SourceConditionalNext.Image.actual (nextRead runtime)) (fun item => decode item.val) (dynamicRead runtime depth index)
          (observed_supported _ _ index (positive runtime index))) +
      error (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
        (fun index => SourceConditionalNext.mean (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
          (SourceConditionalNext.Image.actual (nextRead runtime)) (fun item => decode item.val) (dynamicRead runtime depth index)
          (observed_supported _ _ index (positive runtime index))) decoder :=
  SourceConditionalNext.Image.error_variance_original _ _ _ _ (positive runtime) decoder

theorem original_complete_account (runtime : LivingRuntimeState process) (depth : Nat)
    (decode : NextModel runtime → ℂ) (decoder : Field parity → ℂ) :
    type_of% (SourceWeightedRecovery.Runtime.Actor.History.complete_error_decomposition parity runtimeSeed
      (inventoryBound runtime) depth (decode ∘ nextRead runtime) decoder) :=
  SourceWeightedRecovery.Runtime.Actor.History.complete_error_decomposition parity runtimeSeed
    (inventoryBound runtime) depth (decode ∘ nextRead runtime) decoder

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
