import H0mework.Fock.HistoryConditional.InformationModel
import H0mework.Probability.Source.ConditionalKernel

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInformationReadback

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceConditionalModel (Actors nextRead positive dynamicRead dynamicInformation)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype
  SourceConditionalNext.Image.valuesMeasurable SourceConditionalNext.Image.valuesSingleton
local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem native_parity_kernel (left right : LivingRuntimeState process) :
    SourceOperationNative.Observed.observedPoint parity left = SourceOperationNative.Observed.observedPoint parity right ↔
      (left.state : ZMod 2) = (right.state : ZMod 2) := by
  rw [SourceOperationNative.Observed.native_fibre_iff]
  constructor
  · intro same
    exact same 0
  · intro same stage
    rw [advance_original, advance_original, runtimeAt_state, runtimeAt_state]
    change ((left.state + stage : Nat) : ZMod 2) = ((right.state + stage : Nat) : ZMod 2)
    push_cast
    rw [same]

def parityCode (runtime : LivingRuntimeState process) (index : Actors runtime) : ZMod 2 := index.val

theorem dynamic_kernel (runtime : LivingRuntimeState process) (depth : Nat) (left right : Actors runtime) :
    dynamicRead runtime depth left = dynamicRead runtime depth right ↔ parityCode runtime left = parityCode runtime right := by
  change SourceOperationNative.Observed.observedPoint parity ((runtimeSeed.advance (depth + 1)).advance left.val) =
    SourceOperationNative.Observed.observedPoint parity ((runtimeSeed.advance (depth + 1)).advance right.val) ↔ _
  rw [native_parity_kernel]
  simp only [advance_original, runtimeAt_state, Nat.cast_add, parityCode, add_left_cancel_iff]

theorem dynamic_conditional (runtime : LivingRuntimeState process) (depth : Nat) (index : Actors runtime) :
    SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth) (dynamicRead runtime depth index)
      (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index)) =
    SourceConditionalHistory.conditional (historyPMF (inventoryBound runtime)) (parityCode runtime) (parityCode runtime index)
      (SourceWeightedRecovery.observed_supported _ _ index (positive runtime index)) :=
  SourceConditionalHistory.conditional_eq_of_fibre _ _ _ _ _ _ _ (fun other => dynamic_kernel runtime depth other index)

theorem dynamic_information_code (runtime : LivingRuntimeState process) (depth : Nat) :
    dynamicInformation runtime depth = SourceUniformFibreInformation.conditionalEntropy (inventoryBound runtime) (parityCode runtime) := by
  unfold dynamicInformation
  rw [SourceConditionalNext.conditionalEntropy_eq_of_kernel _ _ (parityCode runtime) _ _ (dynamic_kernel runtime depth)]
  exact model_information runtime (parityCode runtime)

theorem dynamic_information_lower (runtime : LivingRuntimeState process) (depth : Nat) :
    Real.log (inventoryBound runtime + 1 : ℝ) - Real.log 2 ≤ dynamicInformation runtime depth := by
  rw [dynamic_information_code]
  simpa only [ZMod.card, Nat.cast_ofNat] using
    SourceUniformFibreInformation.Capacity.information_lower (inventoryBound runtime) (parityCode runtime)

theorem dynamic_exponential_lower (runtime : LivingRuntimeState process) (depth : Nat) :
    ((inventoryBound runtime + 1 : ℝ) / 2) ^ 2 ≤ Real.exp (2 * dynamicInformation runtime depth) := by
  rw [dynamic_information_code]
  simpa only [ZMod.card, Nat.cast_ofNat] using
    SourceUniformFibreInformation.Capacity.exponential_information_lower (inventoryBound runtime) (parityCode runtime)

end
end SourceInformationReadback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
