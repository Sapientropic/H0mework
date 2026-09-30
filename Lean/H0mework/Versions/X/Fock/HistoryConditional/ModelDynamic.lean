import H0mework.Versions.X.Fock.HistoryConditional.ModelSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalModel

open SourceGeneratedAcquisitionContinuation SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
attribute [local instance] SourceConditionalNext.Image.valuesFintype SourceConditionalNext.Image.valuesMeasurable
  SourceConditionalNext.Image.valuesSingleton

local instance : UniformSpace (Field parity) := fieldUniform parity
local instance : MeasurableSpace (Field parity) := fieldBorel parity
local instance : BorelSpace (Field parity) := ⟨rfl⟩
local instance : T2Space (Field parity) := field_t2 parity

theorem complete_parity_two (runtime : LivingRuntimeState process) :
    SourceOperationNative.Observed.observedPoint parity (runtime.advance 2) =
      SourceOperationNative.Observed.observedPoint parity runtime := by
  apply (SourceOperationNative.Observed.native_fibre_iff parity _ _).mpr
  intro stage
  rw [advance_original (runtime.advance 2) stage, advance_original runtime stage, runtimeAt_state, runtimeAt_state,
    advance_original runtime 2, runtimeAt_state]
  change ((runtime.state + 2 + stage : Nat) : ZMod 2) = ((runtime.state + stage : Nat) : ZMod 2)
  push_cast
  norm_num
  decide

def two (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) : Actors runtime :=
  ⟨2, by omega⟩

theorem two_ne_zero (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    two runtime enough ≠ 0 := by
  intro same
  have values := congrArg Fin.val same
  norm_num [two] at values

def dynamicRead (runtime : LivingRuntimeState process) (depth : Nat) : Actors runtime → Field parity :=
  SourceConditionalTransfer.fieldSample parity (runtimeSeed.advance (depth + 1)) (inventoryBound runtime)

theorem dynamic_same (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    dynamicRead runtime depth (0 : Actors runtime) = dynamicRead runtime depth (two runtime enough) :=
  (complete_parity_two (runtimeSeed.advance (depth + 1))).symm

theorem next_distinct (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) :
    nextRead runtime (0 : Actors runtime) ≠ nextRead runtime (two runtime enough) := by
  intro same
  have clocks := congrArg (clockRead runtime) same
  rw [clock_source, clock_source] at clocks
  norm_num [two] at clocks

def dynamicInformation (runtime : LivingRuntimeState process) (depth : Nat) : ℝ :=
  SourceConditionalNext.conditionalEntropy (historyPMF (inventoryBound runtime)) (dynamicRead runtime depth)
    (SourceConditionalNext.Image.actual (nextRead runtime)) (positive runtime)

theorem dynamic_information_positive (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    0 < dynamicInformation runtime depth := by
  have nonnegative : 0 ≤ dynamicInformation runtime depth := SourceConditionalNext.conditionalEntropy_nonnegative _ _ _ _
  have nonzero : dynamicInformation runtime depth ≠ 0 := by
    intro zero
    have determined := (SourceConditionalNext.Image.entropy_zero_iff (historyPMF (inventoryBound runtime))
      (dynamicRead runtime depth) (nextRead runtime) (positive runtime)).mp zero
    exact next_distinct runtime enough (determined 0 (two runtime enough) (dynamic_same runtime enough depth))
  exact lt_of_le_of_ne nonnegative nonzero.symm

theorem no_dynamic_decoder (runtime : LivingRuntimeState process) (enough : 2 ≤ inventoryBound runtime) (depth : Nat) :
    ¬ ∃ decoder : Field parity → NextModel runtime,
      ∀ index : Actors runtime, decoder (dynamicRead runtime depth index) = nextRead runtime index := by
  rintro ⟨decoder, recovers⟩
  have same := congrArg decoder (dynamic_same runtime enough depth)
  rw [recovers, recovers] at same
  exact next_distinct runtime enough same

end
end SourceConditionalModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
