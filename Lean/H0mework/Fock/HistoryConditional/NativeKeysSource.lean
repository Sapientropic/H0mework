import H0mework.Fock.HistoryConditional.RationalStreamMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeKeys

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

def observed (depth : Nat) (key : ZMod 2) : Field parity :=
  SourceOperationNative.Observed.observedPoint parity (runtimeSeed.advance (depth + 1 + key.val))

theorem observed_injective (depth : Nat) : Function.Injective (observed depth) := by
  intro left right same
  have native := (SourceInformationReadback.native_parity_kernel
    (runtimeSeed.advance (depth + 1 + left.val)) (runtimeSeed.advance (depth + 1 + right.val))).mp same
  simp only [advance_original, runtimeAt_state, Nat.cast_add, ZMod.natCast_zmod_val] at native
  have tail := add_left_cancel native
  exact add_left_cancel tail

theorem source_observed (bound depth : Nat) (index : Fin (bound + 1)) :
    SourceConditionalInventory.observation bound depth index = observed depth (index.val : ZMod 2) := by
  change SourceOperationNative.Observed.observedPoint parity ((runtimeSeed.advance (depth + 1)).advance index.val) =
    SourceOperationNative.Observed.observedPoint parity (runtimeSeed.advance (depth + 1 + (index.val : ZMod 2).val))
  apply (SourceInformationReadback.native_parity_kernel _ _).mpr
  simp only [advance_original, runtimeAt_state, Nat.cast_add, ZMod.natCast_zmod_val]
  ring

theorem birth_observed (bound depth : Nat) :
    SourceConditionalInventory.bornObservation bound depth = observed depth ((bound + 1 : Nat) : ZMod 2) :=
  source_observed (bound + 1) depth (Fin.last (bound + 1))

end
end SourceConditionalNativeKeys
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
