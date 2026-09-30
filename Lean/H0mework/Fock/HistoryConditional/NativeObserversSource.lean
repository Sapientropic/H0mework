import H0mework.Fock.HistoryConditional.NativeObserversUpdate
import H0mework.Fock.HistoryConditional.NativeKeysWord

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeObservers

def clockRead (depth index : Nat) : ℤ × ℤ := (1, ((index + (depth + 1) : Nat) : ℤ))

noncomputable section
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open SourceConditionalModel (Actors fullRead)
open SourceGeneratedAcquisitionContinuation (inventoryBound)

theorem clock_source (bound depth : Nat) (index : Fin (bound + 1)) :
    SourceWeightedRecovery.Runtime.Actor.History.Clock.observe bound depth index = clockRead depth index.val := by
  rw [SourceWeightedRecovery.Runtime.Actor.History.Clock.observe,
    SourceWeightedRecovery.Runtime.Actor.History.Clock.futureModel_source,
    SourceClockFrame.coordinates_apply, SourceClockModel.Fock.mass_current,
    SourceClockModel.Fock.clock_current, SourceClockModel.Fock.clock_current]
  simp only [runtimeAt_scanIndex, clockRead, Nat.cast_add, Nat.cast_one, Nat.cast_zero, one_mul]
  congr 1
  ring

theorem clock_injective (depth : Nat) : Function.Injective (clockRead depth) := by
  intro left right same
  have actual : SourceWeightedRecovery.Runtime.Actor.History.Clock.observe (max left right) depth ⟨left, by omega⟩ =
      SourceWeightedRecovery.Runtime.Actor.History.Clock.observe (max left right) depth ⟨right, by omega⟩ := by
    simpa only [clock_source] using same
  exact congrArg Fin.val (SourceWeightedRecovery.Runtime.Actor.History.Clock.observe_injective _ _ actual)

theorem parity_generated (bound : Nat) :
    generate (fun index : Nat => (index : ZMod 2)) bound = SourceConditionalNativeKeys.generate bound := rfl

theorem full_source (runtime : LivingRuntimeState process) (index : Actors runtime) :
    fullRead runtime index = clockRead 0 index.val :=
  clock_source (inventoryBound runtime) 0 index

end
end SourceConditionalNativeObservers
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
