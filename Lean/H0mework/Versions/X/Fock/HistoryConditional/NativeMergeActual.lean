import H0mework.Versions.X.Fock.HistoryConditional.NativeObserversConsumer
import H0mework.Fock.HistoryConditional.NativeMergeRows
import H0mework.Versions.X.Fock.HistoryConditional.NativePosteriorField

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalNativeMerge

def forgetClock (value : ℤ × ℤ) : ZMod 2 := ((value.2 - value.1 : ℤ) : ZMod 2)

theorem clock_factor (index : Nat) : forgetClock (SourceConditionalNativeObservers.clockRead 0 index) = (index : ZMod 2) := by
  simp [forgetClock, SourceConditionalNativeObservers.clockRead]

theorem full_source (runtime : LivingRuntimeState NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime.process)
    (actor : SourceConditionalModel.Actors runtime) :
    forgetClock (SourceConditionalModel.fullRead runtime actor) = (actor.val : ZMod 2) := by
  rw [SourceConditionalNativeObservers.full_source]
  exact clock_factor actor.val

def state (bound : Nat) : SourceConditionalNativeObservers.State (ZMod 2) bound :=
  merge (SourceConditionalNativeObservers.clockRead 0) forgetClock bound
    (SourceConditionalNativeObservers.generate (SourceConditionalNativeObservers.clockRead 0) bound)

theorem state_original (bound : Nat) : state bound = SourceConditionalNativeKeys.generate bound := by
  rw [state, merged_generated]
  have same : forgetClock ∘ SourceConditionalNativeObservers.clockRead 0 = (fun index : Nat => (index : ZMod 2)) :=
    funext clock_factor
  rw [same]
  rfl

theorem state_next (bound : Nat) : state (bound + 1) = SourceConditionalNativeKeys.advance bound (state bound) := by
  rw [state_original, state_original, SourceConditionalNativeKeys.generated_next]

end SourceConditionalNativeMerge
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
