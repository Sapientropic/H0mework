import H0mework.Versions.X.Fock.PrimeField.ClockResidualKernel
import H0mework.Versions.X.Fock.SourceHistoryClock.FrameAction

/-! One original paired next read restores the existing clock model by its already generated action inverse. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourcePrimeClockResidual

open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open SourceGeneratedRuntimeHistoryProbability SourcePrimeObservationDelay

noncomputable section

abbrev Raw := Fin 1 → IntegralOneParticle × ℤ

abbrev observe (current : LivingRuntimeState process) (bound : Nat) : Fin (bound + 1) → Raw :=
  FiniteRecurrence.Native.query (process := process) jointRead 0 current bound

theorem query_value (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    observe current bound actor 0 =
      (rawField ((current.advance actor.val).state + 1), ((current.advance actor.val).state : ℤ) + 2) := by
  change (rawField ((current.advance actor.val).state + 1),
    (((current.advance actor.val).state + 1 : Nat) : ℤ) + 1) = _
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]

def queryModel (values : Raw) : SourceClockModel.Model :=
  SourceClockFrame.rebuild 0 (1, (values 0).2 - SourceClockModel.clockRead (SourceClockModel.Fock.point 0))

theorem native_mass (current : LivingRuntimeState process) :
    SourceClockModel.massRead (SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock current) = 1 := by
  change SourceClockModel.massRead (SourceClockModel.projection (SourceOperationNative.point current)) = 1
  rw [SourceClockModel.massRead_source]
  exact SourceSuccessorBoundary.mass_single ℤ current.state 1

theorem query_model_actual (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    queryModel (observe current bound actor) =
      SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock
        ((history current bound).stageAt actor).next := by
  have coordinates := SourceClockFrame.coordinates_apply 0
    (SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock
      ((history current bound).stageAt actor).next)
  rw [native_mass, one_mul, SourceOperationNative.Observed.modelPoint_read] at coordinates
  have observed : (observe current bound actor 0).2 =
      SourceClockModel.rawClock ((history current bound).stageAt actor).next.state := rfl
  unfold queryModel
  rw [observed, ← coordinates, SourceClockFrame.rebuild_coordinates]

def restoredModel (values : Raw) : SourceClockModel.Model := SourceClockFrame.inverse 0 (queryModel values)

theorem restored_model_actual (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    restoredModel (observe current bound actor) =
      SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock
        (current.advance actor.val) := by
  rw [restoredModel, query_model_actual]
  change SourceClockFrame.inverse 0
    (SourceOperationNative.Observed.modelPoint (process := process) SourceClockModel.rawClock (current.advance actor.val).tick.next) = _
  rw [← SourceOperationNative.Observed.modelAction_point]
  exact SourceClockFrame.inverse_action 0 _

def decodeClock (values : Raw) : ℂ :=
  ((SourceClockModel.clockRead (restoredModel values) - SourceClockModel.massRead (restoredModel values) : ℤ) : ℂ)

theorem clock_recovered (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    decodeClock (observe current bound actor) = (sample current bound actor : Nat) := by
  rw [decodeClock, restored_model_actual, native_mass, SourceOperationNative.Observed.modelPoint_read]
  change ((((current.advance actor.val).state : ℤ) + 1 - 1 : ℤ) : ℂ) = ((current.advance actor.val).state : ℂ)
  simp only [add_sub_cancel_right, Int.cast_natCast]

theorem observe_injective (current : LivingRuntimeState process) (bound : Nat) :
    Function.Injective (observe current bound) := by
  intro left right same
  have decoded := congrArg decodeClock same
  rw [clock_recovered, clock_recovered] at decoded
  have states : (current.advance left.val).state = (current.advance right.val).state := by
    exact_mod_cast decoded
  rw [native_state_advance, native_state_advance] at states
  exact Fin.ext (Nat.add_left_cancel states)

theorem query_material (current : LivingRuntimeState process) (bound : Nat) (actor : Fin (bound + 1)) :
    observe current bound actor 0 = jointRead ((history current bound).stageAt actor).next.state ∧
      type_of% (sample_factorizes current bound actor) :=
  ⟨rfl, sample_factorizes current bound actor⟩

end
end SourcePrimeClockResidual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
