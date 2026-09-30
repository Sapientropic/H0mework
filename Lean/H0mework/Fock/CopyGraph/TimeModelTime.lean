import H0mework.Fock.CopyGraph.RecoveryBudgetObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

abbrev hilbert (value : SourceJointClockGraph.Carrier) := SourceMassCompletion.firstRead (SourceJointClockGraph.joint value)
abbrev mass (value : SourceJointClockGraph.Carrier) := SourceMassCompletion.massRead (SourceJointClockGraph.joint value)

def time (steps : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.action ^ steps

theorem time_succ (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    time (steps + 1) value = SourceJointClockGraph.action (time steps value) := by
  rw [time, pow_succ']
  rfl

theorem hilbert_next (value : SourceJointClockGraph.Carrier) :
    hilbert (SourceJointClockGraph.action value) = SourceOwnedObservationHistory.SourceShift.shift (hilbert value) := rfl

theorem mass_next (value : SourceJointClockGraph.Carrier) : mass (SourceJointClockGraph.action value) = mass value := rfl

theorem clock_next (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (SourceJointClockGraph.action value) = SourceJointClockGraph.clock value + mass value := rfl

theorem time_mass (steps : Nat) (value : SourceJointClockGraph.Carrier) : mass (time steps value) = mass value := by
  induction steps with
  | zero => rfl
  | succ steps previous => rw [time_succ, mass_next, previous]

theorem time_clock (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (time steps value) = SourceJointClockGraph.clock value + (steps : ℂ) * mass value := by
  induction steps with
  | zero => simp only [time, pow_zero, Nat.cast_zero, zero_mul, add_zero]; rfl
  | succ steps previous =>
    rw [time_succ, clock_next, previous, time_mass]
    push_cast
    ring

theorem time_hilbert_add (steps : Nat) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (time steps value) (coordinate + steps) = hilbert value coordinate := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [time_succ, hilbert_next]
    change SourceOwnedObservationHistory.SourceShift.shift (hilbert (time steps value)) ((coordinate + steps) + 1) = _
    rw [SourceJointTransfer.shift_coordinate, previous]

theorem time_hilbert_before (steps : Nat) (value : SourceJointClockGraph.Carrier)
    (coordinate : Nat) (before : coordinate < steps) : hilbert (time steps value) coordinate = 0 := by
  induction steps generalizing coordinate with
  | zero => omega
  | succ steps previous =>
    rw [time_succ, hilbert_next]
    cases coordinate with
    | zero => exact SourceOwnedObservationHistory.SourceShift.shift_zero_coordinate _
    | succ coordinate =>
      rw [SourceJointTransfer.shift_coordinate]
      exact previous coordinate (Nat.lt_of_succ_lt_succ before)

theorem time_word (steps : Nat) :
    (time steps).toLinearMap = SourceGeneratedActionWords.run (fun _ : Unit => SourceJointClockGraph.action.toLinearMap)
      (List.replicate steps ()) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [List.replicate_succ, SourceGeneratedActionWords.run, ← previous]
    change (SourceJointClockGraph.action ^ (steps + 1)).toLinearMap =
      (SourceJointClockGraph.action ^ steps).toLinearMap * SourceJointClockGraph.action.toLinearMap
    rw [pow_succ]
    rfl

theorem time_native (runtime : LivingRuntimeState process) (steps : Nat) :
    time steps (SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point runtime))) =
      SourceJointClockGraph.read (SourceClockComplex.ofNative (SourceOperationNative.point (runtime.advance steps))) := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [time_succ, previous, SourceJointClockGraph.native_next]
    rfl

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
