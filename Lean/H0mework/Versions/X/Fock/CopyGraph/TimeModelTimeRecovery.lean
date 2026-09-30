import H0mework.Versions.X.Fock.CopyGraph.TimeModelCoordinates

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

noncomputable section

def timeRecovery (steps : Nat) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceJointClockGraph.recover ^ steps

theorem time_recovery_succ (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    timeRecovery (steps + 1) value = timeRecovery steps (SourceJointClockGraph.recover value) := by
  rw [timeRecovery, pow_succ]
  rfl

theorem recovered_hilbert (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (SourceJointClockGraph.recover value) coordinate = hilbert value (coordinate + 1) := by
  rw [SourceJointClockGraph.recover_apply]
  change SourceMassCompletion.firstRead (SourceJointTransfer.wholeTransfer (SourceJointClockGraph.joint value)) coordinate = _
  rw [SourceJointTransfer.whole_transfer]
  exact SourceJointTransfer.transfer_coordinate _ coordinate

theorem recovered_mass (value : SourceJointClockGraph.Carrier) : mass (SourceJointClockGraph.recover value) = mass value := by
  rw [SourceJointClockGraph.recover_apply]
  change SourceMassCompletion.massRead (SourceJointTransfer.wholeTransfer (SourceJointClockGraph.joint value)) = _
  rw [SourceJointTransfer.whole_transfer]
  rfl

theorem recovered_clock (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (SourceJointClockGraph.recover value) = SourceJointClockGraph.clock value - mass value := rfl

theorem time_recovery_hilbert (steps : Nat) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (timeRecovery steps value) coordinate = hilbert value (coordinate + steps) := by
  induction steps generalizing value with
  | zero => rfl
  | succ steps previous =>
    rw [time_recovery_succ, previous, recovered_hilbert]
    rfl

theorem time_recovery_mass (steps : Nat) (value : SourceJointClockGraph.Carrier) : mass (timeRecovery steps value) = mass value := by
  induction steps generalizing value with
  | zero => rfl
  | succ steps previous => rw [time_recovery_succ, previous, recovered_mass]

theorem time_recovery_clock (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (timeRecovery steps value) = SourceJointClockGraph.clock value - (steps : ℂ) * mass value := by
  induction steps generalizing value with
  | zero => simp only [timeRecovery, pow_zero, Nat.cast_zero, zero_mul, sub_zero]; rfl
  | succ steps previous =>
    rw [time_recovery_succ, previous, recovered_clock, recovered_mass]
    push_cast
    ring

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
