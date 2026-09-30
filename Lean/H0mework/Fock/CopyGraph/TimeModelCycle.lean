import H0mework.Fock.CopyGraph.TimeModelTime

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale indexAfter)
noncomputable section

theorem recover_hilbert (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) (coordinate : Nat) :
    hilbert (SourceCopyGraph.recover depth index value) coordinate = hilbert value (indexAfter depth index coordinate) :=
  SourceCopyGraph.recover_coordinate depth index (hilbert value) coordinate

theorem index_successor (depth : Nat) (index : Index depth) (coordinate : Nat) :
    indexAfter depth index (coordinate + 1) = indexAfter depth index coordinate + scale depth index := by
  have source : indexAfter depth index (coordinate + 1) + 1 =
      (indexAfter depth index coordinate + 1) + scale depth index := by
    simp only [SourceCopyProgram.index_exact, Nat.add_mul, Nat.one_mul]
  omega

theorem cycle_hilbert (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    hilbert (SourceCopyGraph.recover depth index (time (scale depth index) value)) =
      hilbert (SourceJointClockGraph.action (SourceCopyGraph.recover depth index value)) := by
  apply lp.ext
  funext coordinate
  rw [recover_hilbert, hilbert_next]
  cases coordinate with
  | zero =>
    rw [SourceOwnedObservationHistory.SourceShift.shift_zero_coordinate]
    apply time_hilbert_before
    have source := SourceCopyProgram.index_exact depth index 0
    have positive := SourceCopyProgram.scale_pos depth index
    simp only [Nat.zero_add, Nat.one_mul] at source
    omega
  | succ coordinate =>
    rw [SourceJointTransfer.shift_coordinate, recover_hilbert, index_successor, time_hilbert_add]

theorem recover_cycle (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.recover depth index (time (scale depth index) value) =
      SourceJointClockGraph.action (SourceCopyGraph.recover depth index value) := by
  apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
  apply Prod.ext
  · apply (WithLp.linearEquiv 2 ℂ (SourceOwnedObservationHistory.SourceShift.H × ℂ)).injective
    apply Prod.ext
    · exact cycle_hilbert depth index value
    · change mass (time (scale depth index) value) = mass value
      exact time_mass _ value
  · change (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock (time (scale depth index) value) =
      (scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value + mass value
    rw [time_clock, mul_add, inv_mul_cancel_left₀ (SourceCopyGraph.scale_nonzero depth index)]

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
