import H0mework.Versions.X.Fock.CopyGraph.TimeModelTimeRecovery

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeModel

open SourceCopyProgram (Index scale)
open SourceOwnedObservationHistory.SourceShift (H)
open scoped Classical
noncomputable section

def restore (depth : Nat) (index : Index depth) (packet : Packet depth index) : SourceJointClockGraph.Carrier :=
  (∑ phase : Fin (index.val + 1), timeRecovery phase.val (SourceCopyGraph.action depth index (packet phase))) -
    (index.val : ℂ) • SourceCopyGraph.axes (mass (packet 0)) ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet 0))

theorem term_hilbert (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) (coordinate : Nat) :
    hilbert (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase))) coordinate =
      if phase = phaseAt depth index coordinate then hilbert value coordinate else 0 := by
  rw [time_recovery_hilbert, phase_source, projected_coordinate]
  simp only [phase_range, time_hilbert_add]

theorem term_mass (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) :
    mass (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase))) = mass value := by
  rw [time_recovery_mass, phase_source]
  change mass (time phase.val value) = _
  exact time_mass phase.val value

theorem term_clock (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier)
    (phase : Fin (index.val + 1)) :
    SourceJointClockGraph.clock (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase))) =
      SourceJointClockGraph.clock value := by
  rw [time_recovery_clock, phase_source, SourceCopyGraph.action_recover]
  change SourceJointClockGraph.clock (time phase.val value) - (phase.val : ℂ) * mass (time phase.val value) = _
  rw [time_clock, time_mass, add_sub_cancel_right]

theorem axes_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    SourceCopyGraph.axes (mass (phases depth index value 0))
      ((scale depth index : ℂ) * SourceJointClockGraph.clock (phases depth index value 0)) =
        SourceCopyGraph.axes (mass value) (SourceJointClockGraph.clock value) := by
  rw [phase_source]
  change SourceCopyGraph.axes (mass value)
    ((scale depth index : ℂ) * ((scale depth index : ℂ)⁻¹ * SourceJointClockGraph.clock value)) = _
  rw [mul_inv_cancel_left₀ (SourceCopyGraph.scale_nonzero depth index)]

theorem restore_hilbert (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    hilbert (restore depth index (phases depth index value)) = hilbert value := by
  apply lp.ext
  funext coordinate
  simp only [restore, hilbert, map_sub, map_sum, map_smul]
  change ((∑ phase : Fin (index.val + 1),
    hilbert (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase)))) -
      (index.val : ℂ) • (0 : H)) coordinate = _
  rw [smul_zero, sub_zero, lp.coeFn_sum, Finset.sum_apply]
  simp only [term_hilbert, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem restore_mass (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    mass (restore depth index (phases depth index value)) = mass value := by
  rw [restore, axes_source]
  simp only [mass, map_sub, map_sum, map_smul]
  change (∑ phase : Fin (index.val + 1),
    mass (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase)))) -
      (index.val : ℂ) * mass value = mass value
  simp only [term_mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem restore_clock (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    SourceJointClockGraph.clock (restore depth index (phases depth index value)) = SourceJointClockGraph.clock value := by
  rw [restore, axes_source]
  simp only [map_sub, map_sum, map_smul]
  change (∑ phase : Fin (index.val + 1),
    SourceJointClockGraph.clock (timeRecovery phase.val (SourceCopyGraph.action depth index (phases depth index value phase)))) -
      (index.val : ℂ) * SourceJointClockGraph.clock value = SourceJointClockGraph.clock value
  simp only [term_clock, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem restore_source (depth : Nat) (index : Index depth) (value : SourceJointClockGraph.Carrier) :
    restore depth index (phases depth index value) = value := by
  apply (WithLp.linearEquiv 2 ℂ (SourceMassCompletion.Joint × ℂ)).injective
  apply Prod.ext
  · apply (WithLp.linearEquiv 2 ℂ (H × ℂ)).injective
    exact Prod.ext (restore_hilbert depth index value) (restore_mass depth index value)
  · exact restore_clock depth index value

end
end SourceCopyTimeModel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
