import H0mework.Versions.X.Fock.CopyGraph.TimeModelObservation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeEnergy

open SourceCopyProgram (Index scale indexAfter)
open SourceCopyTimeModel (Packet hilbert mass time timeRecovery restore)
open SourceOwnedObservationHistory.SourceShift (H)
open scoped Classical InnerProductSpace
noncomputable section

def part (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1))
    (value : SourceJointClockGraph.Carrier) : H :=
  hilbert (timeRecovery phase.val (SourceCopyGraph.action depth index value))

theorem time_norm (steps : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖hilbert (time steps value)‖ = ‖hilbert value‖ := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [SourceCopyTimeModel.time_succ, SourceCopyTimeModel.hilbert_next,
      SourceOwnedObservationHistory.SourceShift.shift.norm_map, previous]

theorem part_outside (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1))
    (value : SourceJointClockGraph.Carrier) (coordinate : Nat)
    (outside : phase ≠ SourceCopyTimeModel.phaseAt depth index coordinate) :
    part depth index phase value coordinate = 0 := by
  rw [part, SourceCopyTimeModel.time_recovery_hilbert]
  apply SourceCopyTimeModel.action_outside
  exact fun present => outside ((SourceCopyTimeModel.phase_range depth index coordinate phase).mp present)

theorem time_part (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1))
    (value : SourceJointClockGraph.Carrier) :
    hilbert (time phase.val (timeRecovery phase.val (SourceCopyGraph.action depth index value))) =
      hilbert (SourceCopyGraph.action depth index value) := by
  apply lp.ext
  funext coordinate
  by_cases before : coordinate < phase.val
  · rw [SourceCopyTimeModel.time_hilbert_before _ _ _ before]
    symm
    apply SourceCopyTimeModel.action_outside
    rw [SourceCopyProgram.index_range, SourceCopyProgram.scale_source]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  · have after : coordinate = coordinate - phase.val + phase.val := by omega
    conv_lhs => rw [after]
    rw [SourceCopyTimeModel.time_hilbert_add, SourceCopyTimeModel.time_recovery_hilbert, ← after]

theorem part_norm (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1))
    (value : SourceJointClockGraph.Carrier) : ‖part depth index phase value‖ = ‖hilbert value‖ := by
  have unchanged := congrArg norm (time_part depth index phase value)
  rw [time_norm] at unchanged
  change ‖part depth index phase value‖ = ‖SourceCopyGraph.hilbertAction depth index (hilbert value)‖ at unchanged
  exact unchanged.trans ((SourceCopyGraph.hilbertAction depth index).norm_map _)

theorem part_orthogonal (depth : Nat) (index : Index depth) (left right : Fin (index.val + 1))
    (distinct : left ≠ right) (x y : SourceJointClockGraph.Carrier) :
    ⟪part depth index left x, part depth index right y⟫_ℂ = 0 := by
  rw [lp.inner_eq_tsum]
  have zero : ∀ coordinate : Nat, ⟪part depth index left x coordinate, part depth index right y coordinate⟫_ℂ = 0 := by
    intro coordinate
    by_cases present : left = SourceCopyTimeModel.phaseAt depth index coordinate
    · rw [part_outside depth index right y coordinate (fun same => distinct (present.trans same.symm)), inner_zero_right]
    · rw [part_outside depth index left x coordinate present, inner_zero_left]
  simp only [zero, tsum_zero]

theorem parts_energy (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    ‖∑ phase : Fin (index.val + 1), part depth index phase (packet phase)‖ ^ 2 =
      ∑ phase : Fin (index.val + 1), ‖hilbert (packet phase)‖ ^ 2 := by
  have diagonal : ∀ phase : Fin (index.val + 1),
      (∑ other : Fin (index.val + 1), ⟪part depth index other (packet other), part depth index phase (packet phase)⟫_ℂ) =
        ⟪part depth index phase (packet phase), part depth index phase (packet phase)⟫_ℂ := by
    intro phase
    apply Finset.sum_eq_single phase
    · intro other _ different
      exact part_orthogonal depth index other phase different _ _
    · simp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [sum_inner, inner_sum, diagonal, map_sum, ← norm_sq_eq_re_inner (𝕜 := ℂ), part_norm]

theorem restore_hilbert (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    hilbert (restore depth index packet) = ∑ phase : Fin (index.val + 1), part depth index phase (packet phase) := by
  simp only [restore, hilbert, map_sub, map_sum, map_smul]
  change (∑ phase : Fin (index.val + 1), part depth index phase (packet phase)) - (index.val : ℂ) • (0 : H) = _
  rw [smul_zero, sub_zero]

theorem restore_mass (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    mass (restore depth index packet) =
      (∑ phase : Fin (index.val + 1), mass (packet phase)) - (index.val : ℂ) * mass (packet 0) := by
  simp only [restore, mass, map_sub, map_sum, map_smul]
  change (∑ phase : Fin (index.val + 1), mass (timeRecovery phase.val (SourceCopyGraph.action depth index (packet phase)))) -
    (index.val : ℂ) * mass (packet 0) = _
  simp only [SourceCopyTimeModel.time_recovery_mass]
  rfl

theorem restore_clock (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    SourceJointClockGraph.clock (restore depth index packet) =
      (∑ phase : Fin (index.val + 1), ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet phase) -
        (phase.val : ℂ) * mass (packet phase))) -
      (index.val : ℂ) * ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet 0)) := by
  simp only [restore, map_sub, map_sum, map_smul, SourceCopyTimeModel.time_recovery_clock]
  rfl

theorem restore_energy (depth : Nat) (index : Index depth) (packet : Packet depth index) :
    ‖restore depth index packet‖ ^ 2 =
      (∑ phase : Fin (index.val + 1), ‖hilbert (packet phase)‖ ^ 2) +
      ‖(∑ phase : Fin (index.val + 1), mass (packet phase)) - (index.val : ℂ) * mass (packet 0)‖ ^ 2 +
      ‖(∑ phase : Fin (index.val + 1), ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet phase) -
          (phase.val : ℂ) * mass (packet phase))) -
        (index.val : ℂ) * ((scale depth index : ℂ) * SourceJointClockGraph.clock (packet 0))‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖hilbert (restore depth index packet)‖ ^ 2 + ‖mass (restore depth index packet)‖ ^ 2) +
    ‖SourceJointClockGraph.clock (restore depth index packet)‖ ^ 2 = _
  rw [restore_hilbert, parts_energy, restore_mass, restore_clock]

end
end SourceCopyTimeEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
