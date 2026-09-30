import H0mework.Versions.X.Fock.CopyGraph.TimeEnergyNext

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeEnergy

open SourceCopyProgram (Index scale)
open SourceCopyTimeModel (Packet phases time finitePhases finiteRestore)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical Topology InnerProductSpace
noncomputable section

theorem clock_source : SourceCopyGraph.axes 0 1 ∈ SourceJointClockGraph.read.range.topologicalClosure :=
  SourceJointClockGraph.clock_axis_mem_closure 1

theorem clock_time (steps : Nat) (scalar : ℂ) :
    time steps (SourceCopyGraph.axes 0 scalar) = SourceCopyGraph.axes 0 scalar := by
  induction steps with
  | zero => rfl
  | succ steps previous =>
    rw [SourceCopyTimeModel.time_succ, previous, SourceJointClockGraph.action_apply]
    change WithLp.toLp 2 (SourceMassCompletion.action 0, scalar + 0) = SourceCopyGraph.axes 0 scalar
    rw [map_zero, add_zero]
    rfl

theorem clock_phase (depth : Nat) (index : Index depth) (phase : Fin (index.val + 1)) :
    phases depth index (SourceCopyGraph.axes 0 1) phase = SourceCopyGraph.axes 0 ((scale depth index : ℂ)⁻¹) := by
  rw [SourceCopyTimeModel.phase_source, clock_time, SourceCopyGraph.recover_apply]
  change WithLp.toLp 2 (WithLp.toLp 2 (SourceCopyGraph.hilbertRecover depth index 0, (0 : ℂ)),
    (scale depth index : ℂ)⁻¹ * 1) = _
  rw [map_zero, mul_one]
  rfl

theorem clock_norm (scalar : ℂ) : ‖SourceCopyGraph.axes 0 scalar‖ ^ 2 = ‖scalar‖ ^ 2 := by
  rw [SourceCopyGraph.axes, WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change (‖(0 : SourceOwnedObservationHistory.SourceShift.H)‖ ^ 2 + ‖(0 : ℂ)‖ ^ 2) + ‖scalar‖ ^ 2 = _
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

theorem clock_observation_energy (depth : Nat) (index : Index depth) :
    (∑ phase : Fin (index.val + 1), ‖phases depth index (SourceCopyGraph.axes 0 1) phase‖ ^ 2) =
      (scale depth index : ℝ)⁻¹ := by
  simp only [clock_phase, clock_norm, norm_inv, Complex.norm_natCast,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← SourceCopyProgram.scale_source depth index]
  have nonzero : (scale depth index : ℝ) ≠ 0 := by exact_mod_cast (SourceCopyProgram.scale_pos depth index).ne'
  field_simp

theorem clock_gap (depth : Nat) (index : Index depth) (nonunit : index.val ≠ 0) :
    (∑ phase : Fin (index.val + 1), ‖phases depth index (SourceCopyGraph.axes 0 1) phase‖ ^ 2) <
      ‖SourceCopyGraph.axes 0 1‖ ^ 2 := by
  rw [clock_observation_energy, clock_norm, norm_one, one_pow]
  have greater : (1 : ℝ) < scale depth index := by
    rw [SourceCopyProgram.scale_source]
    exact_mod_cast (show 1 < index.val + 1 by omega)
  exact inv_lt_one_of_one_lt₀ greater

theorem finite_amplification (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) :
    ∃ steps : Nat,
      (∑ phase : Fin (index.val + 1), ‖finitePhases runtime index steps (SourceCopyGraph.axes 0 1) phase‖ ^ 2) <
        ‖finiteRestore runtime index steps (SourceCopyGraph.axes 0 1)‖ ^ 2 := by
  have continuous : Continuous (fun packet : Packet (inventoryBound runtime) index =>
      ∑ phase : Fin (index.val + 1), ‖packet phase‖ ^ 2) := by fun_prop
  have input := continuous.continuousAt.tendsto.comp
    (SourceCopyTimeModel.finite_phases_tendsto runtime index (SourceCopyGraph.axes 0 1))
  have output := (SourceCopyTimeModel.finite_restore_tendsto runtime index (SourceCopyGraph.axes 0 1)).norm.pow 2
  exact (input.eventually_lt output (clock_gap _ index nonunit)).exists

theorem root_unit_work (depth : Nat) (index : Index depth) :
    clockWork depth index (SourceJointClockGraph.recover (SourceJointClockGraph.read
      (SourceClockComplex.ofNative (SourceOwnedObservationHistory.sourcePoint 0)))) = (scale depth index : ℝ) ^ 2 := by
  rw [SourceJointClockGraph.root_unit_recovery]
  change (scale depth index : ℝ) ^ 2 * (‖(1 : ℂ)‖ ^ 2 + 2 * (⟪(0 : ℂ), (1 : ℂ)⟫_ℂ).re) = _
  norm_num

theorem signed_work (depth : Nat) (index : Index depth) :
    clockWork depth index (SourceCopyGraph.axes 1 (-1)) = -(scale depth index : ℝ) ^ 2 := by
  change (scale depth index : ℝ) ^ 2 * (‖(1 : ℂ)‖ ^ 2 + 2 * (⟪(-1 : ℂ), (1 : ℂ)⟫_ℂ).re) = _
  norm_num [inner]

end
end SourceCopyTimeEnergy
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
