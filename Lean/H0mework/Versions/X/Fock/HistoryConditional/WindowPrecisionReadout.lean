import H0mework.Versions.X.Fock.HistoryConditional.WindowPrecisionEnergy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWindowPrecision

open SourceCopyProgram (Index)
open SourceCopyRecordedRecurrence (cutoff)
open SourceCopyCurrentCoordinates (hilbertLift)
open SourceOperatorObservationAcquisition (Window hilbertRead massRead clockRead)
open SourceMinimumWindowError (readout)
open SourceGeneratedAcquisitionContinuation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem hilbert_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (value : Fin (cutoff runtime index steps + 1) → ℂ) :
    ‖hilbertLift runtime index steps value‖ ^ 2 = ∑ coordinate, ‖value coordinate‖ ^ 2 := by
  have translated : SourceOwnedObservationHistory.SourceShift.shift (hilbertLift runtime index steps value) =
      SourceGInformationCost.synthesis (cutoff runtime index steps) value := by
    simp only [hilbertLift, SourceGInformationCost.synthesis, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, map_sum, map_smul, SourceOwnedObservationHistory.SourceShift.shift_basis]
  have normed := SourceOwnedObservationHistory.SourceShift.shift.norm_map (hilbertLift runtime index steps value)
  rw [translated] at normed
  exact (congrArg (fun norm : ℝ => norm ^ 2) normed.symm).trans (SourceGInformationCost.synthesis_norm _ value)

theorem readout_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    ‖readout runtime index nonunit steps samples‖ ^ 2 =
      (∑ coordinate, ‖hilbertRead runtime index nonunit steps coordinate samples‖ ^ 2) +
        ‖massRead runtime index nonunit steps samples‖ ^ 2 + ‖clockRead runtime index nonunit steps samples‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖hilbertLift runtime index steps (fun coordinate => hilbertRead runtime index nonunit steps coordinate samples)‖ ^ 2 +
    ‖massRead runtime index nonunit steps samples‖ ^ 2 + ‖clockRead runtime index nonunit steps samples‖ ^ 2 = _
  rw [hilbert_energy]

theorem action_readout_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    ‖SourceJointClockGraph.action (readout runtime index nonunit steps samples)‖ ^ 2 =
      (∑ coordinate, ‖hilbertRead runtime index nonunit steps coordinate samples‖ ^ 2) +
        ‖massRead runtime index nonunit steps samples‖ ^ 2 +
        ‖clockRead runtime index nonunit steps samples + massRead runtime index nonunit steps samples‖ ^ 2 := by
  rw [SourceJointClockGraph.action_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖SourceMassCompletion.action (SourceJointClockGraph.joint (readout runtime index nonunit steps samples))‖ ^ 2 + _ = _
  rw [SourceMassCompletion.action.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  change ‖hilbertLift runtime index steps (fun coordinate => hilbertRead runtime index nonunit steps coordinate samples)‖ ^ 2 +
    ‖massRead runtime index nonunit steps samples‖ ^ 2 +
    ‖clockRead runtime index nonunit steps samples + massRead runtime index nonunit steps samples‖ ^ 2 = _
  rw [hilbert_energy]

def gain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : ℝ :=
  (∑ coordinate, coefficientEnergy runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate)) +
    coefficientEnergy runtime index steps (massCoefficients runtime index nonunit steps) +
    coefficientEnergy runtime index steps (clockCoefficients runtime index nonunit steps)

def nextGain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) : ℝ :=
  (∑ coordinate, coefficientEnergy runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate)) +
    coefficientEnergy runtime index steps (massCoefficients runtime index nonunit steps) +
    coefficientEnergy runtime index steps (clockCoefficients runtime index nonunit steps + massCoefficients runtime index nonunit steps)

theorem readout_bound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    ‖readout runtime index nonunit steps samples‖ ^ 2 ≤ gain runtime index nonunit steps * sampleEnergy runtime index samples := by
  have coordinateBound (coordinate : Fin (cutoff runtime index steps + 1)) :=
    evaluate_bound runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate) samples
  have massBound := evaluate_bound runtime index steps (massCoefficients runtime index nonunit steps) samples
  have clockBound := evaluate_bound runtime index steps (clockCoefficients runtime index nonunit steps) samples
  simp only [hilbert_original] at coordinateBound
  rw [mass_original] at massBound
  rw [clock_original] at clockBound
  rw [readout_energy]
  have paid := add_le_add (add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun coordinate _ => coordinateBound coordinate)) massBound) clockBound
  simpa only [gain, add_mul, Finset.sum_mul] using paid

theorem action_readout_bound (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) (samples : Window runtime index) :
    ‖SourceJointClockGraph.action (readout runtime index nonunit steps samples)‖ ^ 2 ≤
      nextGain runtime index nonunit steps * sampleEnergy runtime index samples := by
  have coordinateBound (coordinate : Fin (cutoff runtime index steps + 1)) :=
    evaluate_bound runtime index steps (hilbertCoefficients runtime index nonunit steps coordinate) samples
  have massBound := evaluate_bound runtime index steps (massCoefficients runtime index nonunit steps) samples
  have clockBound := evaluate_bound runtime index steps
    (clockCoefficients runtime index nonunit steps + massCoefficients runtime index nonunit steps) samples
  simp only [hilbert_original] at coordinateBound
  rw [mass_original] at massBound
  rw [map_add, clock_original, mass_original, LinearMap.add_apply] at clockBound
  rw [action_readout_energy]
  have paid := add_le_add (add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun coordinate _ => coordinateBound coordinate)) massBound) clockBound
  simpa only [nextGain, add_mul, Finset.sum_mul] using paid

end
end SourceWindowPrecision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
