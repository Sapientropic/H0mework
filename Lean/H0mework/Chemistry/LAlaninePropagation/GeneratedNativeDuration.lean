import H0mework.Chemistry.LAlaninePropagation.GeneratedShortTimeResponse
import Mathlib.Data.Matrix.Basis

/-!
# A responding duration calculated from integer source entries

The entrywise L1 bound is obtained by the existing matrix-single expansion and
operator norm bound. All magnitude and duration data are computed from the
source integers; no norm bound or target is supplied by a caller.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Dynamics.NativeDuration

open Interface ShortTime

private theorem single_action (i j : Basis) (value : ℂ) (vector : ElectronicSpace) :
    matrixOperatorEquiv (Matrix.single i j value) vector =
      PiLp.single 2 i (value * vector.ofLp j) := by
  ext k
  change Matrix.mulVec (Matrix.single i j value) vector.ofLp k =
    (Pi.single i (value * vector.ofLp j) : Basis → ℂ) k
  simp [Matrix.single_mulVec, Pi.single]

private theorem single_norm_le (i j : Basis) (value : ℂ) :
    ‖matrixOperatorEquiv (Matrix.single i j value)‖ ≤ ‖value‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg value)
  intro vector
  rw [single_action, PiLp.norm_single, norm_mul]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le vector j) (norm_nonneg value)

/-- No spectral estimate or separately supplied matrix norm certificate is needed. -/
theorem matrixOperator_norm_le_entrySum (matrix : Matrix Basis Basis ℂ) :
    ‖matrixOperatorEquiv matrix‖ ≤ ∑ i : Basis, ∑ j : Basis, ‖matrix i j‖ := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single matrix]
  rw [map_sum]
  calc
    ‖∑ i : Basis, matrixOperatorEquiv (∑ j : Basis, Matrix.single i j (matrix i j))‖ ≤
        ∑ i : Basis, ‖matrixOperatorEquiv (∑ j : Basis, Matrix.single i j (matrix i j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Basis, ∑ j : Basis, ‖matrix i j‖ := by
      apply Finset.sum_le_sum
      intro i _membership
      rw [map_sum]
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => single_norm_le i j (matrix i j))

def sourceEntryMagnitude (source : ElectronicPropagationSource) : Nat :=
  ∑ i : Basis, ∑ j : Basis, (activeNumerator source i j).natAbs

def sourceOperatorBound (source : ElectronicPropagationSource) : ℚ :=
  ((1000000000000000 + sourceEntryMagnitude source : Nat) : ℚ) / 1000000000000000

def sourceNativeDuration (source : ElectronicPropagationSource) : ℚ :=
  1 / (4 * sourceOperatorBound source)

theorem sourceOperatorBound_positive (source : ElectronicPropagationSource) :
    0 < sourceOperatorBound source := by
  unfold sourceOperatorBound
  positivity

theorem sourceNativeDuration_positive (source : ElectronicPropagationSource) :
    0 < sourceNativeDuration source :=
  rationalDuration_positive (sourceOperatorBound_positive source)

theorem sourceHamiltonian_bound (source : ElectronicPropagationSource) :
    ‖hamiltonian source‖ ≤ (sourceOperatorBound source : ℝ) := by
  have entryBound := matrixOperator_norm_le_entrySum (activeMatrix source)
  change ‖hamiltonian source‖ ≤ _ at entryBound
  apply entryBound.trans
  have entries : (∑ i : Basis, ∑ j : Basis, ‖activeMatrix source i j‖) =
      (sourceEntryMagnitude source : ℝ) / 1000000000000000 := by
    simp only [sourceEntryMagnitude, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _membership
    apply Finset.sum_congr rfl
    intro j _membership
    norm_num [activeMatrix, norm_div, Complex.norm_intCast, Nat.cast_natAbs]
  rw [entries]
  simp only [sourceOperatorBound]
  push_cast
  gcongr
  linarith

/-- A nonzero source commutator now generates its responding rational time without an M premise. -/
theorem sourceNativeDuration_response (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0) :
    0 < sourceNativeDuration source ∧
      densityEvolution source (sourceNativeDuration source : ℝ) ≠ initialDensity source :=
  density_response_at_rationalDuration source i j nonzero
    (sourceOperatorBound source) (sourceOperatorBound_positive source)
    (sourceHamiltonian_bound source)

/-- Time translation is the same reversible conjugation of the already generated local response. -/
theorem densityEvolution_translate (source : ElectronicPropagationSource) (time step : ℝ) :
    densityEvolution source (time + step) =
      propagator source time * densityEvolution source step * propagator source (-time) := by
  unfold densityEvolution
  rw [propagator_add, show -(time + step) = -step + -time by ring, propagator_add]
  simp only [mul_assoc]

/-- The one source-generated rational duration remains a genuinely changing successor at every time. -/
theorem sourceNativeDuration_allTimes_response (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0) (time : ℝ) :
    densityEvolution source (time + (sourceNativeDuration source : ℝ)) ≠
      densityEvolution source time := by
  intro same
  rw [densityEvolution_translate] at same
  have cancelled := congrArg (fun observable : ElectronicOperator =>
    propagator source (-time) * observable * propagator source time) same
  have cancellation (observable : ElectronicOperator) :
      propagator source (-time) *
        (propagator source time * observable * propagator source (-time)) *
          propagator source time = observable := by
    simp only [← mul_assoc, propagator_neg_mul, one_mul]
    rw [mul_assoc, propagator_neg_mul, mul_one]
  change propagator source (-time) *
      (propagator source time * densityEvolution source (sourceNativeDuration source : ℝ) *
        propagator source (-time)) * propagator source time =
    propagator source (-time) *
      (propagator source time * initialDensity source * propagator source (-time)) *
        propagator source time at cancelled
  rw [cancellation, cancellation] at cancelled
  exact (sourceNativeDuration_response source i j nonzero).2 cancelled

end LAlanine40K2025.Propagation.Dynamics.NativeDuration
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
