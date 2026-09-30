import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Output

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadDepthKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeUnheatedTriadKernel NativeUnheatedStressPairEvolution NativeUnheatedPairInverseKernel
open NativeCompleteStressCarrier
noncomputable section
variable {nu : Viscosity}

def floor (nu : Viscosity) : ℝ := nu.coeff*(2*Real.pi)^2

theorem floor_positive (nu : Viscosity) : 0 < floor nu := by unfold floor; positivity [nu.coeff_pos]

theorem decay_floor (a b c : IntegerWavevector) (nonzero : triadDecay nu a b c ≠ 0) :
    floor nu ≤ triadDecay nu a b c := by
  by_cases left : a = 0 ∧ b = 0
  · rcases left with ⟨rfl, rfl⟩
    have cNonzero : c ≠ 0 := by
      intro zero
      subst c
      simp [triadDecay, integerWaveViscousMultiplier, integerWaveNormSq] at nonzero
    have paid := mul_le_mul_of_nonneg_left (one_le_integerWaveNormSq c cNonzero)
      (mul_nonneg nu.coeff_pos.le (sq_nonneg (2*Real.pi)))
    simpa [floor, triadDecay, integerWaveViscousMultiplier, integerWaveNormSq, mul_assoc] using paid
  · have pair : a ≠ 0 ∨ b ≠ 0 := not_and_or.mp left
    have paid := NativeUnheatedPairInverseKernel.decay_floor (nu := nu) a b pair
    have extra := multiplier_nonnegative c
    unfold floor triadDecay
    unfold decay at paid
    nlinarith [nu.coeff_pos]

def inverseCap (nu : Viscosity) : ℝ := 3*(floor nu)⁻¹

theorem inverseCap_nonnegative (nu : Viscosity) : 0 ≤ inverseCap nu := by
  unfold inverseCap
  positivity [floor_positive nu]

theorem inverse_uniform (a b c : IntegerWavevector) :
    (triadDecay nu a b c)⁻¹ ≤ (floor nu)⁻¹ := by
  by_cases zero : triadDecay nu a b c = 0
  · rw [zero, inv_zero]
    exact inv_nonneg.mpr (floor_positive nu).le
  · simpa only [one_div] using one_div_le_one_div_of_le (floor_positive nu) (decay_floor a b c zero)

theorem inverse_output (a b c : IntegerWavevector) :
    (triadDecay nu a b c)⁻¹ ≤ inverseCap nu*weight (a+b+c) := by
  by_cases zero : a+b+c = 0
  · rw [weight, if_pos zero, mul_one]
    exact (inverse_uniform a b c).trans (by
      unfold inverseCap
      linarith [inv_nonneg.mpr (floor_positive nu).le])
  · have root := NativeUnheatedTriadOutput.extract (nu := nu) a b c
    have positive := integerWaveNormSq_pos zero
    have multiplier : 0 < integerWaveViscousMultiplier (a+b+c) := mul_pos (by positivity) positive
    have paid : (triadDecay nu a b c)⁻¹ ≤ (3/nu.coeff)/integerWaveViscousMultiplier (a+b+c) := by
      apply (le_div_iff₀ multiplier).mpr
      rw [mul_comm]
      exact root
    exact paid.trans_eq (by
      unfold inverseCap floor weight integerWaveViscousMultiplier
      rw [if_neg zero]
      field_simp [nu.coeff_pos.ne', positive.ne'])

def charge (nu : Viscosity) (depth : ℕ) (wave : IntegerWavevector)
    (indices : IntegerWavevector × IntegerWavevector) : ℝ :=
  (triadDecay nu indices.2 (wave-indices.1-indices.2) indices.1)⁻¹^depth

theorem charge_nonnegative (depth : ℕ) (wave : IntegerWavevector) (indices : IntegerWavevector × IntegerWavevector) :
    0 ≤ charge nu depth wave indices := pow_nonneg (inv_nonneg.mpr (triad_nonnegative _ _ _)) depth

theorem charge_output (depth : ℕ) (wave : IntegerWavevector) (indices : IntegerWavevector × IntegerWavevector) :
    charge nu depth wave indices ≤ inverseCap nu^depth*weight wave^depth := by
  have same : indices.2+(wave-indices.1-indices.2)+indices.1 = wave := by abel
  have paid := pow_le_pow_left₀ (inv_nonneg.mpr (triad_nonnegative (nu := nu) indices.2 _ indices.1))
    (inverse_output (nu := nu) indices.2 (wave-indices.1-indices.2) indices.1) depth
  simpa only [charge, mul_pow, same] using paid

theorem charge_uniform (depth : ℕ) (wave : IntegerWavevector) (indices : IntegerWavevector × IntegerWavevector) :
    charge nu depth wave indices ≤ (floor nu)⁻¹^depth :=
  pow_le_pow_left₀ (inv_nonneg.mpr (triad_nonnegative _ _ _)) (inverse_uniform _ _ _) depth

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadDepthKernel
