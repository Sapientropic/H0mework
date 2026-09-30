import H0mework.Versions.X.NavierStokes.UnheatedWriterPair.Kernel

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadKernel

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open NativeUnheatedStressPairEvolution NativeUnheatedPairInverseKernel NativeCompleteStressCarrier

noncomputable section
variable {nu : Viscosity}

def triadDecay (nu : Viscosity) (a b c : IntegerWavevector) : ℝ :=
  nu.coeff * (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c)

theorem multiplier_nonnegative (wave : IntegerWavevector) : 0 ≤ integerWaveViscousMultiplier wave :=
  mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)

theorem triad_nonnegative (a b c : IntegerWavevector) : 0 ≤ triadDecay nu a b c :=
  mul_nonneg nu.coeff_pos.le (add_nonneg (add_nonneg (multiplier_nonnegative a) (multiplier_nonnegative b)) (multiplier_nonnegative c))

theorem output_multiplier (a b : IntegerWavevector) :
    integerWaveViscousMultiplier (a+b) ≤ 2 * (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b) := by
  have row (coordinate : ThreeDimensionalPeriodicCoarseFilterCore.Coordinate) :
      ((a coordinate : ℝ) + (b coordinate : ℝ)) ^ 2 ≤ 2 * ((a coordinate : ℝ)^2 + (b coordinate : ℝ)^2) := by
    nlinarith [sq_nonneg ((a coordinate : ℝ) - (b coordinate : ℝ))]
  have paid := Finset.sum_le_sum (s := Finset.univ) (fun coordinate _ => row coordinate)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at paid
  unfold integerWaveViscousMultiplier integerWaveNormSq
  simp only [Pi.add_apply, Int.cast_add]
  nlinarith [mul_le_mul_of_nonneg_left paid (sq_nonneg (2*Real.pi))]

theorem derivative_numerator (a b c slot : IntegerWavevector)
    (inSlot : slot = a ∨ slot = b ∨ slot = c) :
    Real.sqrt (integerWaveViscousMultiplier (a+b)) * Real.sqrt (integerWaveViscousMultiplier slot) ≤
      2 * (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c) := by
  have slotBound : integerWaveViscousMultiplier slot ≤
      integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c := by
    rcases inSlot with same | same | same <;> rw [same] <;>
      linarith [multiplier_nonnegative a, multiplier_nonnegative b, multiplier_nonnegative c]
  have rootP := Real.sq_sqrt (multiplier_nonnegative (a+b))
  have rootSlot := Real.sq_sqrt (multiplier_nonnegative slot)
  nlinarith [output_multiplier a b, multiplier_nonnegative c,
    sq_nonneg (Real.sqrt (integerWaveViscousMultiplier (a+b)) - Real.sqrt (integerWaveViscousMultiplier slot))]

def normalizedQuartic (nu : Viscosity) (a b c slot : IntegerWavevector) : ℝ :=
  Real.sqrt (integerWaveViscousMultiplier (a+b)) * Real.sqrt (integerWaveViscousMultiplier slot) *
    (decay nu (a+b) c)⁻¹ * (triadDecay nu a b c)⁻¹

theorem normalized_quartic_bound (a b c slot : IntegerWavevector)
    (inSlot : slot = a ∨ slot = b ∨ slot = c) :
    normalizedQuartic nu a b c slot ≤ (2 / nu.coeff) * (decay nu (a+b) c)⁻¹ := by
  let numerator := Real.sqrt (integerWaveViscousMultiplier (a+b)) * Real.sqrt (integerWaveViscousMultiplier slot)
  have dominated : numerator ≤ (2 / nu.coeff) * triadDecay nu a b c := by
    have same : (2 / nu.coeff) * triadDecay nu a b c =
        2 * (integerWaveViscousMultiplier a + integerWaveViscousMultiplier b + integerWaveViscousMultiplier c) := by
      unfold triadDecay
      field_simp [nu.coeff_pos.ne']
    rw [same]
    exact derivative_numerator a b c slot inSlot
  have cancelled : numerator * (triadDecay nu a b c)⁻¹ ≤ 2 / nu.coeff := by
    by_cases zero : triadDecay nu a b c = 0
    · rw [zero, inv_zero, mul_zero]
      positivity [nu.coeff_pos]
    · have bounded := mul_le_mul_of_nonneg_right dominated (inv_nonneg.mpr (triad_nonnegative (nu := nu) a b c))
      simpa only [mul_assoc, mul_inv_cancel₀ zero, mul_one] using bounded
  have denom0 : 0 ≤ decay nu (a+b) c :=
    mul_nonneg nu.coeff_pos.le (add_nonneg (multiplier_nonnegative (a+b)) (multiplier_nonnegative c))
  have paid := mul_le_mul_of_nonneg_right cancelled (inv_nonneg.mpr denom0)
  simpa only [normalizedQuartic, numerator, mul_assoc, mul_left_comm, mul_comm] using paid

theorem normalized_quartic_output (a b c slot : IntegerWavevector)
    (inSlot : slot = a ∨ slot = b ∨ slot = c) :
    normalizedQuartic nu a b c slot ≤ (2 / nu.coeff) * (scale nu)⁻¹ * weight (a+b+c) :=
  (normalized_quartic_bound a b c slot inSlot).trans
    ((mul_le_mul_of_nonneg_left (inverse_bound (nu := nu) (a+b) c) (by positivity [nu.coeff_pos])).trans_eq (by ring))

theorem inverse_internal_bound (p c : IntegerWavevector) :
    (decay nu p c)⁻¹ ≤ (nu.coeff * (2 * Real.pi)^2)⁻¹ * weight c := by
  by_cases cZero : c = 0
  · subst c
    by_cases pZero : p = 0
    · subst p
      simp only [decay, integerWaveViscousMultiplier, integerWaveNormSq, Pi.zero_apply,
        Int.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero,
        add_zero, inv_zero, weight, if_true, mul_one]
      positivity [nu.coeff_pos]
    · have lower := decay_floor (nu := nu) p 0 (Or.inl pZero)
      have bounded := one_div_le_one_div_of_le (by positivity [nu.coeff_pos] : 0 < nu.coeff * (2*Real.pi)^2) lower
      simpa only [weight, if_true, one_div, mul_one] using bounded
  · have positive : 0 < nu.coeff * integerWaveViscousMultiplier c :=
      mul_pos nu.coeff_pos (mul_pos (sq_pos_of_pos (by positivity)) (integerWaveNormSq_pos cZero))
    have lower : nu.coeff * integerWaveViscousMultiplier c ≤ decay nu p c := by
      unfold decay
      nlinarith [multiplier_nonnegative p, nu.coeff_pos]
    have bounded := one_div_le_one_div_of_le positive lower
    simpa only [weight, if_neg cZero, integerWaveViscousMultiplier, one_div, mul_inv_rev, mul_comm, mul_assoc] using bounded

theorem normalized_quartic_internal (a b c slot : IntegerWavevector)
    (inSlot : slot = a ∨ slot = b ∨ slot = c) :
    normalizedQuartic nu a b c slot ≤
      ((2 / nu.coeff) * (nu.coeff * (2 * Real.pi)^2)⁻¹) * weight c :=
  (normalized_quartic_bound a b c slot inSlot).trans
    ((mul_le_mul_of_nonneg_left (inverse_internal_bound (nu := nu) (a+b) c)
      (by positivity [nu.coeff_pos])).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadKernel
