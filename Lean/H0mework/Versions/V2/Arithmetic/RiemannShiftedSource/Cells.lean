import H0mework.Versions.V2.Arithmetic.RiemannRationalSource.SourceCurrent

/-! The original half-density dilation generates its displaced reciprocal flux. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter OriginalPaGreenContact
open scoped InnerProductSpace Topology
noncomputable section

def shiftedReciprocalWave (s : ℂ) (h : ℝ) (n k : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * (t : ℂ)⁻¹ *
    cellWave s k (Real.exp h * n / t)

def shiftedReciprocalFlux (s : ℂ) (h : ℝ) (n k : ℕ) (t : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) *
    (-cellWave s k (Real.exp h * n / t) -
      cellFlux s k (Real.exp h * n / t) / ((Real.exp h * n / t : ℝ) : ℂ))

private theorem shifted_cell_wave_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) {x : ℝ} (positive : 0 < x) :
    HasDerivAt (cellWave coordinate.value k) (cellFlux coordinate.value k x / (x : ℂ) ^ 2) x := by
  simpa only [Complex.cpow_neg, Complex.cpow_two, div_eq_mul_inv, mul_comm] using
    OriginalPaGreenContact.cell_wave_derivative coordinate k positive

theorem shiftedReciprocalWave_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (n k : ℕ) (positive : 0 < n) {t : ℝ} (tp : 0 < t) :
    HasDerivAt (shiftedReciprocalWave coordinate.value h n k)
      (shiftedReciprocalFlux coordinate.value h n k t / (t : ℂ) ^ 2) t := by
  have np : (0 : ℝ) < n := by exact_mod_cast positive
  have mapped : 0 < Real.exp h * n / t := div_pos (mul_pos (Real.exp_pos h) np) tp
  have tn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr tp.ne'
  have nn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr np.ne'
  have hn : (Real.exp h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)
  have reciprocal := (Complex.ofRealCLM.hasDerivAt (x := t)).inv tn
  have argument := (hasDerivAt_const t (Real.exp h * n : ℝ)).div (hasDerivAt_id t) tp.ne'
  have wave := (shifted_cell_wave_derivative coordinate k mapped).scomp t argument
  convert! (reciprocal.mul wave).const_mul (Real.exp (h / 2) : ℂ) using 1
  · funext u
    dsimp only [shiftedReciprocalWave, Pi.mul_apply, Pi.inv_apply,
      Function.comp_apply, Complex.ofRealCLM_apply]
    ring
  · simp only [shiftedReciprocalFlux, Pi.inv_apply, Complex.ofRealCLM_apply,
      Function.comp_apply, id_eq, real_smul, zero_mul, mul_one, zero_sub]
    push_cast
    field_simp
    ring

theorem shiftedReciprocalFlux_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (n k : ℕ) (positive : 0 < n) {t : ℝ} (tp : 0 < t) :
    HasDerivAt (shiftedReciprocalFlux coordinate.value h n k)
      (-coordinate.value * (1 - coordinate.value) * shiftedReciprocalWave coordinate.value h n k t -
        (Real.exp (h / 2) : ℂ) * (2 * coordinate.value - 1) / (t : ℂ)) t := by
  have np : (0 : ℝ) < n := by exact_mod_cast positive
  have mapped : 0 < Real.exp h * n / t := div_pos (mul_pos (Real.exp_pos h) np) tp
  have xn : ((Real.exp h * n / t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr mapped.ne'
  have tn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr tp.ne'
  have nn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr np.ne'
  have hn : (Real.exp h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)
  have wave := shifted_cell_wave_derivative coordinate k mapped
  have flux := (cell_flux_derivative coordinate k mapped).div
    (Complex.ofRealCLM.hasDerivAt (x := Real.exp h * n / t)) xn
  have native := wave.neg.sub flux
  have argument := (hasDerivAt_const t (Real.exp h * n : ℝ)).div (hasDerivAt_id t) tp.ne'
  convert! (native.scomp t argument).const_mul (Real.exp (h / 2) : ℂ) using 1
  simp only [shiftedReciprocalWave, Complex.ofRealCLM_apply,
    real_smul, id_eq, zero_mul, mul_one, zero_sub]
  push_cast
  field_simp
  ring

theorem shiftedReciprocalFlux_contact (s : ℂ) (h : ℝ) (n k : ℕ) (positive : 0 < n) :
    shiftedReciprocalFlux s h n k (Real.exp h * n / (k + 1 : ℝ)) -
      shiftedReciprocalFlux s h n (k + 1) (Real.exp h * n / (k + 1 : ℝ)) =
        (Real.exp (h / 2) : ℂ) * (2 * s - 1) / (k + 1 : ℂ) := by
  have nn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have point : Real.exp h * n / (Real.exp h * n / (k + 1 : ℝ)) = k + 1 := by
    field_simp
  simp only [shiftedReciprocalFlux, point]
  rw [cell_wave_at_contact]
  have flux := cell_flux_contact s k
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  linear_combination (Real.exp (h / 2) : ℂ) / (k + 1 : ℂ) * flux

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
