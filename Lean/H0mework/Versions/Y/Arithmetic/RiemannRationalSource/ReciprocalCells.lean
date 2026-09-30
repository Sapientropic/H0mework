import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.IntegerCells

/-! The actual co-Poisson transpose sends the original integer flux to rational contacts. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open OriginalPaGreenContact
open scoped InnerProductSpace Topology
noncomputable section

def reciprocalSampleWave (s : ℂ) (n k : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * cellWave s k ((n : ℝ) / t)

def reciprocalSampleFlux (s : ℂ) (n k : ℕ) (t : ℝ) : ℂ :=
  -cellWave s k ((n : ℝ) / t) -
    cellFlux s k ((n : ℝ) / t) / (((n : ℝ) / t : ℝ) : ℂ)

private theorem cell_wave_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (k : ℕ) {x : ℝ} (positive : 0 < x) :
    HasDerivAt (cellWave coordinate.value k)
      (cellFlux coordinate.value k x / (x : ℂ) ^ 2) x := by
  simpa only [Complex.cpow_neg, Complex.cpow_two, div_eq_mul_inv, mul_comm] using
    OriginalPaGreenContact.cell_wave_derivative coordinate k positive

theorem reciprocal_sample_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (n k : ℕ) (positive : 0 < n) {t : ℝ} (tp : 0 < t) :
    HasDerivAt (reciprocalSampleWave coordinate.value n k)
      (reciprocalSampleFlux coordinate.value n k t / (t : ℂ) ^ 2) t := by
  have np : (0 : ℝ) < n := by exact_mod_cast positive
  have mapped : 0 < (n : ℝ) / t := div_pos np tp
  have xn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr tp.ne'
  have nn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr np.ne'
  have reciprocal := (Complex.ofRealCLM.hasDerivAt (x := t)).inv xn
  have argument := (hasDerivAt_const t (n : ℝ)).div (hasDerivAt_id t) tp.ne'
  have wave := (cell_wave_derivative coordinate k mapped).scomp t argument
  convert! reciprocal.mul wave using 1
  simp only [reciprocalSampleFlux, Pi.inv_apply, Complex.ofRealCLM_apply,
    Function.comp_apply, id_eq, real_smul, zero_mul, mul_one, zero_sub]
  push_cast
  field_simp
  ring

theorem reciprocal_sample_flux_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (n k : ℕ) (positive : 0 < n) {t : ℝ} (tp : 0 < t) :
    HasDerivAt (reciprocalSampleFlux coordinate.value n k)
      (-coordinate.value * (1 - coordinate.value) *
        reciprocalSampleWave coordinate.value n k t -
          (2 * coordinate.value - 1) / (t : ℂ)) t := by
  have np : (0 : ℝ) < n := by exact_mod_cast positive
  have mapped : 0 < (n : ℝ) / t := div_pos np tp
  have xn : (((n : ℝ) / t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr mapped.ne'
  have tn : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr tp.ne'
  have nn : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr np.ne'
  have w := cell_wave_derivative coordinate k mapped
  have f := (cell_flux_derivative coordinate k mapped).div
    (Complex.ofRealCLM.hasDerivAt (x := (n : ℝ) / t)) xn
  have native := w.neg.sub f
  have argument := (hasDerivAt_const t (n : ℝ)).div (hasDerivAt_id t) tp.ne'
  convert! native.scomp t argument using 1
  simp only [reciprocalSampleWave, Complex.ofRealCLM_apply,
    real_smul, id_eq, zero_mul, mul_one, zero_sub]
  push_cast
  field_simp
  ring

/-- Increasing the source coordinate crosses the physical integer cell in the reverse direction. -/
theorem reciprocal_sample_flux_contact (s : ℂ) (n k : ℕ) (positive : 0 < n) :
    reciprocalSampleFlux s n k ((n : ℝ) / (k + 1 : ℝ)) -
      reciprocalSampleFlux s n (k + 1) ((n : ℝ) / (k + 1 : ℝ)) =
        (2 * s - 1) / (k + 1 : ℂ) := by
  have nn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have kn : (k + 1 : ℝ) ≠ 0 := by positivity
  have point : (n : ℝ) / ((n : ℝ) / (k + 1 : ℝ)) = k + 1 := by
    field_simp
  simp only [reciprocalSampleFlux, point]
  rw [cell_wave_at_contact]
  have flux := cell_flux_contact s k
  push_cast
  calc
    _ = (cellFlux s (k + 1) (k + 1 : ℝ) - cellFlux s k (k + 1 : ℝ)) /
        (k + 1 : ℂ) := by ring
    _ = _ := by rw [flux]

/-- All original rational channels that meet at 1 retain their harmonic weights. -/
theorem reciprocal_sample_flux_integer_collision (s : ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (reciprocalSampleFlux s (k + 1) k 1 -
        reciprocalSampleFlux s (k + 1) (k + 1) 1)) =
      (2 * s - 1) * ∑ k ∈ Finset.range N, (k + 1 : ℂ)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have point : ((k + 1 : ℕ) : ℝ) / (k + 1 : ℝ) = 1 := by
    push_cast
    exact div_self (by positivity)
  have generated := reciprocal_sample_flux_contact s (k + 1) k (by omega)
  rw [point] at generated
  simpa only [div_eq_mul_inv] using generated

theorem second_channel_third_contact (s : ℂ) :
    reciprocalSampleFlux s 2 2 (2 / 3) - reciprocalSampleFlux s 2 3 (2 / 3) =
      (2 * s - 1) / 3 := by
  convert! reciprocal_sample_flux_contact s 2 2 (by omega) using 1 <;> norm_num

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
