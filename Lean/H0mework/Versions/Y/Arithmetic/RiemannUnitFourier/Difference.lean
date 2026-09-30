import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.DyadicForward

/-! The same source shell generates the exact dyadic equation for the original Fourier/complementary Dirichlet difference. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem dyadicMean_read (s : ℂ) :
    burnolUnitDyadicMean s = ((2 : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have reciprocal : (1 / 2 : ℂ) ^ (s - 1) = (2 : ℂ) ^ (1 - s) := by
    rw [one_div]
    change ((2 : ℝ) : ℂ)⁻¹ ^ (s - 1) = _
    rw [Complex.inv_cpow_ofReal_nonneg (by norm_num), ← Complex.cpow_neg]
    congr 1
    ring
  unfold burnolUnitDyadicMean
  rw [reciprocal, show 1 - s = -(s - 1) by ring, div_neg]
  ring

private theorem complementary_dyadic (s : ℂ) (x : ℝ) (nonzero : x ≠ 0) :
    burnolUnitDyadicWaveRaw s x =
      burnolUnitTailDirichletRaw (1 - s) 1 x -
        (2 : ℂ) ^ (1 - s) * burnolUnitTailDirichletRaw (1 - s) 1 (2 * x) := by
  classical
  have positive := abs_pos.mpr nonzero
  have lower : 1 ≤ ⌈|x|⌉₊ := Nat.ceil_pos.mpr positive
  have upper : ⌈|x|⌉₊ ≤ ⌈2 * |x|⌉₊ := Nat.ceil_mono (by linarith)
  have splitSum := Finset.sum_Ico_consecutive (fun n : ℕ => (n : ℂ) ^ (-s)) lower upper
  have exponent : 1 - s - 1 = -s := by ring
  have scaling : (2 : ℂ) ^ (1 - s) * ((|2 * x| : ℝ) : ℂ) ^ (-(1 - s)) =
      ((|x| : ℝ) : ℂ) ^ (s - 1) := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) (abs_nonneg x)]
    norm_num only [Complex.ofReal_ofNat]
    rw [← mul_assoc, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show 1 - s + -(1 - s) = 0 by ring, Complex.cpow_zero, one_mul,
      show -(1 - s) = s - 1 by ring]
  unfold burnolUnitDyadicWaveRaw burnolUnitTailDirichletRaw
  rw [dyadicMean_read]
  simp only [Complex.ofReal_one, Complex.one_cpow, burnolUnitTailDirichletChannels,
    div_one, exponent, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  rw [mul_sub]
  have scaling' : (2 : ℂ) ^ (1 - s) * (↑(2 * |x|) : ℂ) ^ (-(1 - s)) =
      (↑|x| : ℂ) ^ (s - 1) := by simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using scaling
  rw [← mul_assoc ((2 : ℂ) ^ (1 - s)), scaling',
    show -(1 - s) = s - 1 by ring, ← splitSum]
  unfold burnolUnitDyadicChannels
  ring

theorem burnolUnitFourierRadiusTwo_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (burnolUnitTailResponse coordinate 2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (2 : ℂ) ^ (1 - coordinate.value) *
        fourierL2 (burnolUnitTailResponse coordinate 1) (2 * x) := by
  let character := fullMellinTranslationCharacter coordinate.value (-Real.log 2)
  have action := congrArg fourierL2
    (burnolUnitTailResponse_radius_dilation coordinate 1 (by norm_num) (by norm_num)
      (-Real.log 2) (by norm_num [Real.exp_log]))
  have radius : (1 : ℝ) * Real.exp (Real.log 2) = 2 := by
    rw [one_mul, Real.exp_log (by norm_num)]
  rw [fourierL2_burnolMultiplicativeDilation, neg_neg, map_smul, radius] at action
  have factor : character * (2 : ℂ) ^ (1 - coordinate.value) =
      (Real.exp (Real.log 2 / 2) : ℂ) := by
    unfold character fullMellinTranslationCharacter
    rw [Complex.cpow_def_of_ne_zero (by norm_num),
      show Complex.log (2 : ℂ) = (Real.log 2 : ℂ) from
        (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm,
      ← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have characterNe : character ≠ 0 := Complex.exp_ne_zero _
  filter_upwards [Lp.coeFn_smul character (fourierL2 (burnolUnitTailResponse coordinate 2)),
    burnolMultiplicativeDilation_coeFn (Real.log 2) (fourierL2 (burnolUnitTailResponse coordinate 1))]
    with x scalarAt dilationAt
  have actionAt := congrArg (fun value : BurnolL2 => value x) action
  rw [scalarAt] at actionAt
  change burnolMultiplicativeDilation (Real.log 2) (fourierL2 (burnolUnitTailResponse coordinate 1)) x =
      character * fourierL2 (burnolUnitTailResponse coordinate 2) x at actionAt
  rw [dilationAt] at actionAt
  unfold burnolL2RawNormalizedDilation at actionAt
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at actionAt
  apply mul_left_cancel₀ characterNe
  rw [← mul_assoc, factor]
  exact actionAt.symm

theorem burnolUnitFourierComplement_dyadic (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume,
      fourierL2 (burnolUnitTailResponse coordinate 1) x +
          burnolUnitTailDirichletRaw (1 - coordinate.value) 1 x =
        (2 : ℂ) ^ (1 - coordinate.value) *
          (fourierL2 (burnolUnitTailResponse coordinate 1) (2 * x) +
            burnolUnitTailDirichletRaw (1 - coordinate.value) 1 (2 * x)) := by
  have shell := burnolUnitDyadicFourierShell_coeFn coordinate
  rw [map_sub] at shell
  filter_upwards [shell, Lp.coeFn_sub (fourierL2 (burnolUnitTailResponse coordinate 2))
    (fourierL2 (burnolUnitTailResponse coordinate 1)), burnolUnitFourierRadiusTwo_coeFn coordinate, volume.ae_ne (0 : ℝ)]
    with x shellAt subAt radiusAt nonzero
  rw [subAt] at shellAt
  change fourierL2 (burnolUnitTailResponse coordinate 2) x -
    fourierL2 (burnolUnitTailResponse coordinate 1) x = burnolUnitDyadicWaveRaw coordinate.value x at shellAt
  rw [radiusAt, complementary_dyadic coordinate.value x nonzero] at shellAt
  linear_combination -shellAt

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
