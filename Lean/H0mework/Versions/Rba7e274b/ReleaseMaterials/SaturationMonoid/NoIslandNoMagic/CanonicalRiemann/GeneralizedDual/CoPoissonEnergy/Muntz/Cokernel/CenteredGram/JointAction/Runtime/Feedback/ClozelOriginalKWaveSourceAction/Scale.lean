import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Primitive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
local notation "q" => (1 / 4 : ℝ)

private theorem source_positive_power_scale (s : ℂ) (h y : ℝ) (positive : 0 < y) :
    ((Real.exp h * y : ℝ) : ℂ) ^ s = Complex.exp ((h : ℂ) * s) * (y : ℂ) ^ s := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Real.exp_pos h).le positive.le]
  have exponential : (Real.exp h : ℂ) ^ s = Complex.exp ((h : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero h)),
      ← Complex.ofReal_log (Real.exp_pos h).le, Real.log_exp]
  rw [exponential]

private theorem literal_source_band_scale (s : ℂ) (profile : ℝ → ℂ) (h : ℝ) (nonnegative : 0 ≤ h) :
    (∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
      (x : ℂ) ^ s * profile (Real.exp (-h) * x)) =
      -Complex.exp ((s + 1 / 2) * (h : ℂ)) *
        ∫ y : ℝ in (q * Real.exp (-h))..q, (y : ℂ) ^ s * profile y := by
  let f := fun x : ℝ => -(Real.exp (-h / 2) : ℂ) * (x : ℂ) ^ s * profile (Real.exp (-h) * x)
  have endpoints : Real.exp h * (q * Real.exp (-h)) = q := by
    rw [← mul_assoc, mul_comm (Real.exp h) q, mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, mul_one]
  have changed := intervalIntegral.smul_integral_comp_mul_left (f := f)
    (a := q * Real.exp (-h)) (b := q) (Real.exp h)
  rw [endpoints, mul_comm (Real.exp h) q] at changed
  have ordered : q * Real.exp (-h) ≤ q := by
    nlinarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)]
  have insideIntegral : (∫ y : ℝ in (q * Real.exp (-h))..q, f (Real.exp h * y)) =
      (-(Real.exp (-h / 2) : ℂ) * Complex.exp ((h : ℂ) * s)) *
        ∫ y : ℝ in (q * Real.exp (-h))..q, (y : ℂ) ^ s * profile y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y inside
    rw [uIcc_of_le ordered] at inside
    have positive : 0 < y := (mul_pos (by norm_num : (0 : ℝ) < q) (Real.exp_pos (-h))).trans_le inside.1
    have rescale : Real.exp (-h) * (Real.exp h * y) = y := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    dsimp only [f]
    rw [source_positive_power_scale s h y positive, rescale]
    ring
  rw [← changed, insideIntegral, Complex.real_smul, ← mul_assoc]
  have phase : (Real.exp h : ℂ) * (-(Real.exp (-h / 2) : ℂ) * Complex.exp ((h : ℂ) * s)) =
      -Complex.exp ((s + 1 / 2) * (h : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp]
    push_cast
    calc
      _ = -(Complex.exp (h : ℂ) * Complex.exp (-(h : ℂ) / 2) * Complex.exp ((h : ℂ) * s)) := by ring
      _ = -Complex.exp ((h : ℂ) + (-(h : ℂ) / 2) + (h : ℂ) * s) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
      _ = _ := by congr 2; ring
  rw [phase]

theorem actual_original_two_band_source_scalings (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    (∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
      (x : ℂ) ^ (coordinate.value - 1) * positionSource coordinate (Real.exp (-h) * x)) =
      -Complex.exp ((coordinate.value - 1 / 2) * (h : ℂ)) * actualPositionBandPrimitive coordinate h ∧
    (∫ x : ℝ in q..(q * Real.exp h), -(Real.exp (-h / 2) : ℂ) *
      (x : ℂ) ^ (-coordinate.value) * burnolRieszSingleFourierSourceRaw coordinate (Real.exp (-h) * x)) =
      -Complex.exp ((1 / 2 - coordinate.value) * (h : ℂ)) * actualFourierBandPrimitive coordinate h := by
  have position := literal_source_band_scale (coordinate.value - 1) (positionSource coordinate) h nonnegative
  have fourier := literal_source_band_scale (-coordinate.value) (burnolRieszSingleFourierSourceRaw coordinate) h nonnegative
  rw [show coordinate.value - 1 + 1 / 2 = coordinate.value - 1 / 2 by ring] at position
  rw [show -coordinate.value + 1 / 2 = 1 / 2 - coordinate.value by ring] at fourier
  exact ⟨position, fourier⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWaveSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
