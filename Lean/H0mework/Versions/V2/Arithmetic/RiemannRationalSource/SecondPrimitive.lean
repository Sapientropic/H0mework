import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.Euler

/-! The actual compact source generates its second primitive, Euler flux and both outer boundary values. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finiteMoment (exponent : ℂ) (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  ∫ u : ℝ in t..4, (((max (1 / 8 : ℝ) u) : ℝ) : ℂ) ^ exponent * source.1 u

theorem finiteMoment_derivative (exponent : ℂ) (source : burnolCompactAnnulusSource)
    {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    HasDerivAt (finiteMoment exponent source) (-(t : ℂ) ^ exponent * source.1 t) t := by
  have base : Continuous (fun u : ℝ => (((max (1 / 8 : ℝ) u) : ℝ) : ℂ)) := by fun_prop
  have powered : Continuous (fun u : ℝ => (((max (1 / 8 : ℝ) u) : ℝ) : ℂ) ^ exponent) :=
    continuousOn_univ.mp (base.continuousOn.cpow_const (fun u _ =>
    Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))))
  have regular := powered.mul source.1.continuous
  have generated := intervalIntegral.integral_hasDerivAt_left
    (regular.intervalIntegrable t 4) regular.stronglyMeasurable.stronglyMeasurableAtFilter regular.continuousAt
  convert! generated using 1
  simp only [Pi.mul_apply]
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith)]
  ring

def secondCoefficient (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  4 / (2 * coordinate.value - 1) *
    ((t : ℂ) ^ (-coordinate.value) * finiteMoment (coordinate.value - 1) source t -
      (t : ℂ) ^ (coordinate.value - 1) * finiteMoment (-coordinate.value) source t)

def secondFlux (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  4 / (2 * coordinate.value - 1) *
    (-coordinate.value * (t : ℂ) ^ (1 - coordinate.value) * finiteMoment (coordinate.value - 1) source t -
      (coordinate.value - 1) * (t : ℂ) ^ coordinate.value * finiteMoment (-coordinate.value) source t)

private theorem coordinate_nonzero (coordinate : BurnolCompletedMellinCoordinate) : coordinate.value ≠ 0 := by
  intro zero
  have re := congrArg Complex.re zero
  simp only [Complex.zero_re] at re
  linarith [coordinate.rightHalf]

private theorem coordinate_sub_one_nonzero (coordinate : BurnolCompletedMellinCoordinate) : coordinate.value - 1 ≠ 0 := by
  intro zero
  have re := congrArg Complex.re zero
  simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at re
  linarith [coordinate.belowOne]

theorem secondCoefficient_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    HasDerivAt (secondCoefficient coordinate source)
      ((t : ℂ) ^ (-2 : ℂ) * secondFlux coordinate source t) t := by
  let z := coordinate.value
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) lower
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have left := (hasDerivAt_ofReal_cpow_const positive.ne' (neg_ne_zero.mpr (coordinate_nonzero coordinate))).mul
    (finiteMoment_derivative (z - 1) source lower)
  have right := (hasDerivAt_ofReal_cpow_const positive.ne' (coordinate_sub_one_nonzero coordinate)).mul
    (finiteMoment_derivative (-z) source lower)
  have powLeft : (t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ (1 - z) = (t : ℂ) ^ (-z - 1) := by
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  have powRight : (t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ z = (t : ℂ) ^ (z - 1 - 1) := by
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  convert! (left.sub right).const_mul (4 / (2 * z - 1) : ℂ) using 1
  unfold secondFlux
  calc
    _ = 4 / (2 * z - 1) *
      (-z * ((t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ (1 - z)) * finiteMoment (z - 1) source t -
       (z - 1) * ((t : ℂ) ^ (-2 : ℂ) * (t : ℂ) ^ z) * finiteMoment (-z) source t) := by ring
    _ = _ := by rw [powLeft, powRight]; ring

theorem secondFlux_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    HasDerivAt (secondFlux coordinate source)
      (4 * source.1 t - coordinate.value * (1 - coordinate.value) * secondCoefficient coordinate source t) t := by
  let z := coordinate.value
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) lower
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have oneMinus : 1 - z ≠ 0 := by
    have same : 1 - z = -(z - 1) := by ring
    rw [same]
    exact neg_ne_zero.mpr (coordinate_sub_one_nonzero coordinate)
  have delta : 2 * z - 1 ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    norm_num [Complex.sub_re, Complex.mul_re] at re
    linarith [coordinate.rightHalf]
  have left := ((hasDerivAt_ofReal_cpow_const positive.ne' oneMinus).const_mul (-z)).mul
    (finiteMoment_derivative (z - 1) source lower)
  have right := ((hasDerivAt_ofReal_cpow_const positive.ne' (coordinate_nonzero coordinate)).const_mul (z - 1)).mul
    (finiteMoment_derivative (-z) source lower)
  have powLeft : (t : ℂ) ^ (1 - z) * (t : ℂ) ^ (z - 1) = 1 := by
    rw [← Complex.cpow_add _ _ nonzero, show 1 - z + (z - 1) = 0 by ring, Complex.cpow_zero]
  have powRight : (t : ℂ) ^ z * (t : ℂ) ^ (-z) = 1 := by
    rw [← Complex.cpow_add _ _ nonzero, add_neg_cancel, Complex.cpow_zero]
  convert! (left.sub right).const_mul (4 / (2 * z - 1) : ℂ) using 1
  change 4 * source.1 t - z * (1 - z) * secondCoefficient coordinate source t = _
  unfold secondCoefficient
  rw [show 1 - z - 1 = -z by ring]
  calc
    _ = 4 / (2 * z - 1) *
      ((-z * ((1 - z) * (t : ℂ) ^ (-z))) * finiteMoment (z - 1) source t +
       z * ((t : ℂ) ^ (1 - z) * (t : ℂ) ^ (z - 1)) * source.1 t -
       ((z - 1) * (z * (t : ℂ) ^ (z - 1))) * finiteMoment (-z) source t +
       (z - 1) * ((t : ℂ) ^ z * (t : ℂ) ^ (-z)) * source.1 t) := by
      rw [powLeft, powRight]
      dsimp only [z] at delta ⊢
      field_simp [delta, show coordinate.value * 2 - 1 ≠ 0 by simpa only [mul_comm] using delta]
      ring
    _ = _ := by dsimp only [z]; ring

theorem secondCoefficient_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : secondCoefficient coordinate source 4 = 0 := by
  simp [secondCoefficient, finiteMoment]

theorem secondFlux_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : secondFlux coordinate source 4 = 0 := by
  simp [secondFlux, finiteMoment]

theorem secondCoefficient_outer_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : HasDerivAt (secondCoefficient coordinate source) 0 4 := by
  simpa only [secondFlux_outer, mul_zero] using
    secondCoefficient_derivative coordinate source (by norm_num : (1 / 4 : ℝ) ≤ 4)

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
