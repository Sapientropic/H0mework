import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.SecondContact
import H0mework.Versions.Y.Arithmetic.RiemannRationalSource.SecondPrimitive

/-! Same-source contact and strong-action coordinates of the original Pa correction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem compact_source_reciprocal (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditivePhysicalState source) {t : ℝ} (positive : 0 < t) :
    source.1 t⁻¹ = (t : ℂ) * source.1 t := by
  have fourier : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
    apply Subtype.ext
    exact burnolCompactFourierL2_eq_reciprocalL2 source
  have same := congrArg (fun p : BurnolPaAmbientCarrier => burnolTateReciprocalL2 (burnolMobiusSourceL2 p))
    (fourier.symm.trans fixed)
  rw [burnolCompactPa_tate_source, burnolCompactPa_tate_source] at same
  have sources := SchwartzMap.injective_toLp 2 volume same
  have point := congrArg (fun f : SchwartzMap ℝ ℂ => f t) sources
  change burnolCompactTateReciprocalSchwartz source t = source.1 t at point
  rw [burnolCompactTateReciprocalSchwartz_apply, burnolCompactAdditiveSource,
    if_neg positive.ne', abs_of_pos positive] at point
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  field_simp [nonzero] at point
  simpa only [one_div] using point

def tatePrimitive (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (coordinate.value - 1) * ((1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source t⁻¹) +
    burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source)

theorem reciprocal_inside {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    t⁻¹ ∈ Icc (1 / 4 : ℝ) 4 := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  constructor
  · simpa using (inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive).mpr inside.2
  · simpa using (inv_le_inv₀ positive (by norm_num : (0 : ℝ) < 1 / 4)).mpr inside.1

theorem tatePrimitive_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditivePhysicalState source) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    HasDerivAt (tatePrimitive coordinate source)
      (-(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) * source.1 t) t := by
  let z := coordinate.value
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have exponent : z - 1 ≠ 0 := by
    intro zero
    have re := congrArg Complex.re zero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at re
    linarith [coordinate.belowOne]
  have inner := reciprocal_inside inside
  have euler := burnolFirstSourceCoefficient_euler coordinate source inner
  rw [Complex.ofReal_inv, compact_source_reciprocal source fixed positive] at euler
  field_simp [nonzero] at euler
  simp only [one_div] at euler
  have power := hasDerivAt_ofReal_cpow_const positive.ne' exponent
  have reciprocal := (hasDerivAt_id t).inv positive.ne'
  have coefficient := ((burnolFirstSourceCoefficient_hasDerivAt coordinate source inner).scomp t reciprocal).const_mul (1 / 2 : ℂ)
  have generated := (power.mul coefficient).add_const
    (burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source))
  have shift : (t : ℂ) * (t : ℂ) ^ (z - 1 - 1) = (t : ℂ) ^ (z - 1) := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  convert! generated using 1
  simp only [id_eq, one_div, real_smul, Function.comp_apply]
  push_cast
  rw [euler, ← shift]
  dsimp only [z]
  field_simp [nonzero]
  ring

theorem tatePrimitive_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : tatePrimitive coordinate source 4 = 0 := by
  unfold tatePrimitive
  simp only [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
  rw [burnolCompactSourceGreen_endpoint]
  have power : (4 : ℂ) ^ (coordinate.value - 1) *
      (((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1)) = 1 := by
    have product := (Complex.mul_cpow_ofReal_nonneg (a := (4 : ℝ)) (b := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) (coordinate.value - 1)).symm
    norm_num at product
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using product
  calc
    _ = (1 - (4 : ℂ) ^ (coordinate.value - 1) * (((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1))) *
        burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source) := by
      norm_num only [Complex.ofReal_ofNat]
      ring
    _ = 0 := by rw [power]; ring

theorem tatePrimitive_eq_upperMoment (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditivePhysicalState source) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    tatePrimitive coordinate source t = 2 * finiteMoment (coordinate.value - 1) source t := by
  have derivative (u : ℝ) (hu : u ∈ uIcc t 4) :
      HasDerivAt (fun x => tatePrimitive coordinate source x - 2 * finiteMoment (coordinate.value - 1) source x)
        0 u := by
    have interval : t ≤ u ∧ u ≤ 4 := by simpa only [uIcc_of_le inside.2, mem_Icc] using hu
    have inRange : u ∈ Icc (1 / 4 : ℝ) 4 := ⟨inside.1.trans interval.1, interval.2⟩
    convert! (tatePrimitive_derivative coordinate source fixed inRange).sub
      ((finiteMoment_derivative (coordinate.value - 1) source inRange.1).const_mul 2) using 1
    ring
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative
    (intervalIntegrable_const (c := (0 : ℂ)))
  rw [intervalIntegral.integral_zero, tatePrimitive_outer] at generated
  have upper : finiteMoment (coordinate.value - 1) source 4 = 0 := by simp [finiteMoment]
  rw [upper] at generated
  linear_combination generated

theorem firstCoefficient_eq_finiteMoment (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    (1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source t =
      -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) * finiteMoment (-coordinate.value) source t := by
  have density (u : ℝ) : burnolFirstSourceDensity coordinate source u =
      (2 : ℂ) * ((((max (1 / 8 : ℝ) u) : ℝ) : ℂ) ^ (-coordinate.value) * source.1 u) := by
    unfold burnolFirstSourceDensity
    ring
  unfold burnolFirstSourceCoefficient finiteMoment
  simp_rw [density, intervalIntegral.integral_const_mul]
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith)]
  ring

theorem secondContact_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius (burnolCompactAdditivePhysicalState source) =
      burnolCompactAdditivePhysicalState source) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    secondContact coordinate t (lt_of_lt_of_le (by norm_num) inside.1)
      (burnolCompactAdditivePhysicalState source) = secondCoefficient coordinate source t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    (burnolPaSourceContact coordinate t positive (burnolCompactAdditivePhysicalState source) +
      (t : ℂ)⁻¹ * burnolPaSourceContact coordinate t⁻¹ (inv_pos.mpr positive) (burnolCompactAdditivePhysicalState source) +
      (t : ℂ) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source)) = _
  rw [burnolPaSourceContact_compact coordinate source inside,
    burnolPaSourceContact_compact coordinate source (reciprocal_inside inside)]
  have power : (t : ℂ) ^ (-coordinate.value) * (t : ℂ) ^ (coordinate.value - 1) = (t : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ nonzero, show -coordinate.value + (coordinate.value - 1) = -1 by ring,
      Complex.cpow_neg_one]
  calc
    _ = (2 / (2 * coordinate.value - 1) : ℂ) *
      ((1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source t +
        (t : ℂ) ^ (-coordinate.value) * tatePrimitive coordinate source t) := by
      unfold tatePrimitive
      rw [← power]
      ring
    _ = _ := by
      rw [firstCoefficient_eq_finiteMoment coordinate source inside.1,
        tatePrimitive_eq_upperMoment coordinate source fixed inside]
      unfold secondCoefficient
      ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
