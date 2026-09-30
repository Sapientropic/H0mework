import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.Correction

/-! The compact Green current reads the actual recovered source norm, pairing and Mellin boundary. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
private theorem even_window_integral (r : ℝ → ℝ) :
    (∫ x : ℝ, if (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then r |x| else 0) =
      2 * ∫ x : ℝ in (1 / 4 : ℝ)..4, r x := by
  rw [integral_comp_abs (f := fun t => if (1 / 4 : ℝ) ≤ t ∧ t < 4 then r t else 0)]
  have indicator : (fun x : ℝ => if (1 / 4 : ℝ) ≤ x ∧ x < 4 then r x else 0) =
      (Ico (1 / 4 : ℝ) 4).indicator r := by
    funext x
    simp only [Set.indicator_apply, mem_Ico]
  rw [indicator]
  rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (show Ico (1 / 4 : ℝ) 4 ⊆ Ioi 0 from
      fun _ hx => lt_of_lt_of_le (by norm_num) hx.1),
    integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

theorem burnolPaSourceCorrection_compact_tate (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p)) : ℝ → ℂ) =ᵐ[volume]
      fun x => if (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then
        (1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source |x| else 0 := by
  dsimp only
  rw [burnolPaSourceCorrection_compact_source coordinate source, map_smul]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (burnolTateReciprocalL2
    (burnolWeightedReciprocalStepSource (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
      (burnolFirstSourceCoefficientSlope coordinate source))),
    burnolFirstSourceTateWeighted_coe coordinate source] with x scaled read
  rw [scaled]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [read]
  simp only [mul_ite, mul_zero]

theorem burnolPaSourceCorrection_compact_norm (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    ‖burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p))‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ t : ℝ in (1 / 4 : ℝ)..4,
        ‖burnolFirstSourceCoefficient coordinate source t‖ ^ 2 := by
  dsimp only
  rw [burnolL2_norm_sq_eq_integral_norm_sq]
  calc
    _ = ∫ x : ℝ, if (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then
        (1 / 4 : ℝ) * ‖burnolFirstSourceCoefficient coordinate source |x|‖ ^ 2 else 0 := by
      apply integral_congr_ae
      filter_upwards [burnolPaSourceCorrection_compact_tate coordinate source] with x read
      rw [read]
      split_ifs <;> norm_num [norm_mul, mul_pow]
    _ = 2 * ∫ t : ℝ in (1 / 4 : ℝ)..4,
        (1 / 4 : ℝ) * ‖burnolFirstSourceCoefficient coordinate source t‖ ^ 2 :=
      even_window_integral (fun t => (1 / 4 : ℝ) * ‖burnolFirstSourceCoefficient coordinate source t‖ ^ 2)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

theorem burnolPaSourceCorrection_compact_pairing (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    (inner ℂ (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p)))
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 (p : BurnolPaAmbientCarrier)))).re =
        ∫ t : ℝ in (1 / 4 : ℝ)..4,
          (star (burnolFirstSourceCoefficient coordinate source t) * source.1 t).re := by
  dsimp only
  rw [burnolCompactPa_tate_source]
  let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
    simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
      burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
  let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p))
  calc
    _ = (∫ x : ℝ, inner ℂ (psi x) (source.1.toLp 2 volume x)).re := by rw [L2.inner_def]
    _ = ∫ x : ℝ, (inner ℂ (psi x) (source.1.toLp 2 volume x)).re :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) psi (source.1.toLp 2 volume))).symm
    _ = ∫ x : ℝ, if (1 / 4 : ℝ) ≤ |x| ∧ |x| < 4 then
        (1 / 2 : ℝ) * (star (burnolFirstSourceCoefficient coordinate source |x|) * source.1 |x|).re
      else 0 := by
      apply integral_congr_ae
      filter_upwards [burnolPaSourceCorrection_compact_tate coordinate source,
        source.1.coeFn_toLp 2 volume] with x read atX
      rw [read, atX]
      have absRead : source.1 x = source.1 |x| := by
        rcases le_total 0 x with positive | negative
        · rw [abs_of_nonneg positive]
        · rw [abs_of_nonpos negative, source.2.1]
      rw [absRead]
      split_ifs
      · simp
        ring
      · simp
    _ = 2 * ∫ t : ℝ in (1 / 4 : ℝ)..4,
        (1 / 2 : ℝ) * (star (burnolFirstSourceCoefficient coordinate source t) * source.1 t).re :=
      even_window_integral (fun t => (1 / 2 : ℝ) *
        (star (burnolFirstSourceCoefficient coordinate source t) * source.1 t).re)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

theorem burnolCompactPaSourceGreen (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p));
    -4 * (inner ℂ psi
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 (p : BurnolPaAmbientCarrier)))).re =
      (2 * coordinate.value.re - 1) * ‖psi‖ ^ 2 +
        (1 / 2 : ℝ) * ‖((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
          burnolPaResolventSourceCoefficient coordinate (p : BurnolPaAmbientCarrier)‖ ^ 2 := by
  dsimp only
  rw [burnolPaSourceCorrection_compact_pairing coordinate source, burnolPaSourceCorrection_compact_norm coordinate source]
  have energy := burnolCompactSourceGreen_identity coordinate source
  dsimp only at energy
  rw [burnolCompactSourceGreen_endpoint coordinate source] at energy
  have endpoint : ‖-(2 : ℂ) * ((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
      burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source)‖ ^ 2 =
      4 * ‖((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
        burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source)‖ ^ 2 := by
    rw [mul_assoc, norm_mul]
    norm_num [mul_pow]
  rw [endpoint] at energy
  linarith

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
