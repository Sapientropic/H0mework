import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.AnnulusChange
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.ColumnMass
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.Band

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Classical Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszSource OriginalRieszFiniteColumns

noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "bRaw" => burnolRieszSingleFourierSourceRaw

private theorem extension_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (bRaw coordinate) := by
  have original := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), original] with x extended raw
  rw [extended]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, raw inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private theorem column_scaled_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) :
    (fun y : ℝ => fourierColumn coordinate shift (Real.exp shift * y)) =ᵐ[
      volume.restrict (Ioc (q * Real.exp (-shift)) q)]
      fun y => -(Real.exp (-shift / 2) : ℂ) * bRaw coordinate y := by
  let B := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let character := fullMellinTranslationCharacter (star coordinate.value) shift
  have qmp (time : ℝ) : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp time * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp time) (Real.exp_ne_zero time))
  have raw : (fourierColumn coordinate shift : ℝ → ℂ) =ᵐ[volume] fun x =>
      character * (symmetricInterval q).indicator (bRaw coordinate) x -
        (Real.exp (-shift / 2) : ℂ) *
          (symmetricInterval q).indicator (bRaw coordinate) (Real.exp (-shift) * x) := by
    rw [fourierColumn_action]
    filter_upwards [Lp.coeFn_sub (character • B) (burnolMultiplicativeDilation (-shift) B),
      Lp.coeFn_smul character B, burnolMultiplicativeDilation_coeFn (-shift) B,
      extension_read coordinate, (qmp (-shift)).ae (extension_read coordinate)]
      with x subRead scaled action direct inverse
    change (character • B - burnolMultiplicativeDilation (-shift) B : BurnolL2) x = _
    rw [subRead]
    change (character • B : BurnolL2) x - burnolMultiplicativeDilation (-shift) B x = _
    rw [scaled, action]
    change character * B x - (Real.exp (-shift / 2) : ℂ) * B (Real.exp (-shift) * x) = _
    rw [direct, inverse]
  filter_upwards [ae_restrict_of_ae ((qmp shift).ae raw), ae_restrict_mem measurableSet_Ioc]
    with y action inside
  have endpoint : Real.exp shift * (q * Real.exp (-shift)) = q := by
    rw [Real.exp_neg]
    field_simp
  have outer : q < Real.exp shift * y := by
    simpa only [endpoint] using mul_lt_mul_of_pos_left inside.1 (Real.exp_pos shift)
  have outside : Real.exp shift * y ∉ symmetricInterval q := fun member =>
    not_lt_of_ge member.2 outer
  have original : y ∈ symmetricInterval q := by
    change -q ≤ y ∧ y ≤ q
    exact ⟨by nlinarith [Real.exp_pos (-shift), inside.1], inside.2⟩
  have inverse : Real.exp (-shift) * (Real.exp shift * y) = y := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [indicator_of_notMem outside, inverse, indicator_of_mem original] at action
  simpa only [mul_zero, zero_sub, neg_mul] using action

private theorem column_even (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    reflectL2 (fourierColumn coordinate shift) = fourierColumn coordinate shift := by
  have original : reflectL2 (burnolQuarterZeroExtension
      (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) =
      burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) := by
    change reflectL2 (burnolRadiusZeroExtension q _) = _
    rw [burnolRadiusZeroExtension_reflect, burnolRieszSingleFourierSource_reflection_fixed]
    rfl
  conv_rhs => rw [fourierColumn_action]
  rw [fourierColumn_action, map_sub, map_smul, reflectL2_burnolMultiplicativeDilation, original]

theorem annularRead_nonnegative (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    annularRead coordinate shift = -(2 : ℂ) * (Real.exp (shift / 2) : ℂ) *
      ∫ y : ℝ in (q * Real.exp (-shift))..q,
        star (bRaw coordinate y) * bRaw coordinate (Real.exp shift * y) := by
  let f := fun x : ℝ => star (fourierColumn coordinate shift x) * bRaw coordinate x
  have regular : IntegrableOn f (symmetricInterval q)ᶜ := by
    simpa only [fourierTail_eq_source] using exterior_integrable _ _ _ _ _
      (fourierColumn_integrable coordinate shift) (burnolRieszFourier_ae_raw coordinate)
      (fourier_raw coordinate)
  have even : (fun x : ℝ => f (-x)) =ᵐ[volume] f := by
    filter_upwards [Lp.coeFn_compMeasurePreserving (fourierColumn coordinate shift) negMeasurePreserving]
      with x reflected
    change reflectL2 (fourierColumn coordinate shift) x = fourierColumn coordinate shift (-x) at reflected
    rw [column_even] at reflected
    dsimp only [f]
    rw [source_raw_even, ← reflected]
  have supported : ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval (q * Real.exp shift) → f x = 0 := by
    have cutoff := fourierColumn_cutoff_self coordinate shift
    rw [abs_of_nonneg nonnegative] at cutoff
    filter_upwards [cutoff_ae_zero _ _ cutoff] with x zero outside
    dsimp only [f]
    rw [zero outside, star_zero, zero_mul]
  have reduced : annularRead coordinate shift = ∫ x : ℝ in (symmetricInterval q)ᶜ, f x := by
    unfold annularRead
    rw [positionColumn_integral_zero, fourierColumn_integral_zero,
      exteriorRead_zero_of_quarter _ _ (positionColumn_quarter coordinate shift nonnegative)]
    simp only [star_zero, mul_zero, zero_add]
    unfold exteriorRead
    apply integral_congr_ae
    filter_upwards with x
    rw [fourierTail_eq_source]
  have ordered : q * Real.exp (-shift) ≤ q :=
    mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ q)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative))
  have band : (∫ y : ℝ in (q * Real.exp (-shift))..q, f (Real.exp shift * y)) =
      -(Real.exp (-shift / 2) : ℂ) * ∫ y : ℝ in (q * Real.exp (-shift))..q,
        star (bRaw coordinate y) * bRaw coordinate (Real.exp shift * y) := by
    rw [intervalIntegral.integral_of_le ordered, intervalIntegral.integral_of_le ordered,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [column_scaled_read coordinate shift] with y read
    dsimp only [f]
    rw [read, star_mul, star_neg]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  have weight : (Real.exp shift : ℂ) * (Real.exp (-shift / 2) : ℂ) =
      (Real.exp (shift / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [reduced, exterior_integral_eq_scaled shift nonnegative f regular even supported, band]
  calc
    _ = -(2 : ℂ) * ((Real.exp shift : ℂ) * (Real.exp (-shift / 2) : ℂ)) *
        ∫ y : ℝ in (q * Real.exp (-shift))..q,
          star (bRaw coordinate y) * bRaw coordinate (Real.exp shift * y) := by ring
    _ = _ := by rw [weight]

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
