import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Seed
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.NegativeRaw

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalPaPhysicalGreen

noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem unscale_band (shift x : ℝ) (inside : x ∈ Ioc q (q * Real.exp shift)) :
    Real.exp (-shift) * x ∈ Ioc (q * Real.exp (-shift)) q := by
  have inverse : Real.exp (-shift) * (q * Real.exp shift) = q := by
    rw [Real.exp_neg]
    field_simp
  exact ⟨by simpa only [mul_comm (Real.exp (-shift)) q] using
    mul_lt_mul_of_pos_left inside.1 (Real.exp_pos (-shift)),
      (mul_le_mul_of_nonneg_left inside.2 (Real.exp_pos (-shift)).le).trans_eq inverse⟩

private theorem rescale (shift x : ℝ) : Real.exp shift * (Real.exp (-shift) * x) = x := by
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

private theorem exterior_read (shift : ℝ) (column : BurnolL2) (raw profile : ℝ → ℂ)
    (represents : (column : ℝ → ℂ) =ᵐ[volume] raw)
    (even : ∀ x, raw (-x) = raw x)
    (band : ∀ x ∈ Ioc q (q * Real.exp shift),
      raw x = -(Real.exp (-shift / 2) : ℂ) * profile (Real.exp (-shift) * x))
    (supported : ∀ᵐ x ∂volume, x ∉ symmetricInterval (q * Real.exp shift) → column x = 0) :
    (column - originalPhysicalCutoff q column : BurnolL2) =ᵐ[volume] bandRaw shift profile := by
  filter_upwards [Lp.coeFn_sub column (originalPhysicalCutoff q column),
    originalPhysicalCutoff_coeFn q column, represents, supported] with x subAt cutoffAt rawAt supportAt
  rw [subAt]
  change column x - originalPhysicalCutoff q column x = _
  rw [cutoffAt]
  by_cases inside : x ∈ symmetricInterval q
  · have absolute : |x| ≤ q := abs_le.mpr inside
    simp only [indicator_of_mem inside, sub_self, bandRaw,
      not_lt_of_ge absolute, false_and, ↓reduceIte]
  · have outside : q < |x| := lt_of_not_ge (fun absolute => inside (abs_le.mp absolute))
    rw [indicator_of_notMem inside, sub_zero]
    by_cases upper : |x| ≤ q * Real.exp shift
    · have atAbsolute : raw |x| = raw x := by
        rcases le_total 0 x with positive | negative
        · rw [abs_of_nonneg positive]
        · rw [abs_of_nonpos negative, even]
      rw [rawAt, ← atAbsolute, band _ ⟨outside, upper⟩, bandRaw, if_pos ⟨outside, upper⟩]
    · rw [bandRaw, if_neg (fun active => upper active.2)]
      exact supportAt (fun member => upper (abs_le.mpr member))

private theorem position_exterior_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    (positionColumn coordinate (-shift) - originalPhysicalCutoff q (positionColumn coordinate (-shift)) :
      BurnolL2) =ᵐ[volume] bandRaw shift (positionSource coordinate) := by
  apply exterior_read shift _ (negativePositionColumnRaw coordinate shift) _
    (negativePositionColumn_read coordinate shift) _ _ (negativePositionColumn_support coordinate shift nonnegative)
  · intro x
    unfold negativePositionColumnRaw
    rw [mul_neg, positionBaseRaw_even, positionBaseRaw_even]
  · intro x inside
    simpa only [rescale] using
      negativePositionColumnRaw_band coordinate shift (unscale_band shift x inside)

private theorem extension_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
      ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate) := by
  have original := (ae_restrict_iff' (measurableSet_symmetricInterval q)).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolQuarterZeroExtension_coe
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), original] with x extended raw
  rw [extended]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem inside, raw inside]
  · rw [indicator_of_notMem inside, indicator_of_notMem inside]

private def fourierColumnRaw (coordinate : BurnolCompletedMellinCoordinate) (shift x : ℝ) : ℂ :=
  fullMellinTranslationCharacter (star coordinate.value) shift *
      (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate) x -
    (Real.exp (-shift / 2) : ℂ) *
      (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate) (Real.exp (-shift) * x)

private theorem fourier_column_read (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (fourierColumn coordinate shift : ℝ → ℂ) =ᵐ[volume] fourierColumnRaw coordinate shift := by
  let B := burnolQuarterZeroExtension (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
  let character := fullMellinTranslationCharacter (star coordinate.value) shift
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-shift) * x) volume volume := by
    simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := Real.exp (-shift)) (Real.exp_ne_zero _))
  rw [fourierColumn_action]
  filter_upwards [Lp.coeFn_sub (character • B) (burnolMultiplicativeDilation (-shift) B),
    Lp.coeFn_smul character B, burnolMultiplicativeDilation_coeFn (-shift) B,
    extension_read coordinate, qmp.ae (extension_read coordinate)] with x subAt scaled action direct moved
  change (character • B - burnolMultiplicativeDilation (-shift) B : BurnolL2) x = _
  rw [subAt]
  change (character • B : BurnolL2) x - burnolMultiplicativeDilation (-shift) B x = _
  rw [scaled, action]
  change character * B x - (Real.exp (-shift / 2) : ℂ) * B (Real.exp (-shift) * x) = _
  rw [direct, moved]
  rfl

private theorem fourier_exterior_read (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    (fourierColumn coordinate shift - originalPhysicalCutoff q (fourierColumn coordinate shift) :
      BurnolL2) =ᵐ[volume] bandRaw shift (burnolRieszSingleFourierSourceRaw coordinate) := by
  have support : ∀ᵐ x ∂volume, x ∉ symmetricInterval (q * Real.exp shift) → fourierColumn coordinate shift x = 0 := by
    have same := fourierColumn_cutoff_self coordinate shift
    rw [abs_of_nonneg nonnegative] at same
    filter_upwards [originalPhysicalCutoff_coeFn (q * Real.exp shift) (fourierColumn coordinate shift)]
      with x read outside
    rw [same, indicator_of_notMem outside] at read
    exact read
  apply exterior_read shift _ (fourierColumnRaw coordinate shift) _ (fourier_column_read coordinate shift) _ _ support
  · have indicatorEven (x : ℝ) :
        (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate) (-x) =
          (symmetricInterval q).indicator (burnolRieszSingleFourierSourceRaw coordinate) x := by
      have inverse : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
        change (-q ≤ -x ∧ -x ≤ q) ↔ (-q ≤ x ∧ x ≤ q)
        constructor <;> intro inside <;> constructor <;> linarith [inside.1, inside.2]
      by_cases inside : x ∈ symmetricInterval q
      · rw [indicator_of_mem inside, indicator_of_mem (inverse.mpr inside), source_raw_even]
      · rw [indicator_of_notMem inside, indicator_of_notMem (fun h => inside (inverse.mp h))]
    intro x
    unfold fourierColumnRaw
    rw [mul_neg, indicatorEven, indicatorEven]
  · intro x inside
    have positive : 0 < x := lt_trans (by norm_num : (0 : ℝ) < q) inside.1
    have outside : x ∉ symmetricInterval q := fun member => not_lt_of_ge member.2 inside.1
    have moved : Real.exp (-shift) * x ∈ symmetricInterval q :=
      ⟨by nlinarith [mul_pos (Real.exp_pos (-shift)) positive], (unscale_band shift x inside).2⟩
    simp only [fourierColumnRaw, indicator_of_notMem outside, indicator_of_mem moved,
      mul_zero, zero_sub, neg_mul]

theorem positionSeed_eq_exterior (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) :
    positionSeed coordinate shift = positionColumn coordinate (-shift) -
      originalPhysicalCutoff q (positionColumn coordinate (-shift)) := by
  apply ext_inner_left ℂ
  intro test
  rw [positionSeed_pairing coordinate shift nonnegative, L2.inner_def]
  exact integral_congr_ae ((position_exterior_read coordinate shift nonnegative).mono
    (fun x read => congrArg (inner ℂ (test x)) read.symm))

theorem fourierSeed_eq_exterior (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) :
    fourierSeed coordinate shift = fourierColumn coordinate shift -
      originalPhysicalCutoff q (fourierColumn coordinate shift) := by
  apply ext_inner_left ℂ
  intro test
  rw [fourierSeed_pairing coordinate shift nonnegative, L2.inner_def]
  exact integral_congr_ae ((fourier_exterior_read coordinate shift nonnegative).mono
    (fun x read => congrArg (inner ℂ (test x)) read.symm))

end
end OriginalRieszFinitePairing.CoPoisson
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
