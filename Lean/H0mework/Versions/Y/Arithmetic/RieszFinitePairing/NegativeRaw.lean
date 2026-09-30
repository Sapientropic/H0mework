import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Band
import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.ColumnAction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource OriginalRieszSourceGreen OriginalRieszFiniteColumns OriginalPaPhysicalGreen
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "rRaw" => burnolRieszReturnRaw

def positionBaseRaw (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  burnolEvenRaw (burnolAmbientMellinKernelRaw coordinate) x +
    (symmetricInterval q).indicator (rRaw coordinate) x

theorem positionBase_read (coordinate : BurnolCompletedMellinCoordinate) :
    (gapState coordinate + E (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : BurnolL2) =ᵐ[volume]
      positionBaseRaw coordinate := by
  have returned : (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2) : ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval q).indicator (rRaw coordinate) :=
    burnolZeroExtensionMeanZeroFourier_ae_raw (burnolRieszSingleFourierSource coordinate)
  filter_upwards [Lp.coeFn_add (gapState coordinate) (E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)),
    gapState_read coordinate, returned] with x added gap source
  rw [added]
  change gapState coordinate x + E (Constructor.returnState coordinate : BurnolQuarterIntervalL2) x = _
  rw [gap, source]
  rfl

theorem positionBaseRaw_even (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    positionBaseRaw coordinate (-x) = positionBaseRaw coordinate x := by
  have negative : -x ∈ symmetricInterval q ↔ x ∈ symmetricInterval q := by
    simp only [symmetricInterval, mem_Icc]
    constructor <;> intro inside <;> constructor <;> linarith [inside.1, inside.2]
  unfold positionBaseRaw burnolEvenRaw
  simp only [neg_neg]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside, indicator_of_mem (negative.mpr inside), return_raw_even]
    ring
  · rw [indicator_of_notMem inside, indicator_of_notMem (fun member => inside (negative.mp member))]
    ring

def negativePositionColumnRaw (coordinate : BurnolCompletedMellinCoordinate) (shift x : ℝ) : ℂ :=
  (Real.exp (-shift / 2) : ℂ) * positionBaseRaw coordinate (Real.exp (-shift) * x) -
    fullMellinTranslationCharacter (star coordinate.value) (-shift) * positionBaseRaw coordinate x

theorem negativePositionColumn_read (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (positionColumn coordinate (-shift) : ℝ → ℂ) =ᵐ[volume] negativePositionColumnRaw coordinate shift := by
  let base := gapState coordinate + E (Constructor.returnState coordinate : BurnolQuarterIntervalL2)
  let character := fullMellinTranslationCharacter (star coordinate.value) (-shift)
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-shift) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (-shift)) (Real.exp_ne_zero _))
  rw [positionColumn_action]
  filter_upwards [Lp.coeFn_sub (burnolMultiplicativeDilation (-shift) base) (character • base),
    Lp.coeFn_smul character base, burnolMultiplicativeDilation_coeFn (-shift) base,
    positionBase_read coordinate, qmp.ae (positionBase_read coordinate)]
      with x difference scaled action original moved
  change (burnolMultiplicativeDilation (-shift) base - character • base : BurnolL2) x = _
  rw [difference]
  change burnolMultiplicativeDilation (-shift) base x - (character • base : BurnolL2) x = _
  rw [scaled, action]
  change (Real.exp (-shift / 2) : ℂ) * base (Real.exp (-shift) * x) - character * base x = _
  change base x = _ at original
  change base (Real.exp (-shift) * x) = _ at moved
  rw [original, moved]
  rfl

private theorem inverse_character_power (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) {x : ℝ} (positive : 0 < x) :
    fullMellinTranslationCharacter (star coordinate.value) (-shift) *
        ((Real.exp shift * x : ℝ) : ℂ) ^ (-star coordinate.value) =
      (Real.exp (-shift / 2) : ℂ) * (x : ℂ) ^ (-star coordinate.value) := by
  have valueNe : coordinate.value ≠ 0 := by
    intro zero
    have half := coordinate.rightHalf
    rw [zero] at half
    norm_num at half
  have exponentNe : -star coordinate.value ≠ 0 := neg_ne_zero.mpr (star_ne_zero.mpr valueNe)
  have scaled := burnolMellinGapMoment_scaled positive (1 + star coordinate.value) (-shift)
  simp only [neg_neg] at scaled
  unfold burnolRadiusMellinGapMoment at scaled
  rw [show (1 : ℂ) - (1 + star coordinate.value) = -star coordinate.value by ring] at scaled
  have power : ((x * Real.exp shift : ℝ) : ℂ) ^ (-star coordinate.value) =
      Complex.exp ((shift : ℂ) * (-star coordinate.value)) * (x : ℂ) ^ (-star coordinate.value) := by
    have multiplied := congrArg (fun value : ℂ => value * (-star coordinate.value)) scaled
    rw [div_mul_cancel₀ _ exponentNe, mul_assoc, div_mul_cancel₀ _ exponentNe] at multiplied
    simpa only [Complex.ofReal_neg, neg_neg] using multiplied
  rw [mul_comm (Real.exp shift) x, power]
  unfold fullMellinTranslationCharacter
  rw [← mul_assoc, ← Complex.exp_add]
  have exponent : ((1 / 2 : ℂ) - star coordinate.value) * (-shift : ℝ) +
      (shift : ℂ) * (-star coordinate.value) = ((-shift / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [exponent, ← Complex.ofReal_exp]

theorem negativePositionColumnRaw_band (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    {y : ℝ} (inside : y ∈ Ioc (q * Real.exp (-shift)) q) :
    negativePositionColumnRaw coordinate shift (Real.exp shift * y) =
      -(Real.exp (-shift / 2) : ℂ) * positionSource coordinate y := by
  have positive : 0 < y := lt_trans (mul_pos (by norm_num : (0 : ℝ) < q) (Real.exp_pos _)) inside.1
  have inGap : y ∈ symmetricInterval q := ⟨by linarith, inside.2⟩
  have inverse : Real.exp (-shift) * (Real.exp shift * y) = y := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have lower : Real.exp shift * (q * Real.exp (-shift)) = q := by
    rw [Real.exp_neg]
    field_simp
  have outside : q < Real.exp shift * y := by
    rw [← lower]
    exact mul_lt_mul_of_pos_left inside.1 (Real.exp_pos _)
  have outGap : Real.exp shift * y ∉ symmetricInterval q := fun member => not_lt_of_ge member.2 outside
  unfold negativePositionColumnRaw
  rw [inverse]
  unfold positionBaseRaw
  rw [gapState_raw_gap coordinate inGap, gapState_raw_tail coordinate outside,
    indicator_of_mem inGap, indicator_of_notMem outGap, add_zero]
  have scaled := inverse_character_power coordinate shift positive
  unfold positionSource
  linear_combination -(1 / 2 : ℂ) * scaled

theorem negativePositionColumn_band_read (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (fun y : ℝ => positionColumn coordinate (-shift) (Real.exp shift * y)) =ᵐ[
      volume.restrict (Ioc (q * Real.exp (-shift)) q)]
      (fun y : ℝ => -(Real.exp (-shift / 2) : ℂ) * positionSource coordinate y) := by
  have qmp : Measure.QuasiMeasurePreserving (fun y : ℝ => Real.exp shift * y) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero _))
  filter_upwards [ae_restrict_of_ae (s := Ioc (q * Real.exp (-shift)) q)
      (qmp.ae (negativePositionColumn_read coordinate shift)),
    ae_restrict_mem measurableSet_Ioc] with y read inside
  exact read.trans (negativePositionColumnRaw_band coordinate shift inside)

theorem negativePositionColumn_even (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    (fun x : ℝ => positionColumn coordinate (-shift) (-x)) =ᵐ[volume] positionColumn coordinate (-shift) := by
  have even (x : ℝ) : negativePositionColumnRaw coordinate shift (-x) = negativePositionColumnRaw coordinate shift x := by
    unfold negativePositionColumnRaw
    rw [mul_neg, positionBaseRaw_even, positionBaseRaw_even]
  filter_upwards [negativePositionColumn_read coordinate shift,
    negMeasurePreserving.quasiMeasurePreserving.ae (negativePositionColumn_read coordinate shift)]
      with x direct reflected
  rw [direct, reflected, even]

theorem negativePositionColumn_support (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval (q * Real.exp shift) → positionColumn coordinate (-shift) x = 0 := by
  have support := positionColumn_cutoff_self coordinate (-shift)
  rw [abs_neg, abs_of_nonneg nonnegative] at support
  filter_upwards [originalPhysicalCutoff_coeFn (q * Real.exp shift) (positionColumn coordinate (-shift))]
    with x read outside
  rw [support, indicator_of_notMem outside] at read
  exact read

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
