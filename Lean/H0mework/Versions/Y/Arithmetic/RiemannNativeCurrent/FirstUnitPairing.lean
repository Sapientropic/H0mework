import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.FirstRawPairing

/-! The original source normalization produces the literal unit in the first Tate window. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

def burnolFirstSourceMellinCoefficient (coordinate : ℂ)
    (source : burnolCompactAnnulusSource) : ℂ :=
  2 * coPoissonMuntzEvenSourceMellin source.1 (1 - coordinate)

theorem burnolFirstSource_rawInner (coordinate : ℂ)
    (source : burnolCompactAnnulusSource) {x : ℝ}
    (positive : 0 < x) (small : x ≤ (1 / 4 : ℝ)) :
    burnolFourierRightDivisionRaw (coordinate / 2)
      (fun t => (2 : ℂ) * source.1 t) x =
      burnolFirstSourceMellinCoefficient coordinate source * (-(x : ℂ) ^ (coordinate - 1)) := by
  let weighted : ℝ → ℂ := fun t => (t : ℂ) ^ (-coordinate) * ((2 : ℂ) * source.1 t)
  have momentRead : (∫ t : ℝ in Ioi 0, weighted t) =
      coPoissonMuntzEvenSourceMellin source.1 (1 - coordinate) := by
    unfold coPoissonMuntzEvenSourceMellin mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only [weighted, coPoissonMuntzEvenSource]
    rw [show 1 - coordinate - 1 = -coordinate by ring, source.2.1 t]
    simp only [smul_eq_mul]
    ring
  have sameTail : (∫ t : ℝ in Ioi x, weighted t) = ∫ t : ℝ in Ioi 0, weighted t := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with t
    by_cases beyond : x < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi x from beyond),
        Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from positive.trans beyond)]
    · rw [Set.indicator_of_notMem (show t ∉ Ioi x from beyond)]
      by_cases tpos : 0 < t
      · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from tpos)]
        have inside : |t| ≤ (1 / 4 : ℝ) := by
          rw [abs_of_pos tpos]
          exact (le_of_not_gt beyond).trans small
        dsimp only [weighted]
        rw [source.2.2.1 t inside, mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from tpos)]
  rw [burnolFourierRightDivisionRaw_eq_tail _ _ positive]
  rw [show 2 * (coordinate / 2) - 1 = coordinate - 1 by ring,
    show -2 * (coordinate / 2) = -coordinate by ring]
  change -2 * (x : ℂ) ^ (coordinate - 1) * (∫ t : ℝ in Ioi x, weighted t) = _
  rw [sameTail, momentRead]
  unfold burnolFirstSourceMellinCoefficient
  ring

/-- The existing normalized source specializes the generated tail coefficient to one. -/
theorem burnolNormalizedFirstSource_rawUnit (coordinate : ℂ) {x : ℝ}
    (positive : 0 < x) (small : x ≤ (1 / 4 : ℝ)) :
    burnolFourierRightDivisionRaw (coordinate / 2)
      (fun t => (2 : ℂ) * (burnolCoordinateNormalizedAnnulusSource (1 - coordinate)).1 t) x =
      -(x : ℂ) ^ (coordinate - 1) := by
  rw [burnolFirstSource_rawInner coordinate _ positive small]
  have unit : burnolFirstSourceMellinCoefficient coordinate
      (burnolCoordinateNormalizedAnnulusSource (1 - coordinate)) = 1 :=
    burnolCoordinateNormalizedAnnulusSource_mellin_normalization (1 - coordinate)
  rw [unit, one_mul]

theorem burnolFirstSourceRaw_abs (z : ℂ) (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolFourierRightDivisionRaw z (fun t => (2 : ℂ) * source.1 t) x =
      burnolFourierRightDivisionRaw z (fun t => (2 : ℂ) * source.1 t) |x| := by
  rcases le_or_gt 0 x with nonnegative | negative
  · rw [abs_of_nonneg nonnegative]
  · rw [abs_of_neg negative]
    unfold burnolFourierRightDivisionRaw
    congr 1
    apply integral_congr_ae
    filter_upwards with h
    rw [mul_neg, source.2.1]

theorem burnolFirstSourceRaw_outer (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {x : ℝ} (outside : 4 ≤ |x|) :
    burnolFourierRightDivisionRaw (coordinate.value / 2) (fun t => (2 : ℂ) * source.1 t) x = 0 := by
  rw [burnolFirstSourceRaw_abs, burnolFourierRightDivisionRaw_eq_tail _ _ (lt_of_lt_of_le (by norm_num) outside)]
  have empty : (∫ t : ℝ in Ioi |x|, (t : ℂ) ^ (-2 * (coordinate.value / 2)) * ((2 : ℂ) * source.1 t)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    rw [source.2.2.2 t (by
      rw [abs_of_pos (lt_of_lt_of_le (by norm_num) (outside.trans ht.le))]
      exact outside.trans ht.le), mul_zero, mul_zero]
  rw [empty, mul_zero]

theorem burnolCompleteFirstSourceTate_unitPairing (coordinate : BurnolCompletedMellinCoordinate)
    (test : Lp ℂ 2 (volume.restrict (symmetricInterval (1 / 4 : ℝ)))) :
    inner ℂ test (restrictToInterval (1 / 4)
      (burnolTateReciprocalL2 (burnolCompleteRemainderSource (coordinate.value / 2)
        (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1))) =
      ∫ x : ℝ in symmetricInterval (1 / 4 : ℝ),
        inner ℂ (test x) (-(((|x| : ℝ) : ℂ) ^ (coordinate.value - 1))) := by
  let source := burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)
  let value : BurnolL2 := (2 : ℂ) • source.1.toLp 2 volume
  let raw : ℝ → ℂ := fun t => (2 : ℂ) * source.1 t
  have rawStrong : StronglyMeasurable raw :=
    (source.1.continuous.const_mul (2 : ℂ)).stronglyMeasurable
  have rawRead : raw =ᵐ[volume] value := by
    filter_upwards [Lp.coeFn_smul (2 : ℂ) (source.1.toLp 2 volume),
      source.1.coeFn_toLp 2 volume] with x hsmul hsource
    change (2 : ℂ) * source.1 x = value x
    rw [hsmul]
    change (2 : ℂ) * source.1 x = (2 : ℂ) * source.1.toLp 2 volume x
    rw [hsource]
  have even : reflectL2 value = value := by
    have reflection := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
    apply Lp.ext
    filter_upwards [reflection, rawRead, negMeasurePreserving.quasiMeasurePreserving.ae rawRead]
      with x href hraw hneg
    have read : reflectL2 value x = value (-x) := href
    rw [read, ← hneg, ← hraw]
    exact congrArg ((2 : ℂ) * ·) (source.2.1 x)
  have rightQuarter : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  calc
    _ = ∫ x : ℝ in symmetricInterval (1 / 4 : ℝ),
        inner ℂ (test x) (burnolFourierRightDivisionRaw (coordinate.value / 2) raw x) := by
      rw [burnolCompleteRemainderSource_tateFirst _ rightQuarter]
      exact burnolExpandingRightResolvent_pairing_raw (1 / 4) coordinate value even raw rawStrong rawRead test
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ)),
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx nonzero
      have small : |x| ≤ (1 / 4 : ℝ) := abs_le.mpr hx
      have positive : 0 < |x| := abs_pos.mpr nonzero
      rw [burnolFirstSourceRaw_abs (coordinate.value / 2) source x]
      exact congrArg (inner ℂ (test x))
        (burnolNormalizedFirstSource_rawUnit coordinate.value positive small)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
