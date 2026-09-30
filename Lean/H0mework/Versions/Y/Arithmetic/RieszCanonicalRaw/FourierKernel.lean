import H0mework.Versions.Y.Arithmetic.RieszCanonicalRaw.Forcing

/-! The same physical Riesz state consumes the source traces, retaining both Fourier gap means. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

private theorem sourceWindow_read (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolQuarterZeroExtension
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) :
          ℝ → ℂ) =ᵐ[volume]
      (symmetricInterval (1 / 4 : ℝ)).indicator
        (burnolRieszSingleFourierSourceRaw coordinate) := by
  have read := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp
    (burnolRieszSingleFourierSource_ae_raw coordinate)
  filter_upwards [burnolRadiusZeroExtension_coe
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2), read]
      with x extended raw
  change burnolRadiusZeroExtension (1 / 4 : ℝ)
    (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x = _
  rw [extended]
  by_cases inside : x ∈ symmetricInterval (1 / 4 : ℝ)
  · simp only [indicator_of_mem inside]
    exact raw inside
  · simp only [indicator_of_notMem inside]

def burnolRieszFourierExteriorRaw
    (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  burnolEvenRaw (burnolGapTailFourierRaw (1 / 4 : ℝ) coordinate) frequency +
    burnolEvenRaw (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
      (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
        BurnolQuarterIntervalL2)) frequency

def burnolRieszFourierRaw
    (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  burnolRieszFourierExteriorRaw coordinate frequency -
    burnolEvenRaw ((symmetricInterval (1 / 4 : ℝ)).indicator
      (burnolRieszSingleFourierSourceRaw coordinate)) frequency

theorem burnolRieszFourier_ae_raw
    (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) : ℝ → ℂ)
      =ᵐ[volume] burnolRieszFourierRaw coordinate := by
  let q := burnolAmbientCompletedMellinKernelFormula coordinate
  let b := burnolRieszSingleFourierSource coordinate
  let first := fourierL2 (burnolQuarterZeroExtension
    (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2))
  let second := burnolQuarterZeroExtension (b : BurnolQuarterIntervalL2)
  have split : fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      (burnolAmbientEvenPart (fourierL2 q) + burnolAmbientEvenPart first) -
        burnolAmbientEvenPart second := by
    rw [burnolCompletedMellinRieszVector_eq_singleFourierSource]
    simp only [map_add, fourierL2_burnolAmbientEvenPart, map_sub, fourierL2_fourierL2]
    unfold burnolAmbientEvenPart
    simp only [map_sub, reflectL2_reflectL2]
    dsimp only [q, b, first, second]
    module
  rw [split]
  have firstRead := burnolEvenRaw_ae first
    (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
      (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2))
    (burnolRadiusFourierL2_zeroExtension_ae_eq_raw
      (burnolMeanZeroTruncatedFourier b : BurnolQuarterIntervalL2))
  have secondRead := burnolEvenRaw_ae second
    ((symmetricInterval (1 / 4 : ℝ)).indicator (burnolRieszSingleFourierSourceRaw coordinate))
    (sourceWindow_read coordinate)
  filter_upwards [Lp.coeFn_sub
    (burnolAmbientEvenPart (fourierL2 q) + burnolAmbientEvenPart first)
    (burnolAmbientEvenPart second),
    Lp.coeFn_add (burnolAmbientEvenPart (fourierL2 q)) (burnolAmbientEvenPart first),
    burnolEvenRaw_ae (fourierL2 q)
      (burnolGapTailFourierRaw (1 / 4 : ℝ) coordinate)
      (burnolGapTailFourier_ae_canonical (1 / 4 : ℝ) (by norm_num) coordinate),
    firstRead, secondRead] with x subRead addRead qRead firstRaw secondRaw
  rw [subRead]
  change (burnolAmbientEvenPart (fourierL2 q) + burnolAmbientEvenPart first : BurnolL2) x -
    burnolAmbientEvenPart second x = _
  rw [addRead]
  change burnolAmbientEvenPart (fourierL2 q) x + burnolAmbientEvenPart first x -
    burnolAmbientEvenPart second x = _
  rw [qRead, firstRaw, secondRaw]
  rfl

theorem burnolRieszFourierRaw_gap_read
    (coordinate : BurnolCompletedMellinCoordinate) {frequency : ℝ}
    (inside : frequency ∈ symmetricInterval (1 / 4 : ℝ)) :
    burnolRieszFourierRaw coordinate frequency =
      burnolQuarterMeanCoefficient (burnolQuarterRestriction
        (burnolAmbientEvenPart (fourierL2 (burnolAmbientCompletedMellinKernelFormula coordinate)))) +
      burnolQuarterMeanCoefficient (burnolTruncatedFourier
        (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
          BurnolQuarterIntervalL2)) := by
  have negative : -frequency ∈ symmetricInterval (1 / 4 : ℝ) := by
    simpa only [symmetricInterval, mem_Icc, neg_le, le_neg, neg_neg] using
      And.intro inside.2 inside.1
  unfold burnolRieszFourierRaw burnolRieszFourierExteriorRaw burnolEvenRaw
  simp only [indicator_of_mem inside, indicator_of_mem negative,
    burnolRieszSingleFourierSourceRaw, burnolRieszFourierForcingRaw,
    burnolPositionMeanZeroRaw, burnolMeanZeroRaw, burnolEvenRaw,
    burnolMeanZeroFourierRaw, neg_neg]
  ring

theorem burnolRieszFourierExteriorRaw_continuousAt
    (coordinate : BurnolCompletedMellinCoordinate) {frequency : ℝ}
    (nonzero : frequency ≠ 0) :
    ContinuousAt (burnolRieszFourierExteriorRaw coordinate) frequency := by
  have positive := burnolGapTailFourierRaw_continuousAt (1 / 4 : ℝ)
    (by norm_num) coordinate nonzero
  have negative := (burnolGapTailFourierRaw_continuousAt (1 / 4 : ℝ)
    (by norm_num) coordinate (neg_ne_zero.mpr nonzero)).comp continuous_neg.continuousAt
  have returned := burnolRadiusTruncatedFourierRaw_continuous
    (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate) :
      BurnolQuarterIntervalL2)
  exact (continuousAt_const.mul (positive.add negative)).add
    (continuousAt_const.mul
      (returned.continuousAt.add (returned.continuousAt.comp continuous_neg.continuousAt)))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
