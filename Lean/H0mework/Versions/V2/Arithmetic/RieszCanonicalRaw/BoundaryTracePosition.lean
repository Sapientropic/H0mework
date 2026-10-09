import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.PairedBoundaryCanonicalRaw

/-! The same canonical Riesz state generates its inner value, outer trace and actual gap/tail jump. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
noncomputable section

def burnolRieszStatePositiveOuterRaw
    (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) -
    (1 / 2 : ℂ) *
      (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) x +
        burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) (-x))

theorem burnolRieszStateRaw_eq_positiveOuter
    (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (outside : (1 / 4 : ℝ) < x) :
    burnolRieszStateRaw coordinate x =
      burnolRieszStatePositiveOuterRaw coordinate x := by
  have positiveX : 0 < x := (by norm_num : (0 : ℝ) < 1 / 4) |>.trans outside
  have xNotGap : x ∉ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc, not_and_or]
    exact Or.inr (not_le_of_gt outside)
  have negXNotGap : -x ∉ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc, not_and_or]
    exact Or.inl (by linarith)
  have xTail : x ∈ Ioi (1 / 4 : ℝ) := outside
  have negXNotTail : -x ∉ Ioi (1 / 4 : ℝ) := by
    simp only [mem_Ioi, not_lt]
    linarith
  unfold burnolRieszStateRaw burnolAmbientMellinKernelRaw
    burnolGapRieszRaw burnolRieszCorrectionRaw
    burnolRadiusMellinTailKernelRaw burnolRieszStatePositiveOuterRaw
  simp only [Set.indicator_of_notMem xNotGap,
    Set.indicator_of_notMem negXNotGap, xTail, negXNotTail,
    if_true, if_false, mul_zero, zero_add]
  ring

theorem burnolRieszStateRaw_tendsto_quarter_right
    (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (burnolRieszStateRaw coordinate)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ))) := by
  have positiveQuarter : (0 : ℝ) < 1 / 4 := by norm_num
  have powered : ContinuousAt
      (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value)) (1 / 4 : ℝ) :=
    Complex.continuousAt_ofReal_cpow_const (1 / 4 : ℝ)
      (-star coordinate.value) (Or.inr positiveQuarter.ne')
  have fourier : Continuous
      (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) :=
    burnolRadiusTruncatedFourierRaw_continuous _
  have outerContinuous : ContinuousAt
      (burnolRieszStatePositiveOuterRaw coordinate) (1 / 4 : ℝ) := by
    unfold burnolRieszStatePositiveOuterRaw
    fun_prop
  have outerLimit : Tendsto (burnolRieszStatePositiveOuterRaw coordinate)
      (nhdsWithin (1 / 4 : ℝ) (Ioi (1 / 4 : ℝ)))
      (nhds (burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ))) :=
    outerContinuous.tendsto.mono_left inf_le_left
  apply outerLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (burnolRieszStateRaw_eq_positiveOuter coordinate hx).symm

theorem burnolRieszStateRaw_even
    (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    burnolRieszStateRaw coordinate (-x) = burnolRieszStateRaw coordinate x := by
  unfold burnolRieszStateRaw
  simp only [neg_neg]
  ring

def burnolRieszStateQuarterInnerRaw
    (coordinate : BurnolCompletedMellinCoordinate) : ℂ :=
  star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value) *
      star ((‖intervalConstant (1 / 4 : ℝ)‖ ^ 2 : ℂ)⁻¹) -
    burnolQuarterMeanCoefficient
      (burnolTruncatedFourier
        (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2))

theorem burnolRieszStateRaw_eq_quarterInner_of_mem
    (coordinate : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : x ∈ symmetricInterval (1 / 4 : ℝ)) :
    burnolRieszStateRaw coordinate x =
      burnolRieszStateQuarterInnerRaw coordinate := by
  have negInside : -x ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc] at inside ⊢
    constructor <;> linarith [inside.1, inside.2]
  have xNotTail : x ∉ Ioi (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc] at inside
    exact not_lt_of_ge inside.2
  have negXNotTail : -x ∉ Ioi (1 / 4 : ℝ) := by
    simp only [symmetricInterval, mem_Icc] at inside
    simp only [mem_Ioi, not_lt]
    linarith [inside.1]
  unfold burnolRieszStateRaw burnolAmbientMellinKernelRaw
    burnolGapRieszRaw burnolRieszCorrectionRaw
    burnolRadiusMellinTailKernelRaw burnolMeanZeroFourierRaw
    burnolRieszStateQuarterInnerRaw
  simp only [Set.indicator_of_mem inside, Set.indicator_of_mem negInside,
    xNotTail, negXNotTail, if_false, mul_one, add_zero]
  ring

theorem burnolRieszStateRaw_continuousAt_scaled_outer
    (coordinate : BurnolCompletedMellinCoordinate) {scale x : ℝ}
    (outside : (1 / 4 : ℝ) < scale * x) :
    ContinuousAt (fun y : ℝ => burnolRieszStateRaw coordinate (scale * y)) x := by
  have scaleMap : ContinuousAt (fun y : ℝ => scale * y) x := by fun_prop
  have eventuallyOutside : ∀ᶠ y in nhds x, (1 / 4 : ℝ) < scale * y :=
    scaleMap.eventually (Ioi_mem_nhds outside)
  have positiveTarget : 0 < scale * x :=
    (by norm_num : (0 : ℝ) < 1 / 4) |>.trans outside
  have outerContinuous : ContinuousAt
      (burnolRieszStatePositiveOuterRaw coordinate) (scale * x) := by
    unfold burnolRieszStatePositiveOuterRaw
    have powered : ContinuousAt
        (fun y : ℝ => (y : ℂ) ^ (-star coordinate.value)) (scale * x) :=
      Complex.continuousAt_ofReal_cpow_const (scale * x) (-star coordinate.value)
        (Or.inr positiveTarget.ne')
    have fourier : Continuous
        (burnolRadiusTruncatedFourierRaw (1 / 4 : ℝ)
          (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)) :=
      burnolRadiusTruncatedFourierRaw_continuous _
    fun_prop
  have outerComposed : ContinuousAt
      (fun y : ℝ => burnolRieszStatePositiveOuterRaw coordinate (scale * y)) x :=
    outerContinuous.comp scaleMap
  apply outerComposed.congr_of_eventuallyEq
  filter_upwards [eventuallyOutside] with y hy
  exact burnolRieszStateRaw_eq_positiveOuter coordinate hy

theorem burnolRieszStateRaw_continuousAt_scaled_inner
    (coordinate : BurnolCompletedMellinCoordinate) {scale x : ℝ}
    (inside : scale * x ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) :
    ContinuousAt (fun y : ℝ => burnolRieszStateRaw coordinate (scale * y)) x := by
  have scaleMap : ContinuousAt (fun y : ℝ => scale * y) x := by fun_prop
  have eventuallyInside : ∀ᶠ y in nhds x,
      scale * y ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) :=
    scaleMap.eventually (Ioo_mem_nhds inside.1 inside.2)
  have constantContinuous : ContinuousAt
      (fun _y : ℝ => burnolRieszStateQuarterInnerRaw coordinate) x :=
    continuousAt_const
  apply constantContinuous.congr_of_eventuallyEq
  filter_upwards [eventuallyInside] with y hy
  exact burnolRieszStateRaw_eq_quarterInner_of_mem coordinate
    (show scale * y ∈ symmetricInterval (1 / 4 : ℝ) by
      simpa only [symmetricInterval, mem_Icc] using ⟨hy.1.le, hy.2.le⟩)

theorem burnolRieszPairedDilationRaw_continuousAt_quarter
    (coordinate : BurnolCompletedMellinCoordinate) {shift : ℝ}
    (positiveShift : 0 < shift) :
    ContinuousAt (burnolRieszPairedDilationRaw coordinate shift) (1 / 4 : ℝ) := by
  have expPlus : 1 < Real.exp shift := Real.one_lt_exp_iff.mpr positiveShift
  have expMinus : Real.exp (-shift) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos positiveShift)
  have plusOutside : (1 / 4 : ℝ) < Real.exp shift * (1 / 4 : ℝ) := by
    nlinarith
  have minusInside : Real.exp (-shift) * (1 / 4 : ℝ) ∈
      Ioo (-(1 / 4 : ℝ)) (1 / 4 : ℝ) := by
    constructor
    · nlinarith [Real.exp_pos (-shift)]
    · nlinarith [Real.exp_pos (-shift)]
  have plus := burnolRieszStateRaw_continuousAt_scaled_outer coordinate
    plusOutside
  have minus := burnolRieszStateRaw_continuousAt_scaled_inner coordinate minusInside
  unfold burnolRieszPairedDilationRaw burnolRieszDilationRaw
  exact continuousAt_const.mul
    ((continuousAt_const.mul plus).add (continuousAt_const.mul minus))

theorem burnolRieszPairedDilationRaw_even
    (coordinate : BurnolCompletedMellinCoordinate) (shift x : ℝ) :
    burnolRieszPairedDilationRaw coordinate shift (-x) =
      burnolRieszPairedDilationRaw coordinate shift x := by
  unfold burnolRieszPairedDilationRaw burnolRieszDilationRaw
  rw [show Real.exp shift * -x = -(Real.exp shift * x) by ring,
    show Real.exp (-shift) * -x = -(Real.exp (-shift) * x) by ring,
    burnolRieszStateRaw_even, burnolRieszStateRaw_even]

theorem burnolRieszPairedDilationRaw_continuousAt_neg_quarter
    (coordinate : BurnolCompletedMellinCoordinate) {shift : ℝ}
    (positiveShift : 0 < shift) :
    ContinuousAt (burnolRieszPairedDilationRaw coordinate shift) (-(1 / 4 : ℝ)) := by
  have negAt : ContinuousAt (fun x : ℝ => -x) (-(1 / 4 : ℝ)) := continuousAt_neg
  have source : ContinuousAt
      (burnolRieszPairedDilationRaw coordinate shift ∘ fun x : ℝ => -x)
      (-(1 / 4 : ℝ)) :=
    ContinuousAt.comp_of_eq
      (f := fun x : ℝ => -x)
      (g := burnolRieszPairedDilationRaw coordinate shift)
      (y := (1 / 4 : ℝ))
      (burnolRieszPairedDilationRaw_continuousAt_quarter coordinate positiveShift)
      negAt (by norm_num)
  apply source.congr_of_eventuallyEq
  filter_upwards with x
  exact (burnolRieszPairedDilationRaw_even coordinate shift x).symm

/-- The canonical inner value is the actual constant-gap coefficient of the
same zero-owned Riesz state. -/
theorem burnolRieszStateQuarterInnerRaw_eq_gapCoefficient
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszStateQuarterInnerRaw coordinate =
      burnolConstantGapCoefficient (1 / 4 : ℝ)
        (burnolCompletedMellinRieszVector coordinate) := by
  have gap : burnolRieszStateQuarterInnerRaw coordinate •
        intervalConstant (1 / 4 : ℝ) =
      burnolQuarterRestriction
        (burnolCompletedMellinRieszVector coordinate : BurnolL2) := by
    apply Lp.ext
    have restricted := LpToLpRestrictCLM_coeFn ℂ
      (symmetricInterval (1 / 4 : ℝ))
      (burnolCompletedMellinRieszVector coordinate : BurnolL2)
    have raw := ae_restrict_of_ae (s := symmetricInterval (1 / 4 : ℝ))
      (burnolRieszState_ae_raw coordinate)
    filter_upwards [Lp.coeFn_smul (burnolRieszStateQuarterInnerRaw coordinate)
        (intervalConstant (1 / 4 : ℝ)),
      intervalConstant_coeFn (1 / 4 : ℝ), restricted, raw,
      ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ))]
        with x scaled constant restriction source inside
    rw [scaled]
    change burnolRieszStateQuarterInnerRaw coordinate *
        intervalConstant (1 / 4 : ℝ) x = _
    rw [constant, mul_one]
    exact (restriction.trans (source.trans
      (burnolRieszStateRaw_eq_quarterInner_of_mem coordinate inside))).symm
  exact (burnolConstantGapCoefficient_eq (1 / 4 : ℝ) (by norm_num)
    (burnolCompletedMellinRieszVector coordinate)
    (burnolRieszStateQuarterInnerRaw coordinate) gap).symm

theorem burnolRieszStateRaw_eq_quarterInner
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszStateRaw coordinate (1 / 4 : ℝ) =
      burnolRieszStateQuarterInnerRaw coordinate := by
  have posGap : (1 / 4 : ℝ) ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp [symmetricInterval]
  have negGap : (-(1 / 4 : ℝ)) ∈ symmetricInterval (1 / 4 : ℝ) := by
    simp [symmetricInterval]
  have posNotTail : (1 / 4 : ℝ) ∉ Ioi (1 / 4 : ℝ) := by simp
  have negNotTail : (-(1 / 4 : ℝ)) ∉ Ioi (1 / 4 : ℝ) := by norm_num
  unfold burnolRieszStateRaw burnolAmbientMellinKernelRaw
    burnolGapRieszRaw burnolRieszCorrectionRaw
    burnolRadiusMellinTailKernelRaw burnolMeanZeroFourierRaw
    burnolRieszStateQuarterInnerRaw
  simp only [Set.indicator_of_mem posGap, Set.indicator_of_mem negGap,
    posNotTail, negNotTail, if_false, mul_one, add_zero]
  ring

/-- Exact positive-window jump of the same Riesz source.  The Fourier raw of
`b` cancels; what remains is the genuine gap-tail jump minus the two canonical
endpoint reads of `S b`. -/
theorem burnolRieszState_quarter_outer_sub_inner
    (coordinate : BurnolCompletedMellinCoordinate) :
    burnolRieszStatePositiveOuterRaw coordinate (1 / 4 : ℝ) -
        burnolRieszStateQuarterInnerRaw coordinate =
      (1 / 2 : ℂ) * ((1 / 4 : ℝ) : ℂ) ^ (-star coordinate.value) -
        star (burnolRadiusMellinGapMoment (1 / 4 : ℝ) coordinate.value) *
          star ((‖intervalConstant (1 / 4 : ℝ)‖ ^ 2 : ℂ)⁻¹) -
        (1 / 2 : ℂ) *
          (burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
              (1 / 4 : ℝ) +
            burnolMeanZeroFourierRaw (burnolRieszSingleFourierSource coordinate)
              (-(1 / 4 : ℝ))) := by
  unfold burnolRieszStatePositiveOuterRaw burnolRieszStateQuarterInnerRaw
    burnolMeanZeroFourierRaw
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
