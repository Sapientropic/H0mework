import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.FirstUnitPairing

/-! The first complete L² source has its generated exterior unit tail. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

def burnolNormalizedFirstSourceUnitTail (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  let positive := burnolRadiusMellinTailKernelL2 4 (by norm_num) (star coordinate.value)
    (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)
  show BurnolL2 from -(positive + reflectL2 positive)

def burnolNormalizedFirstSourceUnitTailRaw (coordinate : ℂ) (x : ℝ) : ℂ :=
  if (4 : ℝ) < |x| then -(((|x| : ℝ) : ℂ) ^ (-coordinate)) else 0

theorem burnolNormalizedFirstSourceUnitTail_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolNormalizedFirstSourceUnitTail coordinate : ℝ → ℂ) =ᵐ[volume] burnolNormalizedFirstSourceUnitTailRaw coordinate.value := by
  let positive := burnolRadiusMellinTailKernelL2 4 (by norm_num) (star coordinate.value)
    (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)
  have sourceRead : (positive : ℝ → ℂ) =ᵐ[volume]
      burnolRadiusMellinTailKernelRaw 4 (star coordinate.value) :=
    (burnolRadiusMellinTailKernelRaw_memLp (by norm_num) (star coordinate.value)
      (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)).coeFn_toLp
  filter_upwards [Lp.coeFn_neg (positive + reflectL2 positive),
    Lp.coeFn_add positive (reflectL2 positive),
    Lp.coeFn_compMeasurePreserving positive negMeasurePreserving,
    sourceRead, negMeasurePreserving.quasiMeasurePreserving.ae sourceRead]
      with x hneg hadd href hpositive hnegative
  change (-(positive + reflectL2 positive) : BurnolL2) x = _
  rw [hneg]
  change -(positive + reflectL2 positive : BurnolL2) x = _
  rw [hadd]
  have reflection : reflectL2 positive x = positive (-x) := href
  change -(positive x + reflectL2 positive x) = _
  rw [reflection, hpositive, hnegative]
  unfold burnolRadiusMellinTailKernelRaw burnolNormalizedFirstSourceUnitTailRaw
  simp only [mem_Ioi, star_star]
  rcases le_or_gt 0 x with nonnegative | negative
  · have leftOutside : ¬ (4 : ℝ) < -x := by linarith
    rw [if_neg leftOutside, add_zero, abs_of_nonneg nonnegative]
    split_ifs <;> simp
  · have rightOutside : ¬ (4 : ℝ) < x := by linarith
    rw [if_neg rightOutside, zero_add, abs_of_neg negative]
    split_ifs <;> simp

theorem burnolNormalizedFirstSourceUnitTail_tate_coeFn (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) : ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| < (1 / 4 : ℝ) then -(((|x| : ℝ) : ℂ) ^ (coordinate.value - 1)) else 0 := by
  have rawMem := (Lp.memLp (burnolNormalizedFirstSourceUnitTail coordinate)).ae_eq
    (burnolNormalizedFirstSourceUnitTail_coeFn coordinate)
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp (burnolNormalizedFirstSourceUnitTail coordinate))
    rawMem (burnolNormalizedFirstSourceUnitTail_coeFn coordinate)
  filter_upwards [burnolTateReciprocalL2_coeFn (burnolNormalizedFirstSourceUnitTail coordinate),
    pulled, volume.ae_ne (0 : ℝ)] with x hread hpull nonzero
  have positive : 0 < |x| := abs_pos.mpr nonzero
  rw [hread, hpull]
  unfold burnolTateReciprocalRaw burnolNormalizedFirstSourceUnitTailRaw
  rw [abs_inv]
  have condition : (4 : ℝ) < |x|⁻¹ ↔ |x| < (1 / 4 : ℝ) := by
    rw [inv_eq_one_div, lt_div_iff₀ positive]
    constructor <;> intro h <;> linarith
  simp only [condition]
  by_cases small : |x| < (1 / 4 : ℝ)
  · rw [if_pos small, if_pos small, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (abs_nonneg x), Complex.cpow_neg, inv_inv, mul_neg]
    congr 1
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero))]
    congr 1
    ring
  · rw [if_neg small, if_neg small, mul_zero]

private theorem tate_unitTail_inner (coordinate : BurnolCompletedMellinCoordinate) :
    (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))]
        fun x => -(((|x| : ℝ) : ℂ) ^ (coordinate.value - 1)) := by
  filter_upwards [ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate),
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ)),
    ae_restrict_of_ae (volume.ae_ne (1 / 4 : ℝ)),
    ae_restrict_of_ae (volume.ae_ne (-1 / 4 : ℝ))] with x hread hx notRight notLeft
  have small : |x| < (1 / 4 : ℝ) := by
    apply abs_lt.mpr
    have bounds : -(1 / 4 : ℝ) ≤ x ∧ x ≤ (1 / 4 : ℝ) := hx
    constructor <;> rcases bounds with ⟨lower, upper⟩ <;> grind
  rw [hread, if_pos small]

private theorem burnolCompleteFirstSourceTate_unitState (coordinate : BurnolCompletedMellinCoordinate) :
    restrictToInterval (1 / 4)
      (burnolTateReciprocalL2 (burnolCompleteRemainderSource (coordinate.value / 2)
        (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1)) =
      restrictToInterval (1 / 4) (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)) := by
  apply ext_inner_left ℂ
  intro test
  rw [burnolCompleteFirstSourceTate_unitPairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (1 / 4 : ℝ))
      (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)), tate_unitTail_inner coordinate]
        with x hrestriction hsource
  have read : restrictToInterval (1 / 4) (burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)) x =
    burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) x := hrestriction
  rw [read, hsource]

private theorem tate_inner_equality_gives_outer (left right : BurnolL2)
    (same : restrictToInterval (1 / 4) (burnolTateReciprocalL2 left) =
      restrictToInterval (1 / 4) (burnolTateReciprocalL2 right)) :
    ∀ᵐ x : ℝ ∂volume, (4 : ℝ) < |x| → left x = right x := by
  let window := symmetricInterval (1 / 4 : ℝ)
  have restricted : (burnolTateReciprocalL2 left : ℝ → ℂ) =ᵐ[volume.restrict window]
      (burnolTateReciprocalL2 right : ℝ → ℂ) := by
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ window (burnolTateReciprocalL2 left),
      LpToLpRestrictCLM_coeFn ℂ window (burnolTateReciprocalL2 right)] with x hl hr
    have leftRead : restrictToInterval (1 / 4) (burnolTateReciprocalL2 left) x =
      burnolTateReciprocalL2 left x := hl
    have rightRead : restrictToInterval (1 / 4) (burnolTateReciprocalL2 right) x =
      burnolTateReciprocalL2 right x := hr
    rw [← leftRead, same, rightRead]
  have whole := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp restricted
  have masked : window.indicator (burnolTateReciprocalL2 left : ℝ → ℂ) =ᵐ[volume]
      window.indicator (burnolTateReciprocalL2 right : ℝ → ℂ) := by
    filter_upwards [whole] with x hx
    by_cases inside : x ∈ window
    · rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside, hx inside]
    · rw [Set.indicator_of_notMem inside, Set.indicator_of_notMem inside]
  have pulled := burnolTateReciprocalRaw_ae_congr
    ((Lp.memLp (burnolTateReciprocalL2 left)).indicator
      (measurableSet_symmetricInterval (1 / 4 : ℝ)))
    ((Lp.memLp (burnolTateReciprocalL2 right)).indicator
      (measurableSet_symmetricInterval (1 / 4 : ℝ))) masked
  have leftRead := burnolTateReciprocalL2_coeFn (burnolTateReciprocalL2 left)
  have rightRead := burnolTateReciprocalL2_coeFn (burnolTateReciprocalL2 right)
  rw [burnolTateReciprocalL2_involutive] at leftRead rightRead
  filter_upwards [leftRead, rightRead, pulled] with x hl hr hp
  intro outside
  have positive : 0 < |x| := lt_trans (by norm_num) outside
  have small : |x⁻¹| ≤ (1 / 4 : ℝ) := by
    rw [abs_inv, inv_eq_one_div, div_le_iff₀ positive]
    linarith
  have inside : x⁻¹ ∈ window := abs_le.mp small
  unfold burnolTateReciprocalRaw at hl hr hp
  rw [Set.indicator_of_mem inside, Set.indicator_of_mem inside] at hp
  exact hl.trans (hp.trans hr.symm)

theorem burnolCompleteFirstSource_unitOuter (coordinate : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, (4 : ℝ) < |x| →
      burnolCompleteRemainderSource (coordinate.value / 2)
          (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1 x =
        -(((|x| : ℝ) : ℂ) ^ (-coordinate.value)) := by
  have outer := tate_inner_equality_gives_outer _ _ (burnolCompleteFirstSourceTate_unitState coordinate)
  filter_upwards [outer, burnolNormalizedFirstSourceUnitTail_coeFn coordinate] with x hsource htail
  intro outside
  rw [hsource outside, htail]
  exact if_pos outside

theorem burnolCompleteFirstSource_sub_mobius_unitOuter
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
    ∀ᵐ x : ℝ ∂volume, (4 : ℝ) < |x| →
      (burnolCompleteRemainderSource (coordinate.value / 2)
          (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1 -
        burnolMobiusSourceL2 value : BurnolL2) x =
      -(((|x| : ℝ) : ℂ) ^ (-coordinate.value)) := by
  filter_upwards [burnolCompleteFirstSource_unitOuter coordinate,
    Lp.coeFn_sub (burnolCompleteRemainderSource (coordinate.value / 2)
      (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1)
        (burnolMobiusSourceL2 value),
    burnolRadiusZeroExtension_coe (burnolMobiusWindowSourceRead value)]
      with x hsource hsub hext
  intro outside
  have notInside : x ∉ symmetricInterval (4 : ℝ) := by
    intro inside
    exact (not_le_of_gt outside) (abs_le.mpr inside)
  have extension : burnolMobiusSourceL2 value x =
      (symmetricInterval (4 : ℝ)).indicator (fun t => burnolMobiusWindowSourceRead value t) x := hext
  rw [Set.indicator_of_notMem notInside] at extension
  rw [hsub]
  change burnolCompleteRemainderSource (coordinate.value / 2)
    (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1 x -
      burnolMobiusSourceL2 value x = _
  rw [hsource outside, extension, sub_zero]

theorem burnolCompleteFirstSource_ne_mobiusSource
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolPaAmbientCarrier) :
    burnolCompleteRemainderSource (coordinate.value / 2)
        (burnolCoordinateNormalizedAnnulusSource (1 - coordinate.value)) 1 ≠
      burnolMobiusSourceL2 value := by
  intro same
  have outer := burnolCompleteFirstSource_sub_mobius_unitOuter coordinate value
  rw [same, sub_self] at outer
  have impossible : ∀ᵐ x : ℝ ∂volume.restrict (Ioo (5 : ℝ) 6), False := by
    filter_upwards [ae_restrict_of_ae outer,
      ae_restrict_of_ae (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)),
      ae_restrict_mem measurableSet_Ioo] with x hx hzero inside
    have positive : 0 < x := lt_trans (by norm_num) inside.1
    have outside : (4 : ℝ) < |x| := by rw [abs_of_pos positive]; linarith [inside.1]
    have actual := hx outside
    have zeroValue : (0 : BurnolL2) x = (0 : ℂ) := hzero
    rw [zeroValue, eq_neg_iff_add_eq_zero, zero_add] at actual
    exact (Complex.cpow_ne_zero_iff.mpr (Or.inl
      (Complex.ofReal_ne_zero.mpr (abs_pos.mpr positive.ne').ne'))) actual
  have measureZero : (volume.restrict (Ioo (5 : ℝ) 6)) univ = 0 := by
    simpa only [ae_iff, not_false_eq_true, ofPred_true] using impossible
  norm_num at measureZero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
