import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.FirstSourceSplit
import H0mework.Versions.V2.Arithmetic.MellinProjection.GapTailDilation

/-! Actual dilation emits the measured internal current and an occupied moving unit shell. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

local instance canonicalSource2AmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolRadiusNormalizedUnitTail (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) : BurnolL2 :=
  let tail := burnolRadiusMellinTailKernelL2 radius positive (star coordinate.value)
    (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)
  show BurnolL2 from -(tail + reflectL2 tail)

theorem burnolNormalizedFirstSourceUnitTail_dilation (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolMultiplicativeDilation (-shift / 2) (burnolNormalizedFirstSourceUnitTail coordinate) =
      positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift •
        burnolRadiusNormalizedUnitTail coordinate (4 * Real.exp (shift / 2)) (by positivity) := by
  let dual : BurnolCompletedMellinCoordinate := ⟨star coordinate.value,
    by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf,
    by simpa only [Complex.star_def, Complex.conj_re] using coordinate.belowOne⟩
  have actual := burnolRadiusMellinTail_dilation (by norm_num : (0 : ℝ) < 4) dual (-shift / 2)
  have character : fullMellinTranslationCharacter (star dual.value) (-shift / 2) =
      positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift := by
    dsimp only [dual]
    rw [star_star]
    unfold fullMellinTranslationCharacter positiveMellinQuarterRightResolventCharacter
      positiveMellinQuarterRightResolventWeight
    congr 1
    push_cast
    ring
  rw [character, show -(-shift / 2) = shift / 2 by ring] at actual
  dsimp only [dual] at actual
  unfold burnolNormalizedFirstSourceUnitTail burnolRadiusNormalizedUnitTail
  dsimp only
  rw [map_neg, map_add, ← reflectL2_burnolMultiplicativeDilation, actual,
    map_smul, ← smul_add, smul_neg]

theorem burnolAnalyticComplementFirstPaSource_current {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) :
    let value := burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    let character := positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift
    let internal := burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection value)
    let source := burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation) 1 -
      burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection value)
    burnolMultiplicativeDilation (-shift / 2) source - character • source =
      (burnolMultiplicativeDilation (-shift / 2) internal - character • internal) +
        character • (burnolRadiusNormalizedUnitTail coordinate (4 * Real.exp (shift / 2)) (by positivity) -
          burnolNormalizedFirstSourceUnitTail coordinate) := by
  dsimp only
  rw [burnolAnalyticComplementFirstPaSource_split observation nontrivial rightHalf,
    map_add, smul_add, burnolNormalizedFirstSourceUnitTail_dilation, smul_sub]
  dsimp only [burnolDivisionZeroCompletedMellinCoordinate]
  abel

private theorem radiusTail_positiveRead (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positiveRadius : 0 < radius) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → burnolRadiusNormalizedUnitTail coordinate radius positiveRadius x =
      if radius < x then -(x : ℂ) ^ (-coordinate.value) else 0 := by
  let tail := burnolRadiusMellinTailKernelL2 radius positiveRadius (star coordinate.value)
    (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)
  have tailRead : (tail : ℝ → ℂ) =ᵐ[volume]
      burnolRadiusMellinTailKernelRaw radius (star coordinate.value) :=
    (burnolRadiusMellinTailKernelRaw_memLp positiveRadius (star coordinate.value)
      (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)).coeFn_toLp
  filter_upwards [Lp.coeFn_neg (tail + reflectL2 tail), Lp.coeFn_add tail (reflectL2 tail),
    Lp.coeFn_compMeasurePreserving tail negMeasurePreserving,
    tailRead, negMeasurePreserving.quasiMeasurePreserving.ae tailRead]
      with x hneg hadd href hleft hright
  intro positive
  change (-(tail + reflectL2 tail) : BurnolL2) x = _
  rw [hneg]
  change -(tail + reflectL2 tail : BurnolL2) x = _
  rw [hadd]
  change -(tail x + reflectL2 tail x) = _
  have reflection : reflectL2 tail x = tail (-x) := href
  rw [reflection, hleft, hright]
  unfold burnolRadiusMellinTailKernelRaw
  have outside : ¬ -x ∈ Ioi radius := by simp only [mem_Ioi]; linarith
  rw [if_neg outside, add_zero]
  simp only [mem_Ioi, star_star]
  split_ifs <;> simp

theorem burnolNormalizedFirstSourceUnitTail_current_ne_zero (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (positive : 0 < shift) :
    burnolMultiplicativeDilation (-shift / 2) (burnolNormalizedFirstSourceUnitTail coordinate) -
      positiveMellinQuarterRightResolventCharacter (coordinate.value / 2) shift •
        burnolNormalizedFirstSourceUnitTail coordinate ≠ 0 := by
  let radius := 4 * Real.exp (shift / 2)
  have larger : (4 : ℝ) < radius := by
    have growing := Real.one_lt_exp_iff.mpr (show 0 < shift / 2 by linarith)
    dsimp only [radius]
    linarith
  have positiveRadius : 0 < radius := (by norm_num : (0 : ℝ) < 4).trans larger
  have distinct : burnolRadiusNormalizedUnitTail coordinate radius positiveRadius ≠
      burnolNormalizedFirstSourceUnitTail coordinate := by
    intro same
    have sourceRead := radiusTail_positiveRead coordinate radius positiveRadius
    have impossible : ∀ᵐ x : ℝ ∂volume.restrict (Ioo (4 : ℝ) radius), False := by
      filter_upwards [ae_restrict_of_ae sourceRead,
        ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_coeFn coordinate),
        ae_restrict_mem measurableSet_Ioo] with x hsource htail inside
      have xPositive : 0 < x := (by norm_num : (0 : ℝ) < 4).trans inside.1
      have actual := hsource xPositive
      rw [same, htail, if_neg (not_lt.mpr inside.2.le)] at actual
      unfold burnolNormalizedFirstSourceUnitTailRaw at actual
      rw [abs_of_pos xPositive, if_pos inside.1, neg_eq_zero] at actual
      exact (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr xPositive.ne'))) actual
    have measureZero : (volume.restrict (Ioo (4 : ℝ) radius)) univ = 0 := by
      simpa only [ae_iff, not_false_eq_true, ofPred_true] using impossible
    have notLarger : radius ≤ 4 := by
      simpa only [Measure.restrict_apply_univ, Real.volume_Ioo, ENNReal.ofReal_eq_zero,
        sub_nonpos] using measureZero
    exact not_le_of_gt larger notLarger
  rw [burnolNormalizedFirstSourceUnitTail_dilation, ← smul_sub]
  apply smul_ne_zero
  · exact Complex.exp_ne_zero _
  · exact sub_ne_zero.mpr distinct

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
