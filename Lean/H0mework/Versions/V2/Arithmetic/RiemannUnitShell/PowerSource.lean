import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Weighted

/-! The actual power unit shell is the weighted reciprocal-step source, with its original coefficient and endpoints. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def burnolUnitPowerWeight (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ :=
  -(t : ℂ) ^ (coordinate.value - 1)

def burnolUnitPowerSlope (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) : ℂ :=
  -(coordinate.value - 1) * ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 2)

theorem burnolUnitPowerSlope_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (burnolUnitPowerSlope coordinate) := by
  have base : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ)) := by fun_prop
  have powered : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 2)) :=
    continuousOn_univ.mp (base.continuousOn.cpow_const (fun t _ =>
      Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))))
  exact continuous_const.mul powered

theorem burnolUnitPowerWeight_derivative (coordinate : BurnolCompletedMellinCoordinate)
    {t : ℝ} (lower : (1 / 4 : ℝ) ≤ t) :
    HasDerivAt (burnolUnitPowerWeight coordinate) (burnolUnitPowerSlope coordinate t) t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) lower
  have exponentNonzero : coordinate.value - 1 ≠ 0 := by
    intro zero
    have equal := sub_eq_zero.mp zero
    have below := coordinate.belowOne
    rw [equal] at below
    norm_num at below
  have derivative := (hasDerivAt_ofReal_cpow_const positive.ne' exponentNonzero).neg
  have slope : -(coordinate.value - 1) * (t : ℂ) ^ (coordinate.value - 2) =
      -((coordinate.value - 1) * (t : ℂ) ^ (coordinate.value - 1 - 1)) := by
    rw [show coordinate.value - 1 - 1 = coordinate.value - 2 by ring, neg_mul]
  unfold burnolUnitPowerWeight burnolUnitPowerSlope
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith), slope]
  exact derivative

theorem burnolRadiusUnitTail_coeFn (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) :
    (burnolRadiusNormalizedUnitTail coordinate radius positive : ℝ → ℂ) =ᵐ[volume]
      fun x : ℝ => if radius < |x| then -((|x| : ℝ) : ℂ) ^ (-coordinate.value) else 0 := by
  let tail := burnolRadiusMellinTailKernelL2 radius positive (star coordinate.value)
    (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)
  have tailRead : (tail : ℝ → ℂ) =ᵐ[volume]
      burnolRadiusMellinTailKernelRaw radius (star coordinate.value) :=
    (burnolRadiusMellinTailKernelRaw_memLp positive (star coordinate.value)
      (by simpa only [Complex.star_def, Complex.conj_re] using coordinate.rightHalf)).coeFn_toLp
  filter_upwards [Lp.coeFn_neg (tail + reflectL2 tail), Lp.coeFn_add tail (reflectL2 tail),
    Lp.coeFn_compMeasurePreserving tail negMeasurePreserving, tailRead,
    negMeasurePreserving.quasiMeasurePreserving.ae tailRead]
      with x negAt addAt reflectionAt leftAt rightAt
  change (-(tail + reflectL2 tail) : BurnolL2) x = _
  rw [negAt]
  change -(tail + reflectL2 tail : BurnolL2) x = _
  rw [addAt]
  change -(tail x + reflectL2 tail x) = _
  have reflected : reflectL2 tail x = tail (-x) := reflectionAt
  rw [reflected, leftAt, rightAt]
  unfold burnolRadiusMellinTailKernelRaw
  simp only [star_star, mem_Ioi]
  by_cases nonnegative : 0 ≤ x
  · rw [abs_of_nonneg nonnegative, if_neg (by linarith : ¬ radius < -x), add_zero]
    split_ifs <;> simp
  · rw [abs_of_neg (lt_of_not_ge nonnegative), if_neg (by linarith : ¬ radius < x), zero_add]
    split_ifs <;> simp

theorem burnolUnitPowerWeight_reciprocal (coordinate : BurnolCompletedMellinCoordinate)
    {x : ℝ} (nonzero : x ≠ 0) :
    burnolUnitPowerWeight coordinate (|x|⁻¹) * ((|x| : ℝ) : ℂ)⁻¹ =
      -((|x| : ℝ) : ℂ) ^ (-coordinate.value) := by
  have positive := abs_pos.mpr nonzero
  have baseNonzero : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have reciprocalNonzero : ((|x| : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero baseNonzero
  unfold burnolUnitPowerWeight
  rw [Complex.ofReal_inv, neg_mul, Complex.cpow_sub _ _ reciprocalNonzero,
    Complex.cpow_one, div_mul_cancel₀ _ reciprocalNonzero,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg positive.le]; exact ne_of_lt Real.pi_pos),
    ← Complex.cpow_neg]

theorem burnolUnitPowerStep_rawShell (coordinate : BurnolCompletedMellinCoordinate) (radius x : ℝ)
    (positive : 0 < radius) (belowFour : radius < 4) :
    burnolUnitPowerWeight coordinate (|x|⁻¹) * burnolReciprocalStepSourceRaw (1 / 4) radius⁻¹ x =
      (if radius < |x| then -((|x| : ℝ) : ℂ) ^ (-coordinate.value) else 0) -
        (if (4 : ℝ) < |x| then -((|x| : ℝ) : ℂ) ^ (-coordinate.value) else 0) := by
  by_cases zero : x = 0
  · norm_num [zero, burnolReciprocalStepSourceRaw, not_lt.mpr positive.le]
  have absPositive := abs_pos.mpr zero
  have condition : (1 / 4 : ℝ) ≤ |x|⁻¹ ∧ |x|⁻¹ < radius⁻¹ ↔
      |x| ≤ 4 ∧ radius < |x| := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) absPositive,
      inv_lt_inv₀ absPositive positive]
  unfold burnolReciprocalStepSourceRaw
  simp only [condition]
  by_cases outside : (4 : ℝ) < |x|
  · simp [outside, not_le_of_gt outside, belowFour.trans outside]
  · have bounded := le_of_not_gt outside
    by_cases above : radius < |x|
    · rw [if_pos ⟨bounded, above⟩, if_pos above, if_neg outside, sub_zero]
      exact burnolUnitPowerWeight_reciprocal coordinate zero
    · simp [outside, above]

theorem burnolUnitPowerStep_source_eq_actualShell (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positive : 0 < radius) (belowFour : radius < 4) :
    burnolWeightedReciprocalStepSource (1 / 4) radius⁻¹ (burnolUnitPowerWeight coordinate) (burnolUnitPowerSlope coordinate) =
      burnolRadiusNormalizedUnitTail coordinate radius positive - burnolNormalizedFirstSourceUnitTail coordinate := by
  have ordered : (1 / 4 : ℝ) ≤ radius⁻¹ := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive]
    exact belowFour.le
  have rawRead : (burnolRadiusNormalizedUnitTail coordinate radius positive -
      burnolNormalizedFirstSourceUnitTail coordinate : BurnolL2) =ᵐ[volume]
      fun x : ℝ => burnolUnitPowerWeight coordinate (|x|⁻¹) *
        burnolReciprocalStepSourceRaw (1 / 4) radius⁻¹ x := by
    filter_upwards [Lp.coeFn_sub (burnolRadiusNormalizedUnitTail coordinate radius positive)
      (burnolNormalizedFirstSourceUnitTail coordinate), burnolRadiusUnitTail_coeFn coordinate radius positive,
      burnolNormalizedFirstSourceUnitTail_coeFn coordinate] with x differenceAt radiusAt fourAt
    rw [differenceAt]
    change burnolRadiusNormalizedUnitTail coordinate radius positive x -
      burnolNormalizedFirstSourceUnitTail coordinate x = _
    rw [radiusAt, fourAt]
    exact (burnolUnitPowerStep_rawShell coordinate radius x positive belowFour).symm
  apply ext_inner_left ℂ
  intro test
  rw [burnolWeightedReciprocalStepSource_pairing (1 / 4) radius⁻¹
    (burnolUnitPowerWeight coordinate) (burnolUnitPowerSlope coordinate) (by norm_num) ordered
    (fun u inside => burnolUnitPowerWeight_derivative coordinate inside.1)
    (burnolUnitPowerSlope_continuous coordinate).continuousOn (burnolUnitPowerSlope_continuous coordinate).measurable,
    L2.inner_def]
  exact integral_congr_ae (rawRead.mono (fun x hx => congrArg (inner ℂ (test x)) hx.symm))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
