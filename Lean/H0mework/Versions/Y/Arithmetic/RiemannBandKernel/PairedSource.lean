import H0mework.Versions.Y.Arithmetic.RiemannBandKernel.PairedProfile

/-! The paired response's same-source raw fold preserves all six faces and its actual mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology ArithmeticFunction
noncomputable section
private theorem forward_summable (raw : ℝ → ℂ)
    (gap : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → raw x = 0) (x : ℝ) :
    Summable (fun n : ℕ+ => (((n : ℕ) : ℂ)⁻¹) * raw (x / (n : ℕ))) := by
  have zero := gap (x := 0) (by norm_num)
  have quarter : ∀ {u : ℝ}, |u| ≤ (1 / 4 : ℝ) → raw u = raw 0 := by
    intro u small
    rw [gap small, zero]
  have joint : Summable (burnolCenteredMobiusReconstructionJointTerm raw x) := summable_of_hasFiniteSupport
    (burnolCenteredMobiusReconstructionJointTerm_finiteSupport raw quarter x)
  simpa only [Function.comp_def, burnolCenteredMobiusReconstructionJointTerm,
    burnolCenteredMobiusSummand, PNat.val_ofNat, Nat.cast_one, map_one, inv_one, div_one,
    zero, sub_zero, one_mul, ArithmeticFunction.moebius_apply_one, Int.cast_one] using
      joint.comp_injective (Prod.mk_left_injective (1 : ℕ+))

private theorem forward_sub (f g : ℝ → ℂ)
    (hf : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → f x = 0)
    (hg : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → g x = 0) (x : ℝ) :
    burnolInnerGapForward (fun u => f u - g u) x =
      burnolInnerGapForward f x - burnolInnerGapForward g x := by
  unfold burnolInnerGapForward
  simp only [mul_sub]
  exact (forward_summable f hf x).tsum_sub (forward_summable g hg x)

private theorem forward_add (f g : ℝ → ℂ)
    (hf : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → f x = 0)
    (hg : ∀ {x : ℝ}, |x| ≤ (1 / 4 : ℝ) → g x = 0) (x : ℝ) :
    burnolInnerGapForward (fun u => f u + g u) x =
      burnolInnerGapForward f x + burnolInnerGapForward g x := by
  unfold burnolInnerGapForward
  simp only [mul_add]
  exact (forward_summable f hf x).tsum_add (forward_summable g hg x)

private theorem forward_mul (f : ℝ → ℂ) (c : ℂ) (x : ℝ) :
    burnolInnerGapForward (fun u => c * f u) x = c * burnolInnerGapForward f x := by
  unfold burnolInnerGapForward
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

private theorem forward_scaled (f : ℝ → ℂ) (c x : ℝ) :
    burnolInnerGapForward (fun u => f (c * u)) x = burnolInnerGapForward f (c * x) := by
  unfold burnolInnerGapForward
  apply tsum_congr
  intro n
  dsimp only
  congr 2
  ring

private theorem forward_divided (f : ℝ → ℂ) (c x : ℝ) :
    burnolInnerGapForward (fun u => f (u / c)) x = burnolInnerGapForward f (x / c) := by
  unfold burnolInnerGapForward
  apply tsum_congr
  intro n
  dsimp only
  congr 2
  ring

private theorem unitDirichlet_forward (s : ℂ) (x : ℝ) :
    burnolUnitTailDirichletRaw s 1 x =
      burnolInnerGapForward (burnolRadiusUnitTailRaw s 1) x + 1 / s := by
  rw [burnolRadiusUnitTail_finiteCoSum s 1 x (by norm_num)]
  unfold burnolUnitTailDirichletRaw
  simp only [Complex.ofReal_one, Complex.one_cpow]
  ring

def burnolPaCombPairedRawSource (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  let b := 1 + burnolPaCombSourceWidth n
  ((n : ℂ) + 2) / s *
    (burnolRadiusUnitTailRaw s 1 (x / b) - burnolRadiusUnitTailRaw s 1 x -
      (b : ℂ) * burnolRadiusUnitTailRaw (1 - s) 1 (b * x) +
      burnolRadiusUnitTailRaw (1 - s) 1 x - burnolTateStepBoxRaw 1 b x -
      burnolReciprocalStepSourceRaw 1 b x)

def burnolPaCombPairedRawMean (s : ℂ) (n : ℕ) : ℂ :=
  let b := 1 + burnolPaCombSourceWidth n
  ((n : ℂ) + 2) / s * ((Real.log b : ℂ) + (b - 1 : ℂ) + (1 - b : ℂ) / (1 - s))

private theorem paired_source_gaps (s : ℂ) (n : ℕ) {x : ℝ}
    (small : |x| ≤ (1 + burnolPaCombSourceWidth n)⁻¹) :
    let b := 1 + burnolPaCombSourceWidth n
    burnolRadiusUnitTailRaw s 1 (x / b) = 0 ∧
    burnolRadiusUnitTailRaw s 1 x = 0 ∧
    burnolRadiusUnitTailRaw (1 - s) 1 (b * x) = 0 ∧
    burnolRadiusUnitTailRaw (1 - s) 1 x = 0 ∧
    burnolTateStepBoxRaw 1 b x = 0 ∧ burnolReciprocalStepSourceRaw 1 b x = 0 := by
  let b := 1 + burnolPaCombSourceWidth n
  have ordered : 1 ≤ b := by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1]
  have positive : 0 < b := lt_of_lt_of_le (by norm_num) ordered
  have inverseBound : b⁻¹ ≤ 1 := by
    rw [inv_le_comm₀ positive (by norm_num)]
    simpa only [inv_one] using ordered
  have unitBound : |x| ≤ 1 := small.trans inverseBound
  have strict : 1 < b := by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1]
  have inverseStrict : b⁻¹ < 1 := by
    simpa only [inv_one] using (inv_lt_inv₀ positive (by norm_num : (0 : ℝ) < 1)).mpr strict
  have unitStrict : |x| < 1 := small.trans_lt inverseStrict
  have divided : |x / b| ≤ 1 := by rw [abs_div, abs_of_pos positive, div_le_iff₀ positive]; linarith
  have scaled : |b * x| ≤ 1 := by
    rw [abs_mul, abs_of_pos positive]
    have product := mul_le_mul_of_nonneg_left small positive.le
    change b * |x| ≤ b * b⁻¹ at product
    simpa only [mul_inv_cancel₀ positive.ne'] using product
  have reciprocal : ¬ (1 ≤ |x|⁻¹ ∧ |x|⁻¹ < b) := by
    rintro ⟨above, below⟩
    have xp : 0 < |x| := by
      by_contra bad
      have zero : |x| = 0 := le_antisymm (le_of_not_gt bad) (abs_nonneg x)
      rw [zero, inv_zero] at above
      norm_num at above
    have invBound : b ≤ |x|⁻¹ := by
      simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr positive) xp).mpr small
    linarith
  dsimp only
  refine ⟨if_neg (by linarith), if_neg (by linarith), if_neg (by linarith),
    if_neg (by linarith), if_neg (fun h => by linarith [h.1]), if_neg reciprocal⟩

theorem burnolPaCombPairedRawSource_innerMargin (s : ℂ) (n : ℕ) {x : ℝ}
    (small : |x| ≤ (1 + burnolPaCombSourceWidth n)⁻¹) : burnolPaCombPairedRawSource s n x = 0 := by
  have gaps := paired_source_gaps s n small
  unfold burnolPaCombPairedRawSource
  dsimp only
  rw [gaps.1, gaps.2.1, gaps.2.2.1, gaps.2.2.2.1, gaps.2.2.2.2.1, gaps.2.2.2.2.2]
  ring

theorem burnolPaCombSource_inverseMargin (n : ℕ) : (2 / 3 : ℝ) ≤ (1 + burnolPaCombSourceWidth n)⁻¹ := by
  have positive : 0 < 1 + burnolPaCombSourceWidth n := by
    linarith [(burnolPaCombSourceWidth_bounds n).1]
  have bounded : 1 + burnolPaCombSourceWidth n ≤ (3 / 2 : ℝ) := by
    linarith [(burnolPaCombSourceWidth_bounds n).2]
  have inverse := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3 / 2) positive).mpr bounded
  norm_num at inverse
  exact inverse

theorem burnolPaCombPairedRawSource_innerGap (s : ℂ) (n : ℕ) {x : ℝ}
    (small : |x| ≤ (1 / 4 : ℝ)) : burnolPaCombPairedRawSource s n x = 0 :=
  burnolPaCombPairedRawSource_innerMargin s n
    (small.trans ((by norm_num : (1 / 4 : ℝ) ≤ 2 / 3).trans (burnolPaCombSource_inverseMargin n)))

theorem burnolPaCombPairedDirichletRaw_forward (s : ℂ) (n : ℕ) (x : ℝ) :
    burnolPaCombPairedDirichletRaw s n x =
      burnolInnerGapForward (burnolPaCombPairedRawSource s n) x + burnolPaCombPairedRawMean s n := by
  let b := 1 + burnolPaCombSourceWidth n
  let f1 := fun u => burnolRadiusUnitTailRaw s 1 (u / b)
  let f2 := burnolRadiusUnitTailRaw s 1
  let f3 := fun u => burnolRadiusUnitTailRaw (1 - s) 1 (b * u)
  let f4 := burnolRadiusUnitTailRaw (1 - s) 1
  let f5 := burnolTateStepBoxRaw 1 b
  let f6 := burnolReciprocalStepSourceRaw 1 b
  have gaps {u : ℝ} (small : |u| ≤ (1 / 4 : ℝ)) :=
    paired_source_gaps s n
      (small.trans ((by norm_num : (1 / 4 : ℝ) ≤ 2 / 3).trans (burnolPaCombSource_inverseMargin n)))
  have linearRead :
      burnolInnerGapForward (burnolPaCombPairedRawSource s n) x =
        ((n : ℂ) + 2) / s *
          (burnolInnerGapForward f1 x - burnolInnerGapForward f2 x -
            (b : ℂ) * burnolInnerGapForward f3 x + burnolInnerGapForward f4 x -
              burnolInnerGapForward f5 x - burnolInnerGapForward f6 x) := by
    change burnolInnerGapForward (fun u => ((n : ℂ) + 2) / s *
      (f1 u - f2 u - (b : ℂ) * f3 u + f4 u - f5 u - f6 u)) x = _
    rw [forward_mul, forward_sub, forward_sub, forward_add, forward_sub, forward_sub, forward_mul]
    all_goals intro u small
    all_goals
      have g := gaps small
      simp only [f1, f2, f3, f4, f5, f6, b,
        g.1, g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2,
        mul_zero, sub_zero, add_zero]
  rw [linearRead]
  dsimp only [f1, f2, f3, f4, f5, f6]
  rw [forward_divided, forward_scaled]
  unfold burnolPaCombPairedDirichletRaw burnolPaCombResponseDirichletRaw
    burnolPaCombFourierResponseDirichletRaw burnolPaCombPairedRawMean
  simp_rw [unitDirichlet_forward]
  rw [burnolReciprocalStepWave_coSum 1 b x (by norm_num)]
  have harmonic : burnolHarmonicStepWaveRaw 1 b x = burnolInnerGapForward (burnolTateStepBoxRaw 1 b) x -
      (Real.log b : ℂ) := by
    rw [burnolTateStepBox_finiteCoSum 1 b x (by norm_num) (by dsimp only [b]; linarith [(burnolPaCombSourceWidth_bounds n).1])]
    simp only [burnolHarmonicStepWaveRaw, div_one]
  rw [harmonic]
  dsimp only [b]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

def burnolUnitPairRawSource (s : ℂ) (x : ℝ) : ℂ :=
  burnolRadiusUnitTailRaw s 1 x - burnolRadiusUnitTailRaw (1 - s) 1 x

theorem burnolUnitPairRawSource_innerMargin (s : ℂ) {x : ℝ} (small : |x| ≤ 1) :
    burnolUnitPairRawSource s x = 0 := by
  simp only [burnolUnitPairRawSource, burnolRadiusUnitTailRaw, if_neg (not_lt.mpr small), sub_self]

theorem burnolUnitPairDirichletRaw_forward (s : ℂ) (x : ℝ) :
    burnolUnitTailDirichletRaw s 1 x - burnolUnitTailDirichletRaw (1 - s) 1 x =
      burnolInnerGapForward (burnolUnitPairRawSource s) x + (1 / s - 1 / (1 - s)) := by
  rw [unitDirichlet_forward, unitDirichlet_forward]
  change _ = burnolInnerGapForward
    (fun u => burnolRadiusUnitTailRaw s 1 u - burnolRadiusUnitTailRaw (1 - s) 1 u) x + _
  rw [forward_sub]
  · ring
  all_goals intro u small
  all_goals exact if_neg (by linarith)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
