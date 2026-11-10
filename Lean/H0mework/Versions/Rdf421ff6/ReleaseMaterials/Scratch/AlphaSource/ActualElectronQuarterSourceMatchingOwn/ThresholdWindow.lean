import H0mework.Versions.R2cccd55f.ReleaseMaterials.SaturationMonoid.PhysicsCore.LowEnergy.EulerDiagonal.Window
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! An explicit member of the original quarter-window test contract.  Its
cutoff uses the inner-product bump formula directly, without choosing a bump
base through `HasContDiffBump`. -/
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology ContDiff ENNReal
namespace SaturationMonoid.PhysicsCore.LowEnergy.ThresholdWindow
noncomputable section

open EulerDiagonal

def canonicalQuarterCutoff (t : ℝ) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace ℝ).toFun 2 (16 * (t - 1/4))

theorem canonicalQuarterCutoff_formula (t : ℝ) :
    canonicalQuarterCutoff t = Real.smoothTransition (2 - 16 * |t - 1/4|) := by
  norm_num [canonicalQuarterCutoff, ContDiffBumpBase.ofInnerProductSpace,
    Real.norm_eq_abs, abs_mul]

theorem canonicalQuarterCutoff_smooth : ContDiff ℝ ∞ canonicalQuarterCutoff := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have smooth : ContDiffAt ℝ ∞
      (Function.uncurry (ContDiffBumpBase.ofInnerProductSpace ℝ).toFun)
      (2, 16*(t-1/4)) := (ContDiffBumpBase.ofInnerProductSpace ℝ).smooth.contDiffAt
    (prod_mem_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)) univ_mem)
  change ContDiffAt ℝ ∞
    ((Function.uncurry (ContDiffBumpBase.ofInnerProductSpace ℝ).toFun) ∘
      fun t : ℝ => (2, 16*(t-1/4))) t
  exact smooth.comp t
    (contDiffAt_const.prodMk (contDiffAt_const.mul (contDiffAt_id.sub contDiffAt_const)))

theorem canonicalQuarterCutoff_plateau (t : ℝ) (h : |t - 1/4| ≤ 1/16) :
    canonicalQuarterCutoff t = 1 := by
  rw [canonicalQuarterCutoff_formula]
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem canonicalQuarterCutoff_zero (t : ℝ) (h : 1/8 ≤ |t - 1/4|) :
    canonicalQuarterCutoff t = 0 := by
  rw [canonicalQuarterCutoff_formula]
  exact Real.smoothTransition.zero_iff_nonpos.mpr (by linarith)

theorem canonicalQuarterCutoff_support :
    tsupport canonicalQuarterCutoff ⊆ Icc (1/8 : ℝ) (3/8) := by
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  have hn : canonicalQuarterCutoff t ≠ 0 := ht
  have hlt : |t - 1/4| < 1/8 := lt_of_not_ge fun h => hn (canonicalQuarterCutoff_zero t h)
  rcases abs_lt.mp hlt with ⟨hl, hr⟩
  constructor <;> linarith

def canonicalQuarterTest : TimeTest where
  cutoff := canonicalQuarterCutoff
  smooth := canonicalQuarterCutoff_smooth
  compact := isCompact_Icc.of_isClosed_subset isClosed_closure canonicalQuarterCutoff_support
  future := by
    intro t ht
    have lower := (canonicalQuarterCutoff_support ht).1
    change 0 < t
    linarith

theorem canonicalQuarterTest_formula (t : ℝ) :
    canonicalQuarterTest.cutoff t = Real.smoothTransition (2 - 16 * |t - 1/4|) :=
  canonicalQuarterCutoff_formula t

theorem canonicalQuarterTest_center : canonicalQuarterTest.cutoff (1/4) = 1 :=
  canonicalQuarterCutoff_plateau _ (by norm_num)

def QuarterContract (test : TimeTest) : Prop :=
  tsupport test.cutoff ⊆ Icc (1/8 : ℝ) (3/8) ∧ test.cutoff (1/4) = 1

theorem canonicalQuarterTest_contract : QuarterContract canonicalQuarterTest :=
  ⟨canonicalQuarterCutoff_support, canonicalQuarterTest_center⟩

theorem originalQuarterTest_contract : QuarterContract (testAt (1/4) (by norm_num)) := by
  constructor
  · intro t ht
    change t ∈ tsupport (testBump (1/4) (by norm_num)) at ht
    rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at ht
    change |t - 1/4| ≤ (1/4 : ℝ)/2 at ht
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  · exact testAt_center _ _

def momentDensity (test : TimeTest) (damping t : ℝ) : ℝ :=
  test.cutoff t ^ 2 * Real.exp (-2*damping*t)

def M0 (test : TimeTest) (damping : ℝ) : ℝ := ∫ t, momentDensity test damping t

def M2 (test : TimeTest) (damping : ℝ) : ℝ := ∫ t, t^2 * momentDensity test damping t

theorem momentDensity_continuous (test : TimeTest) (damping : ℝ) :
    Continuous (momentDensity test damping) := by
  unfold momentDensity
  exact (test.smooth.continuous.pow 2).mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem momentDensity_compact (test : TimeTest) (damping : ℝ) :
    HasCompactSupport (momentDensity test damping) := by
  apply test.compact.mono
  intro t ht
  contrapose! ht
  simp only [Function.mem_support] at ht ⊢
  simp [momentDensity, ht]

theorem momentDensity_nonneg (test : TimeTest) (damping t : ℝ) :
    0 ≤ momentDensity test damping t := by
  unfold momentDensity
  positivity

theorem M0_pos (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    0 < M0 test damping := by
  apply (momentDensity_continuous test damping).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (momentDensity_compact test damping) (momentDensity_nonneg test damping)
  show momentDensity test damping (1/4) ≠ 0
  dsimp only [momentDensity]
  rw [window.2]
  positivity

theorem M2_pos (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    0 < M2 test damping := by
  have hc : Continuous (fun t : ℝ => t^2 * momentDensity test damping t) :=
    (continuous_id.pow 2).mul (momentDensity_continuous test damping)
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (momentDensity_compact test damping).mul_left
    (fun t => mul_nonneg (sq_nonneg t) (momentDensity_nonneg test damping t))
  show (1/4 : ℝ)^2 * momentDensity test damping (1/4) ≠ 0
  dsimp only [momentDensity]
  rw [window.2]
  positivity

theorem M2_le (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    M2 test damping ≤ (9/64 : ℝ) * M0 test damping := by
  have hc := momentDensity_continuous test damping
  have hk := momentDensity_compact test damping
  have hi : Integrable (momentDensity test damping) volume :=
    hc.integrable_of_hasCompactSupport hk
  have h2 : Integrable (fun t : ℝ => t^2 * momentDensity test damping t) :=
    ((continuous_id.pow 2).mul hc).integrable_of_hasCompactSupport hk.mul_left
  have bound : ∀ t : ℝ, t^2 * momentDensity test damping t ≤
      (9/64 : ℝ) * momentDensity test damping t := by
    intro t
    by_cases hz : test.cutoff t = 0
    · simp [momentDensity, hz]
    · have ht := window.1 (subset_closure (show t ∈ Function.support test.cutoff from hz))
      have square : t^2 ≤ (9/64 : ℝ) := by nlinarith [ht.1, ht.2]
      exact mul_le_mul_of_nonneg_right square (momentDensity_nonneg test damping t)
  have result := integral_mono h2 (hi.const_mul (9/64 : ℝ)) bound
  simpa only [M2, M0, integral_const_mul] using result

theorem normalized_M2_le (test : TimeTest) (window : QuarterContract test) (damping : ℝ) :
    M2 test damping / M0 test damping ≤ (9/64 : ℝ) :=
  (div_le_iff₀ (M0_pos test window damping)).mpr (M2_le test window damping)

theorem canonicalQuarterTest_normalized_M2_le (damping : ℝ) :
    M2 canonicalQuarterTest damping / M0 canonicalQuarterTest damping ≤ (9/64 : ℝ) :=
  normalized_M2_le _ canonicalQuarterTest_contract damping

theorem originalQuarterTest_normalized_M2_le (damping : ℝ) :
    M2 (testAt (1/4) (by norm_num)) damping / M0 (testAt (1/4) (by norm_num)) damping ≤
      (9/64 : ℝ) :=
  normalized_M2_le _ originalQuarterTest_contract damping

theorem canonicalQuarterTest_tested_memLp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {field : ℝ → E} (continuousField : Continuous field) :
    MemLp (tested canonicalQuarterTest 5 field) 2 volume :=
  tested_memLp canonicalQuarterTest 5 continuousField 2

end
end SaturationMonoid.PhysicsCore.LowEnergy.ThresholdWindow
