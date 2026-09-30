import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Smooth test functions supported strictly inside an open finite-dimensional chart. -/

namespace LowEnergy.OpenChartTestDomain

open MeasureTheory Set Function TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff Manifold

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_continuous_approx (Ω : Opens E) (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] {p : ℝ≥0∞} (hp : p ≠ ⊤)
    {f : Ω → F} (hf : HasCompactSupport f) (hc : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      tsupport g ⊆ (Ω : Set E) ∧ HasCompactSupport (fun x : Ω => g x) ∧
      eLpNorm (f - fun x : Ω => g x) p μ ≤ ENNReal.ofReal ε := by
  by_cases hf0 : f =ᵐ[μ] 0
  · refine ⟨0, HasCompactSupport.zero, contDiff_const, ?_, HasCompactSupport.zero, ?_⟩
    · simp
    · change eLpNorm (f - 0) p μ ≤ ENNReal.ofReal ε
      rw [sub_zero, eLpNorm_congr_ae hf0, eLpNorm_zero]
      exact bot_le
  have hs₁ : μ (tsupport f) ≠ ⊤ := hf.measure_lt_top.ne
  have hs₂ : 0 < (μ (tsupport f)).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hf0
    exact ENNReal.toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hf0)).ne' hs₁
  let ε' := ε * (μ (tsupport f)).toReal ^ (-(1 / p.toReal))
  have hε' : 0 < ε' := by positivity
  have hbound : ENNReal.ofReal ε' * μ (tsupport f) ^ (1 / p.toReal) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hs₁, ENNReal.ofReal_rpow_of_pos hs₂,
      ← ENNReal.ofReal_mul hε'.le, ENNReal.ofReal_le_ofReal_iff hε.le]
    dsimp [ε']
    rw [mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel, Real.rpow_zero, mul_one]
  let extended : E → F := Subtype.val.extend f 0
  have hec : Continuous extended := HasCompactSupport.continuous_extend_zero Ω.isOpen hc hf
  have hek : HasCompactSupport extended := hf.extend_zero continuous_subtype_val
  have hes : tsupport extended ⊆ (Ω : Set E) :=
    (hf.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  have heeq : (fun x : Ω => extended x) = f := by
    funext x
    exact Subtype.val_injective.extend_apply _ _ x
  obtain ⟨g, hgc, hgdist, hgsupp⟩ := hec.exists_contDiff_approx ⊤
    (ε := fun _ => ε') continuous_const (fun _ => hε')
  have hgsub : support (fun x : Ω => g x) ⊆ support f := by
    intro x hx
    have hx' := hgsupp hx
    simpa only [Function.mem_support, ← congrFun heeq x] using hx'
  refine ⟨g, hek.mono hgsupp, hgc, (closure_mono hgsupp).trans hes, hf.mono hgsub, ?_⟩
  refine (eLpNorm_sub_le_of_dist_bdd μ hp hf.measurableSet hε'.le ?_
    (subset_tsupport f) (hgsub.trans (subset_tsupport f))).trans hbound
  intro x
  rw [dist_comm]
  simpa only [← congrFun heeq x] using (hgdist (x : E)).le

theorem memLp_approx (Ω : Opens E) (μ : Measure Ω) [μ.Regular]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₁ : 1 ≤ p)
    {f : Ω → F} (hf : MemLp f p μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      tsupport g ⊆ (Ω : Set E) ∧ HasCompactSupport (fun x : Ω => g x) ∧
      eLpNorm (f - fun x : Ω => g x) p μ ≤ ENNReal.ofReal ε := by
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hhalf : 0 < ε / 2 := by positivity
  have hhalf' : 0 < ENNReal.ofReal (ε / 2) := by positivity
  obtain ⟨g, hgk, hgnorm, hgc, hgm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hp hhalf'.ne'
  obtain ⟨g', hg'k, hg'c, hg's, hg'Ω, hg'norm⟩ :=
    compact_continuous_approx Ω μ hp hgk hgc hhalf
  refine ⟨g', hg'k, hg'c, hg's, hg'Ω, ?_⟩
  have hg'm : MemLp (fun x : Ω => g' x) p μ :=
    (hg'c.continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport hg'Ω
  have heq : (f - fun x : Ω => g' x) = (f - g) + (g - fun x : Ω => g' x) := by
    ext x
    simp
  rw [heq]
  calc
    eLpNorm ((f - g) + (g - fun x : Ω => g' x)) p μ ≤
        eLpNorm (f - g) p μ + eLpNorm (g - fun x : Ω => g' x) p μ :=
      eLpNorm_add_le (hf.aestronglyMeasurable.sub hgm.aestronglyMeasurable)
        (hgm.aestronglyMeasurable.sub hg'm.aestronglyMeasurable) hp₁
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hgnorm hg'norm
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

theorem dense_compact_contDiff_inside (Ω : Opens E) (μ : Measure Ω) [μ.Regular]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) [Fact (1 ≤ p)] :
    Dense {f : Lp F p μ | ∃ g : E → F,
      f =ᵐ[μ] (fun x : Ω => g x) ∧ HasCompactSupport g ∧
      ContDiff ℝ ∞ g ∧ tsupport g ⊆ (Ω : Set E)} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hgk, hgc, hgs, hgΩ, hnorm⟩ :=
    memLp_approx Ω μ hp (Fact.out : 1 ≤ p) (Lp.memLp f) hε
  have hgm : MemLp (fun x : Ω => g x) p μ :=
    (hgc.continuous.comp continuous_subtype_val).memLp_of_hasCompactSupport hgΩ
  refine ⟨hgm.toLp _, ⟨g, hgm.coeFn_toLp, hgk, hgc, hgs⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le
      ((Lp.memLp f).sub (Lp.memLp hgm.toLp)).eLpNorm_ne_top hε.le]
  convert hnorm using 1
  apply eLpNorm_congr_ae
  filter_upwards [hgm.coeFn_toLp] with x hx
  exact congrArg (fun y => f x - y) hx

end LowEnergy.OpenChartTestDomain
