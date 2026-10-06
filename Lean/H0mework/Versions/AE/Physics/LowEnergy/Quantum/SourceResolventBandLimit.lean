import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceBoundaryGram
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCutoffSharpCore
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Finite-frequency integration for the actual bounded mixed FullYSourceResolventGraphSplice.resolvent words. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceResolventBandLimit
open Filter MeasureTheory SourceFamilyHilbert SourceFamilyOperator
open FullYSourceResolventGraphSplice SourceBoundaryGram
open scoped Topology InnerProductSpace

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem resolvent_difference (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    FullYSourceResolventGraphSplice.resolvent C z-FullYSourceResolventGraphSplice.resolvent C w=(z-w) • (FullYSourceResolventGraphSplice.resolvent C z*FullYSourceResolventGraphSplice.resolvent C w) := by
  have he : (C-w • 1)-(C-z • 1)=(z-w) • (1 : E →L[ℂ] E) := by
    rw [sub_smul]
    abel
  calc
    _ = FullYSourceResolventGraphSplice.resolvent C z*((C-w • 1)-(C-z • 1))*FullYSourceResolventGraphSplice.resolvent C w := by
      rw [mul_sub,sub_mul,mul_assoc,resolvent_right C hC w hw,mul_one,
        resolvent_left C hC z hz,one_mul]
    _ = _ := by rw [he,mul_smul_comm,mul_one,smul_mul_assoc]

def line (μ t : ℝ) : ℂ := (t : ℂ)+(μ : ℂ)*Complex.I

theorem line_im (μ t : ℝ) : (line μ t).im=μ := by simp [line]

theorem line_difference (μ t s : ℝ) : ‖line μ t-line μ s‖=|t-s| := by
  have he : line μ t-line μ s=((t-s : ℝ) : ℂ) := by simp [line]
  rw [he,Complex.norm_real,Real.norm_eq_abs]

theorem line_resolvent_norm (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (t : ℝ) : ‖FullYSourceResolventGraphSplice.resolvent C (line μ t)‖ ≤ μ⁻¹ := by
  simpa only [line_im,abs_of_pos hμ,one_div] using
    resolvent_norm C hC (line μ t) (by simpa only [line_im] using ne_of_gt hμ)

theorem line_resolvent_difference (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (t s : ℝ) :
    ‖FullYSourceResolventGraphSplice.resolvent C (line μ t)-FullYSourceResolventGraphSplice.resolvent C (line μ s)‖ ≤ μ⁻¹*μ⁻¹*|t-s| := by
  rw [resolvent_difference C hC _ _ (by simpa only [line_im] using ne_of_gt hμ)
    (by simpa only [line_im] using ne_of_gt hμ),norm_smul,line_difference]
  have hb := mul_le_mul (line_resolvent_norm C hC μ hμ t)
    (line_resolvent_norm C hC μ hμ s) (norm_nonneg _) (by positivity : 0 ≤ μ⁻¹)
  exact (mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans hb) (abs_nonneg _)).trans_eq (by ring)

def word (C : E →L[ℂ] E) (μ t : ℝ) : List (E →L[ℂ] E) → E →L[ℂ] E
  | [] => FullYSourceResolventGraphSplice.resolvent C (line μ t)
  | A::L => FullYSourceResolventGraphSplice.resolvent C (line μ t)*A*word C μ t L

def size (μ : ℝ) : List (E →L[ℂ] E) → ℝ
  | [] => μ⁻¹
  | A::L => μ⁻¹*‖A‖*size μ L

def variation (μ : ℝ) : List (E →L[ℂ] E) → ℝ
  | [] => μ⁻¹*μ⁻¹
  | A::L => μ⁻¹*μ⁻¹*‖A‖*size μ L+μ⁻¹*‖A‖*variation μ L

omit [CompleteSpace E] in
theorem size_nonneg (μ : ℝ) (hμ : 0<μ) (L : List (E →L[ℂ] E)) : 0 ≤ size μ L := by
  induction L with
  | nil => exact le_of_lt (inv_pos.mpr hμ)
  | cons A L ih => change 0 ≤ μ⁻¹*‖A‖*size μ L; positivity

omit [CompleteSpace E] in
theorem variation_nonneg (μ : ℝ) (hμ : 0<μ) (L : List (E →L[ℂ] E)) :
    0 ≤ variation μ L := by
  induction L with
  | nil => change 0 ≤ μ⁻¹*μ⁻¹; positivity
  | cons A L ih =>
    change 0 ≤ μ⁻¹*μ⁻¹*‖A‖*size μ L+μ⁻¹*‖A‖*variation μ L
    have := size_nonneg μ hμ L
    positivity

theorem word_norm (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (L : List (E →L[ℂ] E)) (t : ℝ) :
    ‖word C μ t L‖ ≤ size μ L := by
  induction L with
  | nil => exact line_resolvent_norm C hC μ hμ t
  | cons A L ih =>
    change ‖(FullYSourceResolventGraphSplice.resolvent C (line μ t)*A)*word C μ t L‖ ≤ μ⁻¹*‖A‖*size μ L
    apply (norm_mul_le _ _).trans
    exact mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (line_resolvent_norm C hC μ hμ t) (norm_nonneg _)))
      ih (norm_nonneg _) (by positivity)

theorem word_difference (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (L : List (E →L[ℂ] E)) (t s : ℝ) :
    ‖word C μ t L-word C μ s L‖ ≤ variation μ L*|t-s| := by
  induction L with
  | nil => exact line_resolvent_difference C hC μ hμ t s
  | cons A L ih =>
    have he : word C μ t (A::L)-word C μ s (A::L)=
        (FullYSourceResolventGraphSplice.resolvent C (line μ t)-FullYSourceResolventGraphSplice.resolvent C (line μ s))*A*word C μ t L+
        FullYSourceResolventGraphSplice.resolvent C (line μ s)*A*(word C μ t L-word C μ s L) := by
      simp only [word,sub_mul,mul_sub]
      abel
    rw [he]
    have h₁ := mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (line_resolvent_difference C hC μ hμ t s) (norm_nonneg A)))
      (word_norm C hC μ hμ L t) (norm_nonneg _) (by positivity : 0 ≤ μ⁻¹*μ⁻¹*|t-s| *‖A‖)
    have h₂ := mul_le_mul
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (line_resolvent_norm C hC μ hμ s) (norm_nonneg A)))
      ih (norm_nonneg _) (by positivity : 0 ≤ μ⁻¹*‖A‖)
    apply (norm_add_le _ _).trans
    exact (add_le_add ((norm_mul_le _ _).trans h₁) ((norm_mul_le _ _).trans h₂)).trans_eq (by
      simp only [variation]; ring)

theorem word_square_lipschitz (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (L : List (E →L[ℂ] E)) (g : E) :
    LipschitzWith ⟨2*size μ L*variation μ L*‖g‖^2, by
      have := size_nonneg μ hμ L
      have := variation_nonneg μ hμ L
      positivity⟩ (fun t => ‖word C μ t L g‖^2) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  have ht : ‖word C μ t L g‖ ≤ size μ L*‖g‖ :=
    ((word C μ t L).le_opNorm g).trans (mul_le_mul_of_nonneg_right
      (word_norm C hC μ hμ L t) (norm_nonneg g))
  have hs : ‖word C μ s L g‖ ≤ size μ L*‖g‖ :=
    ((word C μ s L).le_opNorm g).trans (mul_le_mul_of_nonneg_right
      (word_norm C hC μ hμ L s) (norm_nonneg g))
  have hd : |‖word C μ t L g‖-‖word C μ s L g‖| ≤ variation μ L*|t-s| *‖g‖ := by
    apply (abs_norm_sub_norm_le _ _).trans
    change ‖(word C μ t L-word C μ s L) g‖ ≤ _
    exact ((word C μ t L-word C μ s L).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (word_difference C hC μ hμ L t s) (norm_nonneg g))
  change |‖word C μ t L g‖^2-‖word C μ s L g‖^2| ≤
    (2*size μ L*variation μ L*‖g‖^2)*|t-s|
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm (‖word C μ t L g‖+‖word C μ s L g‖)]
  calc
    _ ≤ (variation μ L*|t-s| *‖g‖)*(size μ L*‖g‖+size μ L*‖g‖) :=
      mul_le_mul hd (add_le_add ht hs) (by positivity) (by
        have := variation_nonneg μ hμ L
        positivity)
    _ = (2*size μ L*variation μ L*‖g‖^2)*|t-s| := by ring
end Operator

section Integration
variable {I : Type*} (l : Filter I) [NeBot l]

theorem band_integral_limit (f : I → ℝ → ℝ) (g : ℝ → ℝ) (L : NNReal)
    (hf : ∀ i, LipschitzWith L (f i)) (hg : ∀ t, Tendsto (fun i => f i t) l (𝓝 (g t)))
    (a b : ℝ) : Tendsto (fun i => ∫ t in a..b, f i t) l (𝓝 (∫ t in a..b, g t)) := by
  have hgl : LipschitzWith L g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact le_of_tendsto ((hg x).dist (hg y)) (Eventually.of_forall (fun i => (hf i).dist_le_mul x y))
  let S := Set.uIcc a b
  let : CompactSpace S := isCompact_iff_compactSpace.mp isCompact_uIcc
  have heq : Equicontinuous (fun i (x : S) => f i x) := by
    apply (LipschitzWith.uniformEquicontinuous _ L ?_).equicontinuous
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hf i).dist_le_mul x y
  have hu : TendstoUniformly (fun i (x : S) => f i x) (fun x => g x) l := by
    apply UniformFun.tendsto_iff_tendstoUniformly.mp
    exact (heq.tendsto_uniformFun_iff_pi l _).mpr (tendsto_pi_nhds.mpr (fun x => hg x))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(|b-a| +1)
  have hδ : 0<δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.mp hu δ hδ] with i hi
  have hb : ‖∫ t in a..b, f i t-g t‖ ≤ δ*|b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have hh := (hi ⟨t,Set.uIoc_subset_uIcc ht⟩).le
    simpa only [Real.dist_eq,Real.norm_eq_abs,abs_sub_comm] using hh
  rw [intervalIntegral.integral_sub ((hf i).continuous.intervalIntegrable a b)
    (hgl.continuous.intervalIntegrable a b)] at hb
  rw [dist_eq_norm]
  apply hb.trans_lt
  have hden : 0 < |b-a| +1 := by positivity
  dsimp [δ]
  rw [div_mul_eq_mul_div,div_lt_iff₀ hden]
  nlinarith
end Integration

open GaussCoreHilbert GaussDiagonalHistory
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)

def mixedLetter (a : Bool × ℕ) : H →L[ℂ] H :=
  if a.1 then (FullYSourceCutoffVolterra.cutoff a.2).adjoint
  else FullYSourceCutoffVolterra.cutoff a.2

def mixedWord (F : Index) (μ t : ℝ) (L : List (Bool × ℕ)) : H →L[ℂ] H :=
  word (GaussGradedCompression.compression F) μ t (L.map mixedLetter)

def wordFamily (μ : ℝ) (hμ : 0<μ) (L : List (Bool × ℕ)) (t : ℝ) : Operator Index H where
  component F := mixedWord F μ t L
  bounded := ⟨size μ (L.map mixedLetter),size_nonneg μ hμ _,fun F g =>
    ((mixedWord F μ t L).le_opNorm g).trans (mul_le_mul_of_nonneg_right
      (word_norm _ (GaussGradedCompression.compression_selfAdjoint F) μ hμ _ t) (norm_nonneg g))⟩

def wholeWord (μ : ℝ) (hμ : 0<μ) (L : List (Bool × ℕ)) (t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (wordFamily μ hμ L t)

theorem whole_word_nil (μ : ℝ) (hμ : 0<μ) (t : ℝ) :
    wholeWord μ hμ [] t=sameResolvent (line μ t) (by simpa only [line_im] using ne_of_gt hμ) :=
  lift_congr sourceFilter _ _ (fun _ => rfl)

theorem whole_word_cons (μ : ℝ) (hμ : 0<μ) (a : Bool × ℕ) (L : List (Bool × ℕ)) (t : ℝ) :
    wholeWord μ hμ (a::L) t=
      sameResolvent (line μ t) (by simpa only [line_im] using ne_of_gt hμ)*
        reader (mixedLetter a)*wholeWord μ hμ L t := by
  change lift sourceFilter (wordFamily μ hμ (a::L) t)=_
  have he := lift_congr sourceFilter (wordFamily μ hμ (a::L) t) (comp
      (comp (resolventFamily (line μ t) (by simpa only [line_im] using ne_of_gt hμ))
        (SourceFamilyOperator.constant (mixedLetter a))) (wordFamily μ hμ L t)) (fun _ => rfl)
  have ho := lift_comp sourceFilter
    (comp (resolventFamily (line μ t) (by simpa only [line_im] using ne_of_gt hμ))
      (SourceFamilyOperator.constant (mixedLetter a))) (wordFamily μ hμ L t)
  have hi := lift_comp sourceFilter
    (resolventFamily (line μ t) (by simpa only [line_im] using ne_of_gt hμ))
    (SourceFamilyOperator.constant (mixedLetter a))
  have hh := congrArg (fun T : HistorySpace →L[ℂ] HistorySpace =>
    T.comp (lift sourceFilter (wordFamily μ hμ L t))) hi
  exact he.trans (ho.trans hh)

theorem original_mixed_band_limit (μ : ℝ) (hμ : 0<μ) (L : List (Bool × ℕ))
    (g : H) (a b : ℝ) :
    Tendsto (fun F => ∫ t in a..b, ‖mixedWord F μ t L g‖^2) sourceFilter
      (𝓝 (∫ t in a..b, ‖wholeWord μ hμ L t (inclusion g)‖^2)) := by
  refine band_integral_limit (sourceFilter : Filter Index) _ _
    ⟨2*size μ (L.map mixedLetter)*variation μ (L.map mixedLetter)*‖g‖^2, by
      have := size_nonneg μ hμ (L.map mixedLetter)
      have := variation_nonneg μ hμ (L.map mixedLetter)
      positivity⟩ ?_ ?_ a b
  · intro F
    exact word_square_lipschitz _ (GaussGradedCompression.compression_selfAdjoint F) μ hμ _ g
  · intro t
    have ht := square_tendsto sourceFilter
      (act sourceFilter (wordFamily μ hμ L t) (SourceFamilyHilbert.constant sourceFilter g))
    change Tendsto (fun F => ‖mixedWord F μ t L g‖^2) sourceFilter _ at ht
    change Tendsto (fun F => ‖mixedWord F μ t L g‖^2) sourceFilter
      (𝓝 (‖lift sourceFilter (wordFamily μ hμ L t)
        ((SourceFamilyHilbert.constant sourceFilter g) : HistorySpace)‖^2))
    rw [lift_coe,UniformSpace.Completion.norm_coe]
    exact ht

#print axioms resolvent_difference
#print axioms word_difference
#print axioms whole_word_cons
#print axioms original_mixed_band_limit
end LowEnergy.SourceResolventBandLimit
