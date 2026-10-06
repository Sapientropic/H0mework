import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceCutoffNormConvergence
import Mathlib.MeasureTheory.Function.L2Space

/-! The source cutoff estimate is an L²-time obligation; it does not need pointwise graph bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.FullYSourceCutoffTimeGraph
open MeasureTheory Filter
open scoped Topology InnerProductSpace
open FullYSourceCutoffVolterra FullYSourceCutoffNorm
open GaussUnitaryHistory (HistorySpace reader)

section L2
variable {α E : Type*} [MeasurableSpace α] (μ : Measure α)
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem square_integrable (f : Lp E 2 μ) : Integrable (fun t => ‖f t‖^2) μ := by
  have h := (L2.integrable_inner (𝕜 := ℂ) f f).re
  simpa only [inner_self_eq_norm_sq] using h

theorem square_integral (f : Lp E 2 μ) : ‖f‖^2=∫ t, ‖f t‖^2 ∂μ := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  simp only [inner_self_eq_norm_sq]

theorem l2_distance (u : ℕ → Lp E 2 μ)
    (h : ∀ m n, m ≤ n → ∀ᵐ t ∂μ, ‖u n t-u m t‖^2 ≤ ‖u n t‖^2-‖u m t‖^2)
    {m n : ℕ} (hmn : m ≤ n) :
    ‖u n-u m‖^2 ≤ ‖u n‖^2-‖u m‖^2 := by
  rw [square_integral, square_integral, square_integral,
    ← integral_sub (square_integrable μ (u n)) (square_integrable μ (u m))]
  apply integral_mono_ae (square_integrable μ (u n-u m))
    ((square_integrable μ (u n)).sub (square_integrable μ (u m)))
  filter_upwards [Lp.coeFn_sub (u n) (u m), h m n hmn] with t ht hb
  simpa only [ht, Pi.sub_apply] using hb

theorem mapped_l2_distance (A : ℕ → E →L[ℂ] E)
    (hA : ∀ x m n, m ≤ n → ‖A n x-A m x‖^2 ≤ ‖A n x‖^2-‖A m x‖^2)
    (ψ : Lp E 2 μ) {m n : ℕ} (hmn : m ≤ n) :
    ‖(A n).compLpL 2 μ ψ-(A m).compLpL 2 μ ψ‖^2 ≤
      ‖(A n).compLpL 2 μ ψ‖^2-‖(A m).compLpL 2 μ ψ‖^2 := by
  apply l2_distance μ (fun n => (A n).compLpL 2 μ ψ) ?_ hmn
  intro j k hjk
  filter_upwards [(A k).coeFn_compLpL ψ, (A j).coeFn_compLpL ψ] with t hk hj
  rw [hk,hj]
  exact hA (ψ t) j k hjk

theorem mapped_l2_residual (S B : E →L[ℂ] E) (A : ℕ → E →L[ℂ] E)
    (hA : ∀ n x, S (A n x)=B x-(A (n+1) x-A n x)) (ψ : Lp E 2 μ) (n : ℕ) :
    S.compLpL 2 μ ((A n).compLpL 2 μ ψ)=B.compLpL 2 μ ψ-
      ((A (n+1)).compLpL 2 μ ψ-(A n).compLpL 2 μ ψ) := by
  apply Lp.ext
  filter_upwards [S.coeFn_compLpL ((A n).compLpL 2 μ ψ), B.coeFn_compLpL ψ,
    (A n).coeFn_compLpL ψ, (A (n+1)).coeFn_compLpL ψ,
    Lp.coeFn_sub ((A (n+1)).compLpL 2 μ ψ) ((A n).compLpL 2 μ ψ),
    Lp.coeFn_sub (B.compLpL 2 μ ψ)
      ((A (n+1)).compLpL 2 μ ψ-(A n).compLpL 2 μ ψ)] with t hS hB hn hn1 hdiff hout
  simp only [hS,hB,hn,hn1,hdiff,hout,Pi.sub_apply]
  exact hA n (ψ t)

theorem telescoping_limit (S : E →L[ℂ] E) (u : ℕ → E) (b y : E)
    (he : ∀ n, S (u n)=b-(u (n+1)-u n))
    (h : Tendsto u atTop (𝓝 y)) : S y=b := by
  have hs := S.continuous.tendsto y |>.comp h
  have hnext := h.comp (tendsto_add_atTop_nat 1)
  have hr := (tendsto_const_nhds (x := b)).sub (hnext.sub h)
  simp only [sub_self,sub_zero] at hr
  exact tendsto_nhds_unique hs (by simpa only [Function.comp_def,he] using hr)

theorem mapped_graph_ae (S B : E →L[ℂ] E) (ψ y : Lp E 2 μ)
    (h : S.compLpL 2 μ y=B.compLpL 2 μ ψ) :
    ∀ᵐ t ∂μ, S (y t)=B (ψ t) := by
  filter_upwards [S.coeFn_compLpL y,B.coeFn_compLpL ψ] with t hS hB
  rw [←hS,←hB,h]

end L2

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def timeCutoff (n : ℕ) : Lp HistorySpace 2 μ →L[ℂ] Lp HistorySpace 2 μ :=
  (reader (cutoff n)).compLpL 2 μ

theorem time_cutoff_distance (ψ : Lp HistorySpace 2 μ) {m n : ℕ} (hmn : m ≤ n) :
    ‖timeCutoff μ n ψ-timeCutoff μ m ψ‖^2 ≤
      ‖timeCutoff μ n ψ‖^2-‖timeCutoff μ m ψ‖^2 :=
  mapped_l2_distance μ (fun n => reader (cutoff n))
    (fun x _ _ h => source_cutoff_distance x h) ψ hmn

theorem time_strong_limit (ψ : Lp HistorySpace 2 μ)
    (bounded : ∃ C : ℝ, ∀ n, ‖timeCutoff μ n ψ‖ ≤ C) :
    ∃ y : Lp HistorySpace 2 μ,
      Tendsto (fun n => timeCutoff μ n ψ) atTop (𝓝 y) :=
  squared_distance_strong_limit (fun n => timeCutoff μ n ψ)
    (fun _ _ h => time_cutoff_distance μ ψ h) bounded

theorem time_graph_limit (ψ y : Lp HistorySpace 2 μ)
    (h : Tendsto (fun n => timeCutoff μ n ψ) atTop (𝓝 y)) :
    (reader GaussRadialDomain.inverseRadius).compLpL 2 μ y=
      (reader GaussYukawaOperator.bounded).compLpL 2 μ ψ := by
  apply telescoping_limit (reader GaussRadialDomain.inverseRadius |>.compLpL 2 μ)
    (fun n => timeCutoff μ n ψ) _ y ?_ h
  intro n
  apply mapped_l2_residual μ (reader GaussRadialDomain.inverseRadius)
    (reader GaussYukawaOperator.bounded) (fun n => reader (cutoff n)) ?_ ψ n
  intro j x
  have hg := congrArg GaussYukawaInteraction.representation (cutoff_graph_residual j)
  simp only [map_mul,map_sub] at hg
  exact congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) hg

theorem time_graph_of_bounded (ψ : Lp HistorySpace 2 μ)
    (bounded : ∃ C : ℝ, ∀ n, ‖timeCutoff μ n ψ‖ ≤ C) :
    ∃ y : Lp HistorySpace 2 μ,
      Tendsto (fun n => timeCutoff μ n ψ) atTop (𝓝 y) ∧
      ∀ᵐ t ∂μ, reader GaussRadialDomain.inverseRadius (y t)=
        reader GaussYukawaOperator.bounded (ψ t) :=
  (time_strong_limit μ ψ bounded).imp (fun y hy =>
    ⟨hy,mapped_graph_ae μ (reader GaussRadialDomain.inverseRadius)
      (reader GaussYukawaOperator.bounded) ψ y (time_graph_limit μ ψ y hy)⟩)

#print axioms time_strong_limit
#print axioms time_graph_of_bounded
end LowEnergy.FullYSourceCutoffTimeGraph
