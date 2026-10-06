import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCutoffVolterra
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Order.MonotoneConvergence

/-! Positive source geometric cutoffs turn a uniform norm bound into a strong graph limit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.FullYSourceCutoffNorm
open scoped Topology InnerProductSpace BigOperators
open Filter

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem power_pair (Q : E →L[ℂ] E)
    (hQ : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y)) (n : ℕ) (x y : E) :
    inner ℂ ((Q^n) x) y = inner ℂ x ((Q^n) y) := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
    calc
      _ = inner ℂ (Q x) ((Q^n) y) := by rw [pow_succ, mul_apply_eq_comp, ih]
      _ = inner ℂ x (Q ((Q^n) y)) := hQ _ _
      _ = _ := by rw [pow_succ', mul_apply_eq_comp]

theorem power_nonnegative (Q : E →L[ℂ] E)
    (hQ : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (Q x)).re) (n : ℕ) (x : E) :
    0 ≤ (inner ℂ x ((Q^n) x)).re := by
  induction n using Nat.twoStepInduction generalizing x with
  | zero => simpa using inner_self_nonneg (𝕜 := ℂ) (x := x)
  | one => simpa using hp x
  | more n ih _ =>
    have he : inner ℂ x ((Q^(n+2)) x) = inner ℂ (Q x) ((Q^n) (Q x)) := by
      have heq : Q^(n+2)=Q*(Q^n*Q) := by
        calc
          _ = Q^(n+1)*Q := pow_succ _ _
          _ = _ := by rw [pow_succ']; exact mul_assoc _ _ _
      rw [heq, mul_apply_eq_comp, mul_apply_eq_comp, ← hQ]
    rw [he]
    exact ih (Q x)

def partialSum (Q : E →L[ℂ] E) (v : E) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, (Q^j) v

theorem power_cross_nonnegative (Q : E →L[ℂ] E)
    (hQ : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (Q x)).re) (i j : ℕ) (v : E) :
    0 ≤ (inner ℂ ((Q^i) v) ((Q^j) v)).re := by
  rw [power_pair Q hQ, ← mul_apply_eq_comp, ← pow_add]
  exact power_nonnegative Q hQ hp (i+j) v

theorem partial_distance (Q : E →L[ℂ] E)
    (hQ : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (Q x)).re) (v : E) {m n : ℕ} (hmn : m ≤ n) :
    ‖partialSum Q v n-partialSum Q v m‖^2 ≤ ‖partialSum Q v n‖^2-‖partialSum Q v m‖^2 := by
  have hsplit : partialSum Q v n = partialSum Q v m + ∑ j ∈ Finset.Ico m n, (Q^j) v := by
    exact (Finset.sum_range_add_sum_Ico (fun j => (Q^j) v) hmn).symm
  have hc : 0 ≤ (inner ℂ (partialSum Q v m) (∑ j ∈ Finset.Ico m n, (Q^j) v)).re := by
    simp only [partialSum, sum_inner, inner_sum, Complex.re_sum]
    exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ =>
      power_cross_nonnegative Q hQ hp i j v))
  rw [hsplit, add_sub_cancel_left, @norm_add_sq ℂ]
  change 0 ≤ RCLike.re (inner ℂ (partialSum Q v m)
    (∑ j ∈ Finset.Ico m n, (Q^j) v)) at hc
  linarith

variable [CompleteSpace E]

omit [InnerProductSpace ℂ E] in
theorem squared_distance_strong_limit (u : ℕ → E)
    (distance : ∀ m n, m ≤ n → ‖u n-u m‖^2 ≤ ‖u n‖^2-‖u m‖^2)
    (bounded : ∃ C : ℝ, ∀ n, ‖u n‖ ≤ C) :
    ∃ y : E, Tendsto u atTop (𝓝 y) := by
  have hm : Monotone (fun n => ‖u n‖^2) := by
    intro m n hmn
    have hd := distance m n hmn
    nlinarith [sq_nonneg ‖u n-u m‖]
  have hb : BddAbove (Set.range (fun n => ‖u n‖^2)) := by
    obtain ⟨C,hC⟩ := bounded
    refine ⟨C^2, ?_⟩
    rintro _ ⟨n,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hC n) 2
  have he : CauchySeq (fun n => ‖u n‖^2) :=
    (tendsto_atTop_ciSup hm hb).cauchySeq
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp he (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hd := distance N n hn
  have hs := hN n hn
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hn))] at hs
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (u n-u N)]


theorem partial_strong_limit (Q : E →L[ℂ] E)
    (hQ : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hp : ∀ x, 0 ≤ (inner ℂ x (Q x)).re) (v : E)
    (bounded : ∃ C : ℝ, ∀ n, ‖partialSum Q v n‖ ≤ C) :
    ∃ y : E, Tendsto (partialSum Q v) atTop (𝓝 y) :=
  squared_distance_strong_limit (partialSum Q v)
    (fun _ _ h => partial_distance Q hQ hp v h) bounded

end Hilbert

open GaussCoreHilbert
open GaussUnitaryHistory (HistorySpace reader sourceFilter)
open SourceFamilyHilbert SourceFamilyOperator
open FullYSourceCutoffVolterra

def sourceComplement : HistorySpace →L[ℂ] HistorySpace :=
  1-reader GaussRadialDomain.inverseRadius

theorem source_inverse_contraction (x : HistorySpace) :
    ‖reader GaussRadialDomain.inverseRadius x‖ ≤ ‖x‖ := by
  have hH (y : H) : ‖GaussRadialDomain.inverseRadius y‖ ≤ ‖y‖ := by
    have hn : ‖GaussRadialDomain.inverseRadius‖ ≤ 1 :=
      GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
    exact ((GaussRadialDomain.inverseRadius).le_opNorm y).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg y)).trans_eq (one_mul _))
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  change ‖lift sourceFilter (SourceFamilyOperator.constant GaussRadialDomain.inverseRadius)
    (f : HistorySpace)‖ ≤ ‖(f : HistorySpace)‖
  rw [lift_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact le_of_tendsto_of_tendsto (norm_tendsto sourceFilter _)
    (norm_tendsto sourceFilter f) (Filter.Eventually.of_forall (fun F => hH (value f F)))

theorem source_complement_pair (x y : HistorySpace) :
    inner ℂ (sourceComplement x) y = inner ℂ x (sourceComplement y) := by
  have hS : inner ℂ (reader GaussRadialDomain.inverseRadius x) y =
      inner ℂ x (reader GaussRadialDomain.inverseRadius y) :=
    lift_pair sourceFilter _ _ (fun _ => GaussRadialDomain.inverse_pair) x y
  change inner ℂ (x-reader GaussRadialDomain.inverseRadius x) y =
    inner ℂ x (y-reader GaussRadialDomain.inverseRadius y)
  rw [inner_sub_left, inner_sub_right, hS]

theorem source_complement_positive (x : HistorySpace) :
    0 ≤ (inner ℂ x (sourceComplement x)).re := by
  have hb := (re_inner_le_norm (𝕜 := ℂ) x (reader GaussRadialDomain.inverseRadius x)).trans
    (mul_le_mul_of_nonneg_left (source_inverse_contraction x) (norm_nonneg x))
  change 0 ≤ RCLike.re (inner ℂ x (x-reader GaussRadialDomain.inverseRadius x))
  rw [inner_sub_right, map_sub, inner_self_eq_norm_sq]
  nlinarith

theorem partial_recurrence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q : E →L[ℂ] E) (v : E) (n : ℕ) :
    partialSum Q v (n+1)=v+Q (partialSum Q v n) := by
  simp only [partialSum, Finset.sum_range_succ', pow_zero, map_sum,
    pow_succ', mul_apply_eq_comp]
  exact add_comm _ _

private theorem read_recurrence {R E : Type*} [Ring R]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ρ : R →+* (E →L[ℂ] E)) (B Q A : R) (x : E) :
    ρ (B+Q*A) x=ρ B x+ρ Q (ρ A x) := by
  rw [map_add, map_mul, add_apply, mul_apply_eq_comp]

private theorem mapped_geometric {R E : Type*} [Ring R]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ρ : R →+* (E →L[ℂ] E)) (B Q : R) (u : ℕ → R)
    (h0 : u 0=B) (hs : ∀ n, u (n+1)=B+Q*u n) (n : ℕ) (x : E) :
    ρ (u n) x=partialSum (ρ Q) (ρ B x) (n+1) := by
  induction n with
  | zero => simp [h0, partialSum]
  | succ n ih =>
    rw [hs, read_recurrence, ih]
    exact (partial_recurrence (ρ Q) (ρ B x) (n+1)).symm

theorem source_cutoff_partial (n : ℕ) (x : HistorySpace) :
    reader (cutoff n) x=partialSum sourceComplement (reader GaussYukawaOperator.bounded x) (n+1) := by
  have hQ : GaussYukawaInteraction.representation (1-GaussRadialDomain.inverseRadius) =
      sourceComplement := by simp only [map_sub, map_one]; rfl
  have hg := mapped_geometric GaussYukawaInteraction.representation.toRingHom
    GaussYukawaOperator.bounded (1-GaussRadialDomain.inverseRadius) cutoff rfl (fun _ => rfl) n x
  exact hg.trans (congrArg (fun Q : HistorySpace →L[ℂ] HistorySpace =>
    partialSum Q (reader GaussYukawaOperator.bounded x) (n+1)) hQ)

theorem source_cutoff_distance (x : HistorySpace) {m n : ℕ} (hmn : m ≤ n) :
    ‖reader (cutoff n) x-reader (cutoff m) x‖^2 ≤
      ‖reader (cutoff n) x‖^2-‖reader (cutoff m) x‖^2 := by
  simp only [source_cutoff_partial]
  exact partial_distance sourceComplement source_complement_pair source_complement_positive
    _ (Nat.add_le_add_right hmn 1)

theorem source_graph_of_bounded (x : HistorySpace)
    (bounded : ∃ C : ℝ, ∀ n, ‖reader (cutoff n) x‖ ≤ C) :
    ∃ y : HistorySpace,
      Tendsto (fun n => reader (cutoff n) x) atTop (𝓝 y) ∧
      reader GaussYukawaOperator.bounded x=reader GaussRadialDomain.inverseRadius y := by
  have hb : ∃ C : ℝ, ∀ n,
      ‖partialSum sourceComplement (reader GaussYukawaOperator.bounded x) n‖ ≤ C := by
    obtain ⟨C,hC⟩ := bounded
    refine ⟨max C 0, ?_⟩
    intro n
    cases n with
    | zero => simp only [partialSum, Finset.range_zero, Finset.sum_empty, norm_zero]; exact le_max_right C 0
    | succ n => rw [← source_cutoff_partial]; exact (hC n).trans (le_max_left C 0)
  obtain ⟨y,hy⟩ := partial_strong_limit sourceComplement source_complement_pair
    source_complement_positive (reader GaussYukawaOperator.bounded x) hb
  have hc : Tendsto (fun n => reader (cutoff n) x) atTop (𝓝 y) := by
    simpa only [source_cutoff_partial, Function.comp_def] using
      hy.comp (tendsto_add_atTop_nat 1)
  exact ⟨y,hc,source_cutoff_graph_limit x y hc⟩

#print axioms partial_strong_limit
#print axioms source_cutoff_distance
#print axioms source_graph_of_bounded
end LowEnergy.FullYSourceCutoffNorm
