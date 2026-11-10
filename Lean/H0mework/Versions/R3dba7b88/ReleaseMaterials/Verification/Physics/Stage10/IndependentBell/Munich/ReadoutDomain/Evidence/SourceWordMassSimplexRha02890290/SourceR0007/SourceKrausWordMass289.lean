import H0mework.Versions.R5a407445.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceHiddenWordFlowRha0286.SourceR0009.SourceHiddenWordFlow286
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

/-! The complete Kraus inventory generates all finite-word mass.

The Volterra operator below inserts the actual first jump and integrates its
actual continuous time. Its nth iterate is the sum over every n-letter word,
with the original intervening survival operators. The vacuum term and the
uncompleted prefix term come from the same source; neither a normalizer nor
a completed measure is an input.

All Kraus letters are included in this normalization identity. In the physical
consumer, capture/ion records may be traced, while natural-emission labels and
their complex amplitudes remain the joint field. This diagonal norm identity
does not turn coherent natural-emission alternatives into classical branches.
The separate flat-simplex/Fock identification consumes these iterated integrals.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace SourceKrausWordMass289

open SourceKrausSurvival285 SourceHiddenWordFlow286

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {ι : Type v} [Fintype ι]

private def quadratic (x : E) : Operator (E := E) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E x)

omit [CompleteSpace E] in
private theorem quadratic_apply (x : E) (A : Operator (E := E)) :
    quadratic x A = inner ℂ x (A x) := rfl

private theorem quadratic_adjoint (A X : Operator (E := E)) (x : E) :
    quadratic x (A.adjoint * X * A) = quadratic (A x) X := by
  change inner ℂ x (A.adjoint (X (A x))) = inner ℂ (A x) (X (A x))
  exact ContinuousLinearMap.adjoint_inner_right A x (X (A x))

omit [CompleteSpace E] in
private theorem quadratic_one (x : E) :
    quadratic x (1 : Operator (E := E)) = (‖x‖ ^ 2 : ℝ) := by
  change inner ℂ x x = (‖x‖ ^ 2 : ℝ)
  apply Complex.ext
  · change (inner ℂ x x).re = ‖x‖ ^ 2
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  · change (inner ℂ x x).im = 0
    exact inner_self_im (𝕜 := ℂ) x

omit [CompleteSpace E] in
private theorem ext_quadratic (A B : Operator (E := E))
    (same : ∀ x, quadratic x A = quadratic x B) : A = B := by
  have written : A.toLinearMap = B.toLinearMap :=
    (ext_inner_map A.toLinearMap B.toLinearMap).mp (fun x => by
      simpa only [quadratic_apply, ContinuousLinearMap.coe_coe, inner_conj_symm] using
        congrArg (starRingEnd ℂ) (same x))
  ext x
  exact congrArg (fun T : E →ₗ[ℂ] E => T x) written

variable [Nontrivial E] (source : RawKrausWindow E ι)

def firstBranch (s r : ℝ) (j : ι) : Operator (E := E) :=
  source.chartJump j r * source.chartPropagator s r

theorem firstBranch_continuous (j : ι) :
    Continuous (fun pair : ℝ × ℝ => firstBranch source pair.1 pair.2 j) :=
  ((source.chartJump_continuous j).comp continuous_snd).mul source.chartPropagator_continuous

private theorem chartPropagator_original (s r : ℝ)
    (hs : s ∈ Icc source.left source.right) (hr : r ∈ Icc source.left source.right) :
    source.chartPropagator s r = source.propagate s r := by
  simp only [RawKrausWindow.chartPropagator, RawKrausWindow.timeProjection,
    projIcc_of_mem source.ordered hs, projIcc_of_mem source.ordered hr]

private theorem firstBranch_original (s r : ℝ)
    (hs : s ∈ Icc source.left source.right) (hr : r ∈ Icc source.left source.right)
    (j : ι) : firstBranch source s r j = source.jumps r j * source.propagate s r := by
  rw [firstBranch, chartPropagator_original source s r hs hr]
  simp only [RawKrausWindow.chartJump, RawKrausWindow.timeProjection,
    projIcc_of_mem source.ordered hr]

theorem propagate_opNorm_le_one (s r : ℝ) (hs : source.left ≤ s)
    (hsr : s ≤ r) (hr : r ≤ source.right) : ‖source.propagate s r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using source.propagate_contracts s r hs hsr hr x

theorem firstBranch_norm (s r : ℝ) (hs : s ∈ Icc source.left source.right)
    (hr : r ∈ Icc s source.right) (j : ι) :
    ‖firstBranch source s r j‖ ≤ source.jump_bounds j := by
  rw [firstBranch_original source s r hs ⟨hs.1.trans hr.1,hr.2⟩]
  exact (norm_mul_le _ _).trans <| by
    simpa only [mul_one] using mul_le_mul
      (source.jumps_norm r ⟨hs.1.trans hr.1,hr.2⟩ j)
      (propagate_opNorm_le_one source s r hs.1 hr.1 hr.2)
      (norm_nonneg _) (source.jump_bounds j).coe_nonneg

def insertion (f : ℝ → Operator (E := E)) (s r : ℝ) : Operator (E := E) :=
  ∑ j, (firstBranch source s r j).adjoint * f r * firstBranch source s r j

theorem insertion_continuous (f : ℝ → Operator (E := E)) (hf : Continuous f) :
    Continuous (fun pair : ℝ × ℝ => insertion source f pair.1 pair.2) :=
  continuous_finsetSum Finset.univ fun j _ =>
    (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
      (firstBranch_continuous source j)).mul (hf.comp continuous_snd)).mul
        (firstBranch_continuous source j)

def advance (f : ℝ → Operator (E := E)) (s : ℝ) : Operator (E := E) :=
  ∫ r in s..source.right, insertion source f s r

theorem advance_continuous (f : ℝ → Operator (E := E)) (hf : Continuous f) :
    Continuous (advance source f) := by
  have written : Continuous (fun s : ℝ =>
      ∫ r in source.right..s, insertion source f s r) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun s r : ℝ => insertion source f s r) (a₀ := source.right)
      (insertion_continuous source f hf) continuous_id
  have same : advance source f = (fun s : ℝ =>
      -(∫ r in source.right..s, insertion source f s r)) := by
    funext s
    exact intervalIntegral.integral_symm _ _
  rw [same]
  exact written.neg

private theorem insertion_integrable (f : ℝ → Operator (E := E))
    (hf : Continuous f) (s : ℝ) :
    IntervalIntegrable (insertion source f s) volume s source.right :=
  ((insertion_continuous source f hf).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem advance_sub (f g : ℝ → Operator (E := E))
    (hf : Continuous f) (hg : Continuous g) (s : ℝ) :
    advance source (fun r => f r - g r) s = advance source f s - advance source g s := by
  simp only [advance, insertion, mul_sub, sub_mul, Finset.sum_sub_distrib]
  exact intervalIntegral.integral_sub (insertion_integrable source f hf s)
    (insertion_integrable source g hg s)

theorem advance_congr (f g : ℝ → Operator (E := E))
    (same : EqOn f g (Icc source.left source.right)) (s : ℝ)
    (hs : s ∈ Icc source.left source.right) : advance source f s = advance source g s := by
  apply intervalIntegral.integral_congr
  intro r hr
  have inside : r ∈ Icc source.left source.right := by
    rw [uIcc_of_le hs.2] at hr
    exact ⟨hs.1.trans hr.1,hr.2⟩
  simp only [insertion, same inside]

theorem quadratic_advance (f : ℝ → Operator (E := E)) (hf : Continuous f)
    (s : ℝ) (x : E) :
    quadratic x (advance source f s) =
      ∫ r in s..source.right, ∑ j, quadratic (firstBranch source s r j x) (f r) := by
  rw [advance, ← (quadratic x).intervalIntegral_comp_comm (insertion_integrable source f hf s)]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [insertion, map_sum, quadratic_adjoint]

def vacuum (s : ℝ) : Operator (E := E) :=
  (source.chartPropagator s source.right).adjoint * source.chartPropagator s source.right

theorem vacuum_continuous : Continuous (vacuum source) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (source.chartPropagator_continuous.comp (continuous_id.prodMk continuous_const))).mul
      (source.chartPropagator_continuous.comp (continuous_id.prodMk continuous_const))

theorem quadratic_vacuum (s : ℝ) (x : E) :
    quadratic x (vacuum source s) = (‖source.chartPropagator s source.right x‖ ^ 2 : ℝ) := by
  simpa only [vacuum, mul_one] using (quadratic_adjoint
    (source.chartPropagator s source.right) 1 x).trans (quadratic_one _)

theorem vacuum_norm (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    ‖vacuum source s‖ ≤ 1 := by
  rw [vacuum, chartPropagator_original source s source.right hs
    (right_mem_Icc.mpr source.ordered)]
  have bound := propagate_opNorm_le_one source s source.right hs.1 hs.2 le_rfl
  calc
    _ ≤ ‖(source.propagate s source.right).adjoint‖ * ‖source.propagate s source.right‖ := norm_mul_le _ _
    _ = ‖source.propagate s source.right‖ * ‖source.propagate s source.right‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 := by nlinarith [norm_nonneg (source.propagate s source.right)]

/-- Complete first-jump energy becomes an operator identity for every input. -/
theorem vacuum_plus_advance_one (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    vacuum source s + advance source (fun _ => 1) s = 1 := by
  apply ext_quadratic
  intro x
  rw [map_add, quadratic_vacuum, quadratic_advance source _ continuous_const,
    quadratic_one, chartPropagator_original source s source.right hs
      (right_mem_Icc.mpr source.ordered)]
  have times : (∫ r in s..source.right, ∑ j,
      quadratic (firstBranch source s r j x) (1 : Operator (E := E))) =
      ((∫ r in s..source.right, ∑ j,
        ‖source.jumps r j (source.propagate s r x)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.2] at hr
    simp only [quadratic_one, firstBranch_original source s r hs
      ⟨hs.1.trans hr.1,hr.2⟩, mul_apply_eq_comp, Complex.ofReal_sum]
  rw [times, ← Complex.ofReal_add]
  exact congrArg Complex.ofReal (source.survival_plus_first_jump s source.right hs.1 hs.2 le_rfl x)

def iterate (seed : ℝ → Operator (E := E)) : ℕ → ℝ → Operator (E := E)
  | 0 => seed
  | n+1 => advance source (iterate seed n)

theorem iterate_continuous (seed : ℝ → Operator (E := E)) (continuous : Continuous seed)
    (n : ℕ) : Continuous (iterate source seed n) := by
  induction n with
  | zero => exact continuous
  | succ n ih => exact advance_continuous source _ ih

private theorem insertion_norm (f : ℝ → Operator (E := E)) (s r : ℝ)
    (hs : s ∈ Icc source.left source.right) (hr : r ∈ Icc s source.right) :
    ‖insertion source f s r‖ ≤ (source.activityBound : ℝ) * ‖f r‖ := by
  calc
    _ ≤ ∑ j, ‖(firstBranch source s r j).adjoint * f r * firstBranch source s r j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, (source.jump_bounds j : ℝ) ^ 2 * ‖f r‖ := by
      apply Finset.sum_le_sum
      intro j _
      have bound := firstBranch_norm source s r hs hr j
      calc
        _ ≤ (‖(firstBranch source s r j).adjoint‖ * ‖f r‖) * ‖firstBranch source s r j‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖firstBranch source s r j‖ * ‖f r‖ * ‖firstBranch source s r j‖ := by
          rw [LinearIsometryEquiv.norm_map]
        _ ≤ (source.jump_bounds j : ℝ) * ‖f r‖ * (source.jump_bounds j : ℝ) := by
          gcongr
        _ = _ := by ring
    _ = _ := by simp only [← Finset.sum_mul, RawKrausWindow.activityBound,
      NNReal.coe_sum, NNReal.coe_pow]

private theorem polynomial_integral (n : ℕ) (a b : ℝ) :
    (∫ r in a..b, (b-r)^n) = (b-a)^(n+1)/(n+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^n) b]
  rw [integral_pow]
  simp

/-- Every uncompleted word prefix has the source factorial tail price. -/
theorem iterate_norm (seed : ℝ → Operator (E := E))
    (bound : ∀ s ∈ Icc source.left source.right, ‖seed s‖ ≤ 1) (n : ℕ)
    (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    ‖iterate source seed n s‖ ≤
      (source.activityBound : ℝ)^n * (source.right-s)^n / n.factorial := by
  induction n generalizing s with
  | zero => simpa only [iterate, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one] using bound s hs
  | succ n ih =>
      have majorant_cont : Continuous (fun r : ℝ =>
          (source.activityBound : ℝ) * ((source.activityBound : ℝ)^n * (source.right-r)^n / n.factorial)) := by
        fun_prop
      change ‖∫ r in s..source.right, insertion source (iterate source seed n) s r‖ ≤ _
      calc
        _ ≤ ∫ r in s..source.right,
            (source.activityBound : ℝ) * ((source.activityBound : ℝ)^n * (source.right-r)^n / n.factorial) := by
          apply intervalIntegral.norm_integral_le_of_norm_le hs.2
            (Filter.Eventually.of_forall fun r hr => ?_) (majorant_cont.intervalIntegrable _ _)
          exact (insertion_norm source _ s r hs ⟨hr.1.le,hr.2⟩).trans
            (mul_le_mul_of_nonneg_left (ih r ⟨hs.1.trans hr.1.le,hr.2⟩) source.activityBound.coe_nonneg)
        _ = _ := by
          have integrand : (fun r : ℝ => (source.activityBound : ℝ) *
              ((source.activityBound : ℝ)^n * (source.right-r)^n / n.factorial)) =
              fun r => ((source.activityBound : ℝ) * (source.activityBound : ℝ)^n / n.factorial) *
                (source.right-r)^n := by
            funext r
            ring
          rw [integrand, intervalIntegral.integral_const_mul, polynomial_integral]
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            pow_succ, div_eq_mul_inv, mul_inv_rev]
          ring

def prefixTail (n : ℕ) (s : ℝ) : Operator (E := E) := iterate source (fun _ => 1) n s

def wordGram (n : ℕ) (s : ℝ) : Operator (E := E) := iterate source (vacuum source) n s

theorem prefixTail_continuous (n : ℕ) : Continuous (prefixTail source n) :=
  iterate_continuous source _ continuous_const n

theorem wordGram_continuous (n : ℕ) : Continuous (wordGram source n) :=
  iterate_continuous source _ (vacuum_continuous source) n

theorem wordGram_eq_tail_sub (n : ℕ) (s : ℝ)
    (hs : s ∈ Icc source.left source.right) :
    wordGram source n s = prefixTail source n s - prefixTail source (n+1) s := by
  induction n generalizing s with
  | zero =>
      change vacuum source s = 1 - advance source (fun _ => 1) s
      exact eq_sub_iff_add_eq.mpr (vacuum_plus_advance_one source s hs)
  | succ n ih =>
      change advance source (wordGram source n) s =
        advance source (prefixTail source n) s - advance source (prefixTail source (n+1)) s
      rw [← advance_sub source _ _ (prefixTail_continuous source n)
        (prefixTail_continuous source (n+1))]
      exact advance_congr source _ _ (fun r hr => ih r hr) s hs

theorem finite_word_balance (n : ℕ) (s : ℝ)
    (hs : s ∈ Icc source.left source.right) :
    (∑ k ∈ Finset.range n, wordGram source k s) + prefixTail source n s = 1 := by
  induction n with
  | zero => simp [prefixTail, iterate]
  | succ n ih =>
      rw [Finset.sum_range_succ, wordGram_eq_tail_sub source n s hs]
      rw [add_assoc, sub_add_cancel]
      exact ih

theorem prefixTail_norm (n : ℕ) (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    ‖prefixTail source n s‖ ≤ (source.activityBound : ℝ)^n * (source.right-s)^n / n.factorial :=
  iterate_norm source _ (fun _ _ => by simp) n s hs

theorem wordGram_norm (n : ℕ) (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    ‖wordGram source n s‖ ≤ (source.activityBound : ℝ)^n * (source.right-s)^n / n.factorial :=
  iterate_norm source _ (vacuum_norm source) n s hs

theorem prefixTail_tendsto_zero (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    Tendsto (fun n => prefixTail source n s) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa only [mul_pow] using prefixTail_norm source n s hs
  · simpa only [mul_pow] using FloorSemiring.tendsto_pow_div_factorial_atTop
      ((source.activityBound : ℝ) * (source.right-s))

theorem wordGram_norm_summable (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    Summable (fun n => ‖wordGram source n s‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => by simpa only [mul_pow] using wordGram_norm source n s hs)
    (Real.summable_pow_div_factorial ((source.activityBound : ℝ)*(source.right-s)))

/-- The full source word expansion has identity Gram, without normalization input. -/
theorem wordGram_hasSum_identity (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    HasSum (fun n => wordGram source n s) 1 := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm (wordGram_norm_summable source s hs)).mpr
  have limit : Tendsto (fun n => (1 : Operator (E := E)) - prefixTail source n s)
      atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub (prefixTail_tendsto_zero source s hs))
  apply limit.congr'
  exact Filter.Eventually.of_forall fun n =>
    (eq_sub_iff_add_eq.mpr (finite_word_balance source n s hs)).symm

def wordMass (n : ℕ) (s : ℝ) (x : E) : ℝ := (quadratic x (wordGram source n s)).re

theorem wordMass_zero (s : ℝ) (x : E) :
    wordMass source 0 s x = ‖source.chartPropagator s source.right x‖^2 := by
  simp only [wordMass, wordGram, iterate, quadratic_vacuum, Complex.ofReal_re]

/-- This is the actual nested all-letter integral, retaining the same branch amplitudes. -/
theorem wordMass_succ (n : ℕ) (s : ℝ) (x : E) :
    wordMass source (n+1) s x = ∫ r in s..source.right,
      ∑ j, wordMass source n r (firstBranch source s r j x) := by
  let functional : Operator (E := E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((quadratic x).restrictScalars ℝ)
  change functional (advance source (wordGram source n) s) = _
  rw [advance, ← functional.intervalIntegral_comp_comm
    (insertion_integrable source (wordGram source n) (wordGram_continuous source n) s)]
  apply intervalIntegral.integral_congr
  intro r _
  change (quadratic x (insertion source (wordGram source n) s r)).re = _
  simp only [insertion, map_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (quadratic x ((firstBranch source s r j).adjoint * wordGram source n r *
    firstBranch source s r j)).re = (quadratic (firstBranch source s r j x) (wordGram source n r)).re
  rw [quadratic_adjoint]

theorem wordMass_nonnegative (n : ℕ) (s : ℝ)
    (hs : s ∈ Icc source.left source.right) (x : E) : 0 ≤ wordMass source n s x := by
  induction n generalizing s x with
  | zero => rw [wordMass_zero]; exact sq_nonneg _
  | succ n ih =>
      rw [wordMass_succ]
      exact intervalIntegral.integral_nonneg hs.2 fun r hr =>
        Finset.sum_nonneg fun j _ => ih r ⟨hs.1.trans hr.1,hr.2⟩ _

/-- The original input norm is the total complete-word mass. -/
theorem wordMass_hasSum_norm (s : ℝ) (hs : s ∈ Icc source.left source.right) (x : E) :
    HasSum (fun n => wordMass source n s x) (‖x‖^2) := by
  let functional : Operator (E := E) →L[ℝ] ℝ :=
    Complex.reCLM.comp ((quadratic x).restrictScalars ℝ)
  have written := functional.hasSum (wordGram_hasSum_identity source s hs)
  change HasSum (fun n => (quadratic x (wordGram source n s)).re)
    (quadratic x (1 : Operator (E := E))).re at written
  rw [quadratic_one, Complex.ofReal_re] at written
  exact written

end SourceKrausWordMass289
