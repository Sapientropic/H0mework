import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false

noncomputable section

namespace SaturationMonoid.SourceMomentVisibility

open MeasureTheory ProbabilityTheory Set Complex Filter
open scoped Topology

private theorem window_interior {X : Type*} [MeasurableSpace X]
    (read : X → ℝ) (μ : Measure X) (radius : ℝ)
    (exponential : Ioo (-radius) radius ⊆ integrableExpSet read μ) :
    Ioo (-radius) radius ⊆ interior (integrableExpSet read μ) := by
  calc
    Ioo (-radius) radius = interior (Ioo (-radius) radius) := isOpen_Ioo.interior_eq.symm
    _ ⊆ interior (integrableExpSet read μ) := interior_mono exponential

/-- A two-sided exponential domain makes the full real moments determine the finite measure. -/
theorem measure_eq_of_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (radius : ℝ) (positive : 0 < radius)
    (exponentialμ : Ioo (-radius) radius ⊆ integrableExpSet id μ)
    (exponentialν : Ioo (-radius) radius ⊆ integrableExpSet id ν)
    (moments : ∀ n : ℕ, (∫ t : ℝ, t ^ n ∂μ) = ∫ t : ℝ, t ^ n ∂ν) :
    μ = ν := by
  let band : Set ℂ := reCLM ⁻¹' Ioo (-radius) radius
  have connected : IsPreconnected band :=
    ((convex_Ioo (-radius) radius).linear_preimage reCLM.toLinearMap).isPreconnected
  have origin : (0 : ℂ) ∈ band := by
    change (0 : ℝ) ∈ Ioo (-radius) radius
    exact ⟨neg_lt_zero.mpr positive, positive⟩
  have insideμ (z : ℂ) (inBand : z ∈ band) :
      z.re ∈ interior (integrableExpSet id μ) :=
    window_interior id μ radius exponentialμ inBand
  have insideν (z : ℂ) (inBand : z ∈ band) :
      z.re ∈ interior (integrableExpSet id ν) :=
    window_interior id ν radius exponentialν inBand
  have left : AnalyticOnNhd ℂ (complexMGF id μ) band :=
    fun z inBand => analyticAt_complexMGF (insideμ z inBand)
  have right : AnalyticOnNhd ℂ (complexMGF id ν) band :=
    fun z inBand => analyticAt_complexMGF (insideν z inBand)
  have derivative (σ : Measure ℝ) (atZero : (0 : ℂ).re ∈ interior (integrableExpSet id σ))
      (n : ℕ) :
      iteratedDeriv n (complexMGF id σ) 0 = ↑(∫ t : ℝ, t ^ n ∂σ) := by
    rw [iteratedDeriv_complexMGF atZero]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow,
      integral_complex_ofReal]
  have vanish (n : ℕ) : iteratedDeriv n (complexMGF id μ - complexMGF id ν) 0 = 0 := by
    rw [iteratedDeriv_sub (left 0 origin).contDiffAt (right 0 origin).contDiffAt]
    rw [derivative μ (insideμ 0 origin), derivative ν (insideν 0 origin), moments n, sub_self]
  have delta := left.sub right
  have all : Set.EqOn (complexMGF id μ - complexMGF id ν) 0 band := by
    apply delta.eqOn_zero_of_preconnected_of_eventuallyEq_zero connected origin
    apply analyticOrderAt_eq_top.mp
    apply ENat.eq_top_iff_forall_ge.mpr
    intro n
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (delta 0 origin)).mpr
    intro j _
    exact vanish j
  apply Measure.ext_of_charFun
  funext t
  have onAxis : (t : ℂ) * I ∈ band := by
    change ((t : ℂ) * I).re ∈ Ioo (-radius) radius
    simp only [mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]
    exact ⟨neg_lt_zero.mpr positive, positive⟩
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  exact sub_eq_zero.mp (all onAxis)


section EvenMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

private def density (μ : Measure Ω) (weight : Ω → ℝ) : Measure Ω :=
  μ.withDensity fun x => ↑(weight x).toNNReal

private def evenMeasure (μ : Measure Ω) (read : Ω → ℝ) : Measure ℝ :=
  μ.map read + μ.map (fun x => -read x)

private theorem density_eval {μ : Measure Ω} {weight : Ω → ℝ}
    (measurableWeight : Measurable weight) (test : Ω → ℝ) :
    (∫ x, test x ∂density μ weight) = ∫ x, (↑(weight x).toNNReal : ℝ) * test x ∂μ :=
  integral_withDensity_eq_integral_smul (measurable_real_toNNReal.comp measurableWeight) test

private theorem density_integrable {μ : Measure Ω} {weight test : Ω → ℝ}
    (measurableWeight : Measurable weight) (measurableTest : Measurable test)
    (domination : Integrable (fun x => |weight x| * |test x|) μ) :
    Integrable test (density μ weight) := by
  let measurablePos := measurable_real_toNNReal.comp measurableWeight
  apply (integrable_withDensity_iff_integrable_smul (μ := μ) measurablePos).2
  refine domination.mono' (measurablePos.aestronglyMeasurable.smul measurableTest.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  change ‖(↑(weight x).toNNReal : ℝ) * test x‖ ≤ |weight x| * |test x|
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _), Real.coe_toNNReal']
  exact mul_le_mul_of_nonneg_right (max_le (le_abs_self _) (abs_nonneg _)) (abs_nonneg _)

private theorem even_eval {μ : Measure Ω} {read : Ω → ℝ} (measurableRead : Measurable read)
    {test : ℝ → ℝ} (measurableTest : Measurable test) (paid : Integrable test (evenMeasure μ read)) :
    (∫ t, test t ∂evenMeasure μ read) =
      (∫ x, test (read x) ∂μ) + ∫ x, test (-read x) ∂μ := by
  have parts := (integrable_add_measure (μ := μ.map read) (ν := μ.map (fun x => -read x))).mp paid
  have opposite : Measurable (fun x => -read x) := measurableRead.neg
  rw [evenMeasure, integral_add_measure parts.1 parts.2,
    integral_map measurableRead.aemeasurable measurableTest.aestronglyMeasurable,
    integral_map opposite.aemeasurable measurableTest.aestronglyMeasurable]

private theorem density_window {μ : Measure Ω} {read weight : Ω → ℝ}
    (measurableRead : Measurable read) (measurableWeight : Measurable weight) (radius : ℝ)
    (budget : Integrable (fun x => |weight x| * Real.exp (radius * |read x|)) μ) :
    Ioo (-radius) radius ⊆ integrableExpSet id (evenMeasure (density μ weight) read) := by
  intro t ht
  have tBound : |t| ≤ radius := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have onSide (side : Ω → ℝ) (measurableSide : Measurable side) (sideBound : ∀ x, |side x| = |read x|) :
      Integrable (fun s : ℝ => Real.exp (t * s)) ((density μ weight).map side) := by
    apply (integrable_map_measure (by fun_prop) measurableSide.aemeasurable).2
    apply density_integrable measurableWeight (by fun_prop)
    refine budget.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_mul, abs_abs,
      abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    calc
      t * side x ≤ |t * side x| := le_abs_self _
      _ = |t| * |read x| := by rw [abs_mul, sideBound]
      _ ≤ radius * |read x| := mul_le_mul_of_nonneg_right tBound (abs_nonneg _)
  exact (integrable_add_measure).2
    ⟨onSide read measurableRead (fun _ => rfl), onSide (fun x => -read x) measurableRead.neg
      (fun x => abs_neg (read x))⟩

private theorem signed_eval {μ : Measure Ω} {weight test : Ω → ℝ}
    (measurableWeight : Measurable weight)
    (pos : Integrable test (density μ weight)) (neg : Integrable test (density μ (-weight))) :
    (∫ x, weight x * test x ∂μ) =
      (∫ x, test x ∂density μ weight) - ∫ x, test x ∂density μ (-weight) := by
  have pi := (integrable_withDensity_iff_integrable_smul
    (measurable_real_toNNReal.comp measurableWeight)).mp pos
  have ni := (integrable_withDensity_iff_integrable_smul
    (measurable_real_toNNReal.comp measurableWeight.neg)).mp neg
  change Integrable (fun x => (↑(weight x).toNNReal : ℝ) * test x) μ at pi
  change Integrable (fun x => (↑((-weight) x).toNNReal : ℝ) * test x) μ at ni
  rw [density_eval measurableWeight, density_eval measurableWeight.neg, ← integral_sub pi ni]
  apply integral_congr_ae
  filter_upwards with x
  change weight x * test x = (↑(weight x).toNNReal : ℝ) * test x -
    (↑(-weight x).toNNReal : ℝ) * test x
  rw [← sub_mul, Real.coe_toNNReal', Real.coe_toNNReal']
  by_cases nonnegative : 0 ≤ weight x
  · rw [max_eq_left nonnegative, max_eq_right (neg_nonpos.mpr nonnegative), sub_zero]
  · have nonpositive := le_of_not_ge nonnegative
    rw [max_eq_right nonpositive, max_eq_left (neg_nonneg.mpr nonpositive), zero_sub, neg_neg]

/-- An exponentially dominated signed read with silent even moments has zero bounded even reads. -/
theorem signed_even_test_zero {μ : Measure Ω} {read weight : Ω → ℝ}
    (measurableRead : Measurable read) (measurableWeight : Measurable weight)
    (radius : ℝ) (positive : 0 < radius)
    (budget : Integrable (fun x => |weight x| * Real.exp (radius * |read x|)) μ)
    (moments : ∀ n : ℕ, (∫ x, weight x * read x ^ (2*n) ∂μ) = 0)
    (test : ℝ → ℝ) (measurableTest : Measurable test)
    (even : ∀ t, test (-t) = test t) (bounded : ∀ t, ‖test t‖ ≤ 1) :
    (∫ x, weight x * test (read x) ∂μ) = 0 := by
  let p := density μ weight
  let n := density μ (-weight)
  have wInt : Integrable weight μ := by
    refine budget.mono' measurableWeight.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg positive.le (abs_nonneg _)))
  let _ : IsFiniteMeasure p := isFiniteMeasure_withDensity_ofReal wInt.hasFiniteIntegral
  let _ : IsFiniteMeasure n := isFiniteMeasure_withDensity_ofReal wInt.neg.hasFiniteIntegral
  let _ : IsFiniteMeasure (evenMeasure p read) := by unfold evenMeasure; infer_instance
  let _ : IsFiniteMeasure (evenMeasure n read) := by unfold evenMeasure; infer_instance
  have pWindow := density_window measurableRead measurableWeight radius budget
  have nWindow : Ioo (-radius) radius ⊆ integrableExpSet id (evenMeasure n read) :=
    density_window measurableRead measurableWeight.neg radius (by simpa only [Pi.neg_apply, abs_neg] using budget)
  have atZero : (0 : ℝ) ∈ Ioo (-radius) radius := ⟨neg_lt_zero.mpr positive, positive⟩
  have power (mass : Measure Ω)
      (window : Ioo (-radius) radius ⊆ integrableExpSet id (evenMeasure mass read)) (j : ℕ) :
      Integrable (fun t : ℝ => t^j) (evenMeasure mass read) :=
    integrable_pow_of_mem_interior_integrableExpSet
      (window_interior id _ radius window atZero) j
  have formula (mass : Measure Ω)
      (window : Ioo (-radius) radius ⊆ integrableExpSet id (evenMeasure mass read)) (j : ℕ) :
      (∫ t : ℝ, t^j ∂evenMeasure mass read) =
        (1 + (-1 : ℝ)^j) * ∫ x, read x ^ j ∂mass := by
    rw [even_eval measurableRead (by fun_prop) (power mass window j)]
    have negPower : (fun x => (-read x)^j) = fun x => (-1 : ℝ)^j * read x^j := by
      funext x
      rw [← neg_one_mul (read x), mul_pow]
    rw [negPower, integral_const_mul]
    ring
  have sameMoments (j : ℕ) :
      (∫ t : ℝ, t^j ∂evenMeasure p read) = ∫ t : ℝ, t^j ∂evenMeasure n read := by
    rw [formula p pWindow j, formula n nWindow j]
    rcases Nat.even_or_odd j with ⟨k, two⟩ | odd
    · have index : j = 2*k := by omega
      have ip : Integrable (fun x => read x^(2*k)) p :=
        (power p pWindow (2*k)).left_of_add_measure.comp_aemeasurable measurableRead.aemeasurable
      have ineg : Integrable (fun x => read x^(2*k)) n :=
        (power n nWindow (2*k)).left_of_add_measure.comp_aemeasurable measurableRead.aemeasurable
      have eq := sub_eq_zero.mp ((signed_eval measurableWeight ip ineg).symm.trans (moments k))
      rw [index, eq]
    · simp only [odd.neg_one_pow, add_neg_cancel, zero_mul]
  have same := measure_eq_of_moments radius positive pWindow nWindow sameMoments
  have testp : Integrable test (evenMeasure p read) :=
    (integrable_const (1 : ℝ)).mono' measurableTest.aestronglyMeasurable (Eventually.of_forall bounded)
  have testn : Integrable test (evenMeasure n read) := same ▸ testp
  have pulled := congrArg (fun μ : Measure ℝ => ∫ t, test t ∂μ) same
  rw [even_eval measurableRead measurableTest testp, even_eval measurableRead measurableTest testn] at pulled
  simp only [even] at pulled
  have payp : Integrable (fun x => test (read x)) p :=
    testp.left_of_add_measure.comp_aemeasurable measurableRead.aemeasurable
  have payn : Integrable (fun x => test (read x)) n :=
    testn.left_of_add_measure.comp_aemeasurable measurableRead.aemeasurable
  rw [signed_eval measurableWeight payp payn]
  linarith

end EvenMeasure


section ComplexWeight

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem power_le_exp (radius x : ℝ) (positive : 0 < radius) (nonnegative : 0 ≤ x) (j : ℕ) :
    x ^ j ≤ ((j.factorial : ℝ) / radius ^ j) * Real.exp (radius * x) := by
  have fac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have paid := (div_le_iff₀ fac).mp (Real.pow_div_factorial_le_exp (radius * x) (mul_nonneg positive.le nonnegative) j)
  rw [mul_pow] at paid
  calc
    x ^ j ≤ Real.exp (radius * x) * j.factorial / radius ^ j :=
      (le_div_iff₀ (pow_pos positive j)).mpr (by simpa only [mul_comm (x^j)] using paid)
    _ = _ := by ring

private theorem power_integrable {μ : Measure Ω} {read : Ω → ℝ} {weight : Ω → ℂ}
    (measurableRead : Measurable read) (measurableWeight : Measurable weight)
    (radius : ℝ) (positive : 0 < radius)
    (budget : Integrable (fun x => ‖weight x‖ * Real.exp (radius * |read x|)) μ) (j : ℕ) :
    Integrable (fun x => weight x * ((read x : ℂ)^j)) μ := by
  let C : ℝ := (j.factorial : ℝ) / radius ^ j
  refine (budget.const_mul C).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖weight x‖ * (C * Real.exp (radius * |read x|)) :=
      mul_le_mul_of_nonneg_left (power_le_exp radius |read x| positive (abs_nonneg _) j) (norm_nonneg _)
    _ = _ := by ring

/-- The same even moments control bounded complex tests against the full complex weight. -/
theorem complex_even_test_zero {μ : Measure Ω} {read : Ω → ℝ} {weight : Ω → ℂ}
    (measurableRead : Measurable read) (measurableWeight : Measurable weight)
    (radius : ℝ) (positive : 0 < radius)
    (budget : Integrable (fun x => ‖weight x‖ * Real.exp (radius * |read x|)) μ)
    (moments : ∀ j : ℕ, (∫ x, weight x * (read x : ℂ) ^ (2*j) ∂μ) = 0)
    (test : ℝ → ℂ) (measurableTest : Measurable test)
    (even : ∀ t, test (-t) = test t) (bounded : ∀ t, ‖test t‖ ≤ 1) :
    (∫ x, weight x * test (read x) ∂μ) = 0 := by
  have total : Integrable (fun x => ‖weight x‖) μ := by
    refine budget.mono' measurableWeight.norm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg positive.le (abs_nonneg _)))
  have proj_bound (p : ℂ →L[ℝ] ℝ) (boundedP : ‖p‖ ≤ 1) (value : ℂ) :
      ‖p value‖ ≤ ‖value‖ :=
    (p.le_opNorm value).trans (mul_le_of_le_one_left (norm_nonneg _) boundedP)
  have component (p q : ℂ →L[ℝ] ℝ) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
      Integrable (fun x => p (weight x) * q (test (read x))) μ ∧
        (∫ x, p (weight x) * q (test (read x)) ∂μ) = 0 := by
    have pMeas : Measurable (fun x => p (weight x)) := p.continuous.measurable.comp measurableWeight
    have qMeas : Measurable (fun t => q (test t)) := q.continuous.measurable.comp measurableTest
    have boundQ (t : ℝ) : ‖q (test t)‖ ≤ 1 := (proj_bound q hq _).trans (bounded t)
    have pBudget : Integrable (fun x => |p (weight x)| * Real.exp (radius * |read x|)) μ := by
      refine budget.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
      exact mul_le_mul_of_nonneg_right (by simpa only [← Real.norm_eq_abs] using proj_bound p hp (weight x))
        (Real.exp_pos _).le
    have pMoments (j : ℕ) : (∫ x, p (weight x) * read x ^ (2*j) ∂μ) = 0 := by
      have dom := power_integrable measurableRead measurableWeight radius positive budget (2*j)
      calc
        _ = p (∫ x, weight x * (read x : ℂ) ^ (2*j) ∂μ) := by
          rw [← p.integral_comp_comm dom]
          apply integral_congr_ae
          filter_upwards with x
          rw [← Complex.ofReal_pow, mul_comm (weight x), ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
        _ = 0 := by rw [moments j, map_zero]
    refine ⟨total.mono' (pMeas.mul (qMeas.comp measurableRead)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_), ?_⟩
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (boundQ (read x))).trans (proj_bound p hp _)
    · exact signed_even_test_zero measurableRead pMeas radius positive pBudget pMoments
        (fun t => q (test t)) qMeas (fun t => congrArg q (even t)) boundQ
  have whole : Integrable (fun x => weight x * test (read x)) μ := by
    refine total.mono' (measurableWeight.mul (measurableTest.comp measurableRead)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (bounded (read x))
  have re : ‖reCLM‖ ≤ 1 := reCLM_norm.le
  have im : ‖imCLM‖ ≤ 1 := imCLM_norm.le
  obtain ⟨rr, zeroRR⟩ := component reCLM reCLM re re
  obtain ⟨ii, zeroII⟩ := component imCLM imCLM im im
  obtain ⟨ri, zeroRI⟩ := component reCLM imCLM re im
  obtain ⟨ir, zeroIR⟩ := component imCLM reCLM im re
  apply Complex.ext
  · change RCLike.re (∫ x, weight x * test (read x) ∂μ) = (0 : ℝ)
    rw [← integral_re whole]
    change (∫ x, reCLM (weight x) * reCLM (test (read x)) -
      imCLM (weight x) * imCLM (test (read x)) ∂μ) = 0
    rw [integral_sub rr ii, zeroRR, zeroII, sub_zero]
  · change RCLike.im (∫ x, weight x * test (read x) ∂μ) = (0 : ℝ)
    rw [← integral_im whole]
    change (∫ x, reCLM (weight x) * imCLM (test (read x)) +
      imCLM (weight x) * reCLM (test (read x)) ∂μ) = 0
    rw [integral_add ri ir, zeroRI, zeroIR, add_zero]

end ComplexWeight

end SaturationMonoid.SourceMomentVisibility
