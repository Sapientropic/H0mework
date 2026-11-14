import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.SourceMomentVisibility
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option autoImplicit false

noncomputable section

namespace SaturationMonoid.PositiveTimeJointMoments

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology

private abbrev time : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private abbrev times : Measure (ℝ × ℝ) := time.prod time

/-- This is the time moment before any scalar normalization. -/
def moment (source : ℝ → ℂ) (degree : ℕ) : ℂ :=
  ∫ t : ℝ, (t : ℂ)^degree * source t ∂time

private theorem positive_times : ∀ᵐ p ∂times, 0 < p.1 ∧ 0 < p.2 := by
  change ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))),
    p ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

private def radius (p : ℝ × ℝ) : ℝ := Real.sqrt (p.1 * p.2)

private def weight (a b : ℝ → ℂ) (cutoff : ℕ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 : ℂ)^cutoff * a p.1) * ((p.2 : ℂ)^cutoff * b p.2)

private theorem radius_le (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.sqrt (s*t) ≤ (s+t)/2 := by
  rw [Real.sqrt_mul hs]
  nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt t), Real.sq_sqrt hs, Real.sq_sqrt ht]

private theorem monomial_decay_integrable (degree : ℕ) (decay : ℝ) (positive : 0 < decay) :
    Integrable (fun t : ℝ => t^degree * Real.exp (-decay*t)) time := by
  have atZero : (-1 : ℝ) < degree := by
    exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg degree)
  change IntegrableOn (fun t : ℝ => t^degree * Real.exp (-decay*t)) (Ioi 0)
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) atZero one_pos positive

private theorem exp_budget (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (decay C D : ℝ) (decayPos : 0 < decay) (cNonneg : 0 ≤ C) (dNonneg : 0 ≤ D)
    (aBound : ∀ t > 0, ‖a t‖ ≤ C * Real.exp (-decay*t))
    (bBound : ∀ t > 0, ‖b t‖ ≤ D * Real.exp (-decay*t)) (cutoff : ℕ) :
    Integrable (fun p => ‖weight a b cutoff p‖ * Real.exp (decay * |radius p|)) times := by
  let majorant (t : ℝ) : ℝ := t^cutoff * Real.exp (-(decay/2)*t)
  have majorantInt : Integrable majorant time :=
    monomial_decay_integrable cutoff (decay/2) (half_pos decayPos)
  have paired := (majorantInt.const_mul C).mul_prod (majorantInt.const_mul D)
  refine paired.mono' (by unfold weight radius; fun_prop) ?_
  filter_upwards [positive_times] with p inside
  obtain ⟨hs, ht⟩ := inside
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  simp only [weight, radius, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, abs_of_pos ht, abs_of_nonneg (Real.sqrt_nonneg _)]
  have m₁ := mul_le_mul_of_nonneg_left (aBound p.1 hs) (pow_nonneg hs.le cutoff)
  have m₂ := mul_le_mul_of_nonneg_left (bBound p.2 ht) (pow_nonneg ht.le cutoff)
  have expMove : Real.exp (decay * Real.sqrt (p.1*p.2)) ≤
      Real.exp (decay * ((p.1+p.2)/2)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (radius_le _ _ hs.le ht.le) decayPos.le)
  calc
    _ ≤ (p.1^cutoff * (C * Real.exp (-decay*p.1))) *
        (p.2^cutoff * (D * Real.exp (-decay*p.2))) *
        Real.exp (decay * ((p.1+p.2)/2)) := by
      exact mul_le_mul (mul_le_mul m₁ m₂ (by positivity) (by positivity)) expMove (by positivity)
        (by positivity)
    _ = _ := by
      dsimp [majorant]
      calc
        _ = (C*p.1^cutoff)*(D*p.2^cutoff) *
            (Real.exp (-decay*p.1) * Real.exp (-decay*p.2) *
              Real.exp (decay*((p.1+p.2)/2))) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add,
            show -decay*p.1 + -decay*p.2 + decay*((p.1+p.2)/2) =
              -(decay/2)*p.1 + -(decay/2)*p.2 by ring, Real.exp_add]
          ring

private theorem joint_even (a b : ℝ → ℂ) (cutoff degree : ℕ) :
    (∫ p, weight a b cutoff p * (radius p : ℂ)^(2*degree) ∂times) =
      moment a (cutoff+degree) * moment b (cutoff+degree) := by
  rw [moment, moment, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [positive_times] with p inside
  have square : (radius p : ℂ)^(2 : ℕ) = (p.1 : ℂ) * (p.2 : ℂ) := by
    rw [← Complex.ofReal_pow, radius, Real.sq_sqrt (mul_nonneg inside.1.le inside.2.le),
      Complex.ofReal_mul]
  rw [pow_mul, square, mul_pow, weight, pow_add, pow_add]
  ring

private def phase (ξ t : ℝ) : ℂ :=
  Complex.exp (2 * ((ξ : ℂ) * I) * (Real.log |t| : ℂ))

private theorem phase_bound (ξ t : ℝ) : ‖phase ξ t‖ ≤ 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

private theorem phase_split (ξ s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    phase ξ (Real.sqrt (s*t)) =
      Complex.exp (((ξ : ℂ)*I) * (Real.log s : ℂ)) *
        Complex.exp (((ξ : ℂ)*I) * (Real.log t : ℂ)) := by
  rw [phase, abs_of_nonneg (Real.sqrt_nonneg _), Real.log_sqrt (mul_nonneg hs.le ht.le),
    Real.log_mul hs.ne' ht.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem line_weight (f : ℝ → ℂ) (cutoff : ℕ) (ξ : ℝ) :
    mellin f ((cutoff : ℂ) + 1 + (ξ : ℂ)*I) =
      ∫ t : ℝ, ((t : ℂ)^cutoff * f t) *
        Complex.exp (((ξ : ℂ)*I) * (Real.log t : ℂ)) ∂time := by
  unfold mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have positive : 0 < t := ht
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  rw [show (cutoff : ℂ) + 1 + (ξ : ℂ)*I - 1 = (cutoff : ℂ) + (ξ : ℂ)*I by ring,
    Complex.cpow_add _ _ nonzero, Complex.cpow_natCast, Complex.cpow_def_of_ne_zero nonzero,
    ← Complex.ofReal_log positive.le, smul_eq_mul,
    mul_comm (Real.log t : ℂ) ((ξ : ℂ)*I)]
  ring

private theorem joint_line (a b : ℝ → ℂ) (cutoff : ℕ) (ξ : ℝ) :
    mellin a ((cutoff : ℂ) + 1 + (ξ : ℂ)*I) * mellin b ((cutoff : ℂ) + 1 + (ξ : ℂ)*I) =
      ∫ p, weight a b cutoff p * phase ξ (radius p) ∂times := by
  rw [line_weight, line_weight, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [positive_times] with p inside
  rw [radius, phase_split ξ _ _ inside.1 inside.2, weight]
  ring

private abbrev halfPlane : Set ℂ := reCLM ⁻¹' Ioi (0 : ℝ)

private theorem profile_analytic (f : ℝ → ℂ) (continuous : Continuous f)
    (decay C : ℝ) (decayPos : 0 < decay) (nonnegative : 0 ≤ C)
    (bound : ∀ t > 0, ‖f t‖ ≤ C * Real.exp (-decay*t)) :
    AnalyticOnNhd ℂ (mellin f) halfPlane := by
  have infinity : f =O[atTop] fun t => Real.exp (-decay*t) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact bound t ht
  have zero : f =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact (bound t ht').trans (mul_le_of_le_one_right nonnegative
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr decayPos.le) ht'.le)))
  have derivative : DifferentiableOn ℂ (mellin f) halfPlane := by
    intro z hz
    have positive : 0 < z.re := hz
    exact (mellin_differentiableAt_of_isBigO_rpow_exp decayPos
      (continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
      infinity zero positive).differentiableWithinAt
  exact derivative.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re)

private theorem integer_moment (f : ℝ → ℂ) (j : ℕ) :
    mellin f ((j : ℂ)+1) = moment f j := by
  simp only [mellin, moment, add_sub_cancel_right, Complex.cpow_natCast, smul_eq_mul]

/-- Two actual positive-time sources with exponential domain have simultaneous nonzero moments on every tail. -/
theorem joint_tail (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (decay C D : ℝ) (decayPos : 0 < decay) (cNonneg : 0 ≤ C) (dNonneg : 0 ≤ D)
    (aBound : ∀ t > 0, ‖a t‖ ≤ C * Real.exp (-decay*t))
    (bBound : ∀ t > 0, ‖b t‖ ≤ D * Real.exp (-decay*t))
    (liveA : ∃ j, moment a j ≠ 0) (liveB : ∃ j, moment b j ≠ 0) (cutoff : ℕ) :
    ∃ j ≥ cutoff, moment a j ≠ 0 ∧ moment b j ≠ 0 := by
  by_contra disjoint
  have silent (degree : ℕ) :
      (∫ p, weight a b cutoff p * (radius p : ℂ)^(2*degree) ∂times) = 0 := by
    rw [joint_even, mul_eq_zero]
    by_cases erased : moment a (cutoff+degree) = 0
    · exact Or.inl erased
    · refine Or.inr ?_
      by_contra alive
      exact disjoint ⟨cutoff+degree, by omega, erased, alive⟩
  have measurablePhase (ξ : ℝ) : Measurable (phase ξ) := by unfold phase; fun_prop
  have zeroLine (ξ : ℝ) :
      mellin a ((cutoff : ℂ)+1+(ξ : ℂ)*I) * mellin b ((cutoff : ℂ)+1+(ξ : ℂ)*I) = 0 := by
    rw [joint_line]
    exact SourceMomentVisibility.complex_even_test_zero
      (show Measurable radius by unfold radius; fun_prop)
      (show Measurable (weight a b cutoff) by unfold weight; fun_prop)
      decay decayPos (exp_budget a b ha hb decay C D decayPos cNonneg dNonneg aBound bBound cutoff)
      silent (phase ξ) (measurablePhase ξ) (fun t => by simp [phase, abs_neg]) (phase_bound ξ)
  let center : ℝ := (cutoff : ℝ)+1
  let vertical : Set ℂ := reCLM ⁻¹' {center}
  have centerOn : (center : ℂ) ∈ vertical := by simp [vertical]
  have nextOn : (center : ℂ)+I ∈ vertical := by simp [vertical]
  have distinct : (center : ℂ) ≠ (center : ℂ)+I := by
    intro same
    have impossible := congrArg Complex.im same
    simp at impossible
  have nontrivial : vertical.Nontrivial := ⟨_, centerOn, _, nextOn, distinct⟩
  have lineConnected : IsPreconnected vertical :=
    ((convex_singleton center).linear_preimage reCLM.toLinearMap).isPreconnected
  have freq : ∃ᶠ z in 𝓝[≠] (center : ℂ), z ∈ vertical :=
    frequently_mem_iff_neBot.mpr (lineConnected.preperfect_of_nontrivial nontrivial (center : ℂ) centerOn)
  have zfreq : ∃ᶠ z in 𝓝[≠] (center : ℂ), (mellin a * mellin b) z = 0 :=
    freq.mp <| by
      filter_upwards with z hz
      have re : z.re = center := hz
      rw [← re_add_im z, re, show (center : ℂ) = (cutoff : ℂ)+1 by simp [center]]
      exact zeroLine z.im
  have analyticA := profile_analytic a ha decay C decayPos cNonneg aBound
  have analyticB := profile_analytic b hb decay D decayPos dNonneg bBound
  have centerIn : (center : ℂ) ∈ halfPlane := by change 0 < center; unfold center; positivity
  have whole : IsPreconnected halfPlane :=
    ((convex_Ioi (0 : ℝ)).linear_preimage reCLM.toLinearMap).isPreconnected
  have zeroAll := (analyticA.mul analyticB).eqOn_zero_of_preconnected_of_frequently_eq_zero
    whole centerIn zfreq
  rcases analyticA.eq_zero_or_eq_zero_of_mul_eq_zero analyticB zeroAll whole with zeroA | zeroB
  · obtain ⟨j, live⟩ := liveA
    have inBand : (j : ℂ)+1 ∈ halfPlane := by
      change 0 < ((j : ℂ)+1).re
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity
    exact live ((integer_moment a j).symm.trans (zeroA _ inBand))
  · obtain ⟨j, live⟩ := liveB
    have inBand : (j : ℂ)+1 ∈ halfPlane := by
      change 0 < ((j : ℂ)+1).re
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity
    exact live ((integer_moment b j).symm.trans (zeroB _ inBand))

end SaturationMonoid.PositiveTimeJointMoments
