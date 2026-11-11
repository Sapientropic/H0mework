import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedCombRead
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState Filter Set Finset Polynomial MeasureTheory
open BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory
open scoped BigOperators InnerProductSpace Polynomial Topology

local notation "R" => burnolDirectRightResolventCLM
local notation "S" => burnolDirectRightResolvent
local notation "K" => burnolCompletedMellinRieszVector
local notation "seed" => (burnolPaCombApproximation 0:BurnolL2)

private theorem anchor_right (anchor : BurnolCompletedMellinCoordinate) :
    (1/4:ℝ) < (anchor.value/2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [anchor.rightHalf]

private theorem observed_resolvent_word (read : BurnolL2 →L[ℂ] ℂ)
    (anchor : BurnolCompletedMellinCoordinate) (x : ℂ)
    (right : (1/4:ℝ) < (anchor.value/2+x).re) (v : BurnolL2) (length : Nat) :
    x^length * read (S (anchor.value/2+x) (((R anchor)^length) v)) =
      read (S (anchor.value/2+x) v) -
        ∑ i ∈ range length, x^i * read (((R anchor)^(i+1)) v) := by
  have step (w : BurnolL2) :
      x * read (S (anchor.value/2+x) (R anchor w)) =
        read (S (anchor.value/2+x) w) - read (R anchor w) := by
    have action := burnolDirectRightResolvent_identity (anchor.value/2+x) (anchor.value/2)
      right (anchor_right anchor) w
    change S (anchor.value/2+x) w - R anchor w =
      (anchor.value/2+x-anchor.value/2) • S (anchor.value/2+x) (R anchor w) at action
    rw [show anchor.value/2+x-anchor.value/2=x by ring] at action
    simpa only [map_sub, map_smul, smul_eq_mul] using (congrArg read action).symm
  induction length with
  | zero => simp
  | succ n prior =>
    calc
      _ = x^n * (x * read (S (anchor.value/2+x) (R anchor (((R anchor)^n) v)))) := by
        rw [pow_succ' (R anchor) n, mul_apply_eq_comp, pow_succ x n, mul_assoc]
      _ = _ := by
        rw [step, mul_sub, prior, sum_range_succ, pow_succ' (R anchor) n, mul_apply_eq_comp]
        ring

private theorem polynomial_times_decay (p : ℂ[X]) :
    Tendsto (fun x : ℝ => ‖p.eval (x:ℂ)‖ * Real.exp (-x*combDelay)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine squeeze_zero' (Eventually.of_forall fun _ => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) ?_
      (by simpa only [zero_add] using hp.add hq)
    filter_upwards with x
    rw [eval_add, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (Real.exp_nonneg _)
  | monomial n a =>
    have limit := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) combDelay combDelay_pos).const_mul ‖a‖
    rw [mul_zero] at limit
    refine limit.congr' ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [eval_monomial, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx, Real.rpow_natCast]
    rw [show -combDelay*x = -x*combDelay by ring, mul_assoc]

private theorem polynomial_zero_of_decay (p : ℂ[X])
    (vanishes : Tendsto (fun x : ℝ => ‖p.eval (x:ℂ)‖) atTop (𝓝 0)) : p = 0 := by
  by_cases positive : 0 < p.degree
  · have diverges : Tendsto (fun x : ℝ => ‖(x:ℂ)‖) atTop atTop := by
      apply tendsto_id.congr'
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      simp only [id_eq, Complex.norm_real, Real.norm_of_nonneg hx]
    have high := (p.tendsto_norm_atTop positive diverges).eventually (eventually_ge_atTop (1:ℝ))
    have low := vanishes.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
    obtain ⟨_, below, above⟩ := (low.and high).exists
    exact (not_lt_of_ge above below).elim
  · have constant := eq_C_of_degree_le_zero (le_of_not_gt positive)
    have constantLimit : Tendsto (fun x : ℝ => ‖p.eval (x:ℂ)‖) atTop (𝓝 ‖p.coeff 0‖) := by
      apply tendsto_const_nhds.congr'
      filter_upwards with x
      congr 1
      simpa only [eval_C] using (congrArg (Polynomial.eval (x:ℂ)) constant).symm
    have zero := norm_eq_zero.mp (tendsto_nhds_unique constantLimit vanishes)
    rw [constant, zero, map_zero]

private theorem observed_other_resolvent_zero (read : BurnolL2 →L[ℂ] ℂ)
    (anchor : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (silent : ∀ n : Nat, read (((R anchor)^(n+1)) v) = 0)
    (w : ℂ) (right : (1/4:ℝ) < w.re) : read (S w v) = 0 := by
  rw [burnolDirectRightResolvent, map_neg, ← read.integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn w right v)]
  rw [setIntegral_eq_zero_of_forall_eq_zero ?_, neg_zero]
  intro t ht
  rw [burnolDirectRightResolventIntegrand, map_smul,
    DilationFromPowers.observed_inward_zero read anchor v silent t ht, smul_zero]

private def historyPrefix (read : BurnolL2 →L[ℂ] ℂ)
    (anchor : BurnolCompletedMellinCoordinate) (length : Nat) : ℂ[X] :=
  ∑ i ∈ range length, C (read (((R anchor)^(i+1)) seed)) * X^i

private theorem historyPrefix_eval (read : BurnolL2 →L[ℂ] ℂ)
    (anchor : BurnolCompletedMellinCoordinate) (length : Nat) (x : ℂ) :
    (historyPrefix read anchor length).eval x =
      ∑ i ∈ range length, x^i * read (((R anchor)^(i+1)) seed) := by
  simp only [historyPrefix, eval_finsetSum, eval_mul, eval_C, eval_X_pow, mul_comm]

private theorem no_silent_word (anchor : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta anchor.value = 0)
    (opening : analyticOrderAt (fixedPrice anchor) anchor.value ≠ ⊤)
    (indices : Finset Nat) (a : Nat → ℂ) (highest : Nat)
    (within : highest ∈ indices) (largest : ∀ j ∈ indices, j ≤ highest) (live : a highest ≠ 0)
    (silent : ∀ n : Nat, inner ℂ (fourierL2 (K anchor:BurnolL2))
      (((R anchor)^(n+1)) (∑ j ∈ indices, a j • ((R anchor)^j) seed)) = 0) : False := by
  let read := innerSL ℂ (fourierL2 (K anchor:BurnolL2))
  let term (j : Nat) : ℂ[X] := C (a j) * X^(highest-j)
  let denominator : ℂ[X] := ∑ j ∈ indices, term j
  let numerator : ℂ[X] := ∑ j ∈ indices, term j * historyPrefix read anchor j
  have start : denominator.eval 0 = a highest := by
    simp only [denominator, term, eval_finsetSum, eval_mul, eval_C, eval_X_pow]
    rw [sum_eq_single highest]
    · simp
    · intro j hj different
      have strictly := lt_of_le_of_ne (largest j hj) different
      rw [zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt strictly)), mul_zero]
    · exact fun absent => (absent within).elim
  have equation (x : ℂ) (right : (1/4:ℝ)<(anchor.value/2+x).re) :
      denominator.eval x * read (S (anchor.value/2+x) seed) = numerator.eval x := by
    have vanished := observed_other_resolvent_zero read anchor
      (∑ j ∈ indices, a j • ((R anchor)^j) seed) silent _ right
    let action : BurnolL2 →ₗ[ℂ] BurnolL2 :=
      { toFun := S (anchor.value/2+x)
        map_add' := fun left value => by
          have split := burnolDirectRightResolvent_sub (anchor.value/2+x) right left (-value)
          have neg : S (anchor.value/2+x) (-value) = -S (anchor.value/2+x) value := by
            simpa only [neg_one_smul] using burnolDirectRightResolvent_smul (anchor.value/2+x) (-1) value
          simpa only [sub_neg_eq_add, neg] using split
        map_smul' := burnolDirectRightResolvent_smul (anchor.value/2+x) }
    change read (action (∑ j ∈ indices, a j • ((R anchor)^j) seed)) = 0 at vanished
    simp only [map_sum, map_smul, smul_eq_mul] at vanished
    have one (j : Nat) (hj : j ∈ indices) :
        x^highest * (a j * read (action (((R anchor)^j) seed))) =
          (term j).eval x * (read (S (anchor.value/2+x) seed) -
            (historyPrefix read anchor j).eval x) := by
      have degree : highest-j+j=highest := Nat.sub_add_cancel (largest j hj)
      rw [← degree, pow_add]
      simp only [term, eval_mul, eval_C, eval_X_pow, historyPrefix_eval]
      rw [← observed_resolvent_word read anchor x right seed j]
      change (x^(highest-j) * x^j) * (a j * read (S (anchor.value/2+x) (((R anchor)^j) seed))) = _
      ring
    have all := congrArg (fun z : ℂ => x^highest*z) vanished
    change x^highest * (∑ j ∈ indices, a j * read (action (((R anchor)^j) seed))) = x^highest*0 at all
    rw [mul_zero, mul_sum, sum_congr rfl one] at all
    apply sub_eq_zero.mp
    calc
      _ = ∑ j ∈ indices, (term j).eval x * (read (S (anchor.value/2+x) seed) -
          (historyPrefix read anchor j).eval x) := by
        simp only [denominator, numerator, eval_finsetSum, eval_mul, mul_sub, sum_sub_distrib, sum_mul]
      _ = 0 := all
  have small := (polynomial_times_decay denominator).mul_const (delayBudget anchor)
  rw [zero_mul] at small
  have decays : Tendsto (fun x : ℝ => ‖numerator.eval (x:ℂ)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ small
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    have right : (1/4:ℝ)<(anchor.value/2+(x:ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [anchor_right anchor]
    rw [← equation (x:ℂ) right, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (actual_delayed_rightward_price anchor zero hx) (norm_nonneg _)
  have numeratorZero := polynomial_zero_of_decay numerator decays
  have changeParameter : ContinuousAt (fun s : ℂ => (s-anchor.value)/2) anchor.value := by fun_prop
  have changeLimit : Tendsto (fun s : ℂ => (s-anchor.value)/2) (𝓝 anchor.value) (𝓝 0) := by
    simpa only [sub_self, zero_div] using changeParameter.tendsto
  have atZero : denominator.eval 0 ≠ 0 := by rw [start]; exact live
  have denominatorLive : ∀ᶠ s : ℂ in 𝓝 anchor.value, denominator.eval ((s-anchor.value)/2) ≠ 0 :=
    changeLimit.eventually (denominator.continuous.continuousAt.eventually_ne atZero)
  have rightNear : ∀ᶠ s : ℂ in 𝓝 anchor.value, (1/4:ℝ)<(s/2).re :=
    (show ContinuousAt (fun s : ℂ => (s/2).re) anchor.value from by fun_prop).eventually
      (Ioi_mem_nhds (anchor_right anchor))
  apply opening
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [denominatorLive, rightNear] with s nonzero right
  have scalar : anchor.value/2+(s-anchor.value)/2=s/2 := by ring
  have law := equation ((s-anchor.value)/2) (by rw [scalar]; exact right)
  rw [scalar, numeratorZero, eval_zero] at law
  exact (mul_eq_zero.mp law).resolve_left nonzero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

include nontrivial in
/-- Every finite word of original source powers is separated by the same fixed price along any tail. -/
theorem actual_power_price_columns_independent (start : Nat) :
    LinearIndependent ℂ (fun j : Nat => fun n : Nat =>
      inner ℂ (fourierL2 (K c:BurnolL2)) (((R c)^(start+n+j)) seed)) := by
  classical
  let read := innerSL ℂ (fourierL2 (K c:BurnolL2))
  let column (j : Nat) (n : Nat) := read (((R c)^(start+n+j)) seed)
  change LinearIndependent ℂ column
  rw [linearIndependent_iff']
  intro indices a erased i belongs
  by_contra nonzero
  let active := indices.filter (fun j => a j ≠ 0)
  have inhabited : active.Nonempty := ⟨i, mem_filter.mpr ⟨belongs,nonzero⟩⟩
  let highest := active.max' inhabited
  have live := (mem_filter.mp (max'_mem active inhabited)).2
  have eraseActive : ∑ j ∈ active, a j • column j = 0 := by
    refine (sum_subset (filter_subset _ _) ?_).trans erased
    intro j hj absent
    have gone : a j = 0 := by
      by_contra has
      exact absent (mem_filter.mpr ⟨hj,has⟩)
    rw [gone, zero_smul]
  let v := ∑ j ∈ active, a j • ((R c)^j) seed
  have quiet (k : Nat) (after : start ≤ k) : read (((R c)^k) v) = 0 := by
    let n := k-start
    have index : start+n=k := Nat.add_sub_of_le after
    have scalar := congrArg (fun f : Nat → ℂ => f n) eraseActive
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] at scalar
    simp only [v, map_sum, map_smul, ← mul_apply_eq_comp, ← pow_add]
    simpa only [column, index] using scalar
  have opening : analyticOrderAt (fixedPrice c) (c).value ≠ ⊤ := by
    rw [actual_fixed_price_order observation nontrivial half]
    simp
  exact no_silent_word c observation.mathlibZero opening active a highest (max'_mem active inhabited)
    (fun j hj => le_max' active j hj) live
    (fun n => original_power_read_zero_of_tail read c v start quiet (n+1))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
