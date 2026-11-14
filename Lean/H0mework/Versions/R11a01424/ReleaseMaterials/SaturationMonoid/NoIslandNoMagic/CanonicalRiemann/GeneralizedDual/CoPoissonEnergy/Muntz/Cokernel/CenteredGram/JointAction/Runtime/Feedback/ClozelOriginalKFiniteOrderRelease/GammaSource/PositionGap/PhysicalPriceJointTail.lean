import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceGrid
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceJointTail

open BurnolPhysicalState Filter MeasureTheory Set
open scoped Topology
open private probe positive_weight_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.MellinSeparation
open private probe_real continuous_probe_price from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceGrid

private abbrev strip : Set ℂ := Complex.re ⁻¹' Ioo (1/2 : ℝ) 1

private theorem strip_open : IsOpen strip := isOpen_Ioo.preimage Complex.continuous_re

private theorem strip_connected : IsPreconnected strip :=
  ((convex_halfSpace_re_gt (1/2 : ℝ)).inter (convex_halfSpace_re_lt 1)).isPreconnected

private def integrand (v : BurnolPaAmbientCarrier) (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(Real.log x : ℂ) * z) * (v : BurnolL2) x

private theorem integrand_actual (v : BurnolPaAmbientCarrier) (z : ℂ) {x : ℝ} (positive : 0 < x) :
    integrand v z x = (x : ℂ)^(-z) * (v : BurnolL2) x := by
  unfold integrand
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne'),
    ← Complex.ofReal_log positive.le, neg_mul, mul_neg]

private theorem integrand_paid (v : BurnolPaAmbientCarrier) (z : ℂ) (inside : z ∈ strip) :
    IntegrableOn (integrand v z) (Ioi 0) := by
  let d : BurnolCompletedMellinCoordinate := ⟨z, inside.1, inside.2⟩
  have paid := positive_weight_integrable d (v : BurnolL2) v.property.1.1
  apply paid.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (integrand_actual v z hx).symm

private def wholePrice (v : BurnolPaAmbientCarrier) (z : ℂ) : ℂ :=
  ∫ x in Ioi 0, integrand v z x

private theorem original_price (v : BurnolPaAmbientCarrier) (d : BurnolCompletedMellinCoordinate) :
    wholePrice v d.value = burnolCompletedMellinEvaluator d v := by
  have restrict := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f v)
    (burnolAmbientCompletedMellinEvaluator_restrict d)
  refine (setIntegral_congr_fun measurableSet_Ioi (fun _ hx => integrand_actual v d.value hx)).trans ?_
  exact (burnolAmbientCompletedMellinEvaluator_eq_positive_integral_of_positionGap d
    (v : BurnolL2) v.property.1.1).symm.trans restrict

private theorem integrand_norm (v : BurnolPaAmbientCarrier) (z : ℂ) (x : ℝ) :
    ‖integrand v z x‖ = Real.exp (-(z.re * Real.log x)) * ‖(v : BurnolL2) x‖ := by
  unfold integrand
  rw [norm_mul, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, neg_zero,
    zero_mul, sub_zero, neg_mul]
  rw [mul_comm (Real.log x) z.re]

private theorem log_derivative_bound {w z ε : ℝ} (positive : 0 < ε) (near : |w-z| ≤ ε) (t : ℝ) :
    |t| * Real.exp (-(w*t)) ≤
      (1/ε) * (Real.exp (-((z-2*ε)*t)) + Real.exp (-((z+2*ε)*t))) := by
  have absorbed : |t| ≤ (1/ε) * Real.exp (ε*|t|) := by
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ positive).2
    have bound := Real.add_one_le_exp (ε*|t|)
    linarith only [bound, mul_comm ε |t|]
  have shift : (z-w)*t ≤ ε*|t| := calc
    _ ≤ |(z-w)*t| := le_abs_self _
    _ = |w-z| * |t| := by rw [abs_mul, abs_sub_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right near (abs_nonneg _)
  have exponents : -(w*t)+ε*|t| ≤ -(z*t)+2*ε*|t| := by
    linarith only [shift, sub_mul z w t]
  have reciprocal : 0 ≤ (1/ε : ℝ) := by positivity
  calc
    _ ≤ ((1/ε)*Real.exp (ε*|t|)) * Real.exp (-(w*t)) :=
      mul_le_mul_of_nonneg_right absorbed (Real.exp_nonneg _)
    _ = (1/ε) * Real.exp (-(w*t)+ε*|t|) := by rw [Real.exp_add]; ring
    _ ≤ (1/ε) * Real.exp (-(z*t)+2*ε*|t|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponents) reciprocal
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ reciprocal
      by_cases sign : 0 ≤ t
      · rw [show -(z*t)+2*ε*|t| = -((z-2*ε)*t) by rw [abs_of_nonneg sign]; ring]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [show -(z*t)+2*ε*|t| = -((z+2*ε)*t) by rw [abs_of_neg (lt_of_not_ge sign)]; ring]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)

private theorem whole_price_analytic (v : BurnolPaAmbientCarrier) : AnalyticOnNhd ℂ (wholePrice v) strip := by
  apply DifferentiableOn.analyticOnNhd _ strip_open
  intro z inside
  have roomLeft : 0 < z.re-1/2 := sub_pos.mpr inside.1
  have roomRight : 0 < 1-z.re := sub_pos.mpr inside.2
  let ε := min (z.re-1/2) (1-z.re) / 4
  have positive : 0 < ε := div_pos (lt_min roomLeft roomRight) (by norm_num)
  have leftRoom : 2*ε < z.re-1/2 := by
    have lower := min_le_left (z.re-1/2) (1-z.re)
    dsimp only [ε]
    linarith
  have rightRoom : 2*ε < 1-z.re := by
    have lower := min_le_right (z.re-1/2) (1-z.re)
    dsimp only [ε]
    linarith
  let lower : ℂ := z - ((2*ε : ℝ) : ℂ)
  let upper : ℂ := z + ((2*ε : ℝ) : ℂ)
  have lowerIn : lower ∈ strip := by
    change 1/2 < lower.re ∧ lower.re < 1
    simp only [lower, Complex.sub_re, Complex.ofReal_re]
    constructor <;> linarith [inside.1, inside.2]
  have upperIn : upper ∈ strip := by
    change 1/2 < upper.re ∧ upper.re < 1
    simp only [upper, Complex.add_re, Complex.ofReal_re]
    constructor <;> linarith [inside.1, inside.2]
  have distance (w : ℂ) (near : w ∈ Metric.ball z ε) : |w.re-z.re| < ε := by
    have distanceNorm : ‖w-z‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using near
    have h := (Complex.abs_re_le_norm (w-z)).trans_lt distanceNorm
    simpa only [Complex.sub_re] using h
  have within (w : ℂ) (near : w ∈ Metric.ball z ε) : w ∈ strip := by
    have reNear := abs_lt.mp (distance w near)
    change 1/2 < w.re ∧ w.re < 1
    constructor <;> linarith
  let bound (x : ℝ) := (1/ε) * (‖integrand v lower x‖ + ‖integrand v upper x‖)
  let derivative (w : ℂ) (x : ℝ) := -(Real.log x : ℂ) * integrand v w x
  have measurableLog :
      AEStronglyMeasurable (fun x : ℝ => -(Real.log x : ℂ)) (volume.restrict (Ioi 0)) :=
    ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg).aestronglyMeasurable
  have boundPaid : IntegrableOn bound (Ioi 0) :=
    ((integrand_paid v lower lowerIn).norm.add (integrand_paid v upper upperIn).norm).const_mul _
  have derivBound (x : ℝ) (w : ℂ) (near : w ∈ Metric.ball z ε) : ‖derivative w x‖ ≤ bound x := by
    have realBound := log_derivative_bound positive (distance w near).le (Real.log x)
    have scaled := mul_le_mul_of_nonneg_right realBound (norm_nonneg ((v : BurnolL2) x))
    simp only [derivative, bound, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, integrand_norm,
      lower, upper, Complex.add_re, Complex.sub_re, Complex.ofReal_re, mul_assoc, add_mul] at scaled ⊢
    exact scaled
  have pointwise (x : ℝ) (w : ℂ) : HasDerivAt (fun q => integrand v q x) (derivative w x) w := by
    have linear : HasDerivAt (fun q : ℂ => -(Real.log x : ℂ) * q) (-(Real.log x : ℂ)) w := by
      simpa using (hasDerivAt_id w).const_mul (-(Real.log x : ℂ))
    have exponent : HasDerivAt (fun q : ℂ => Complex.exp (-(Real.log x : ℂ) * q))
        (Complex.exp (-(Real.log x : ℂ) * w) * -(Real.log x : ℂ)) w :=
      (Complex.hasDerivAt_exp _).comp w linear
    have rearranged :
        (Complex.exp (-(Real.log x : ℂ) * w) * -(Real.log x : ℂ)) * (v : BurnolL2) x =
          derivative w x := by
      dsimp only [derivative, integrand]
      ring
    exact (exponent.mul_const ((v : BurnolL2) x)).congr_deriv rearranged
  have domain : ∀ᶠ w in 𝓝 z, w ∈ Metric.ball z ε := Metric.ball_mem_nhds z positive
  have actual := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := integrand v) (F' := derivative) (bound := bound)
    (Metric.ball_mem_nhds z positive)
    (domain.mono fun w hw => (integrand_paid v w (within w hw)).aestronglyMeasurable)
    (integrand_paid v z inside) (measurableLog.mul (integrand_paid v z inside).aestronglyMeasurable)
    (.of_forall derivBound) boundPaid (.of_forall fun x w _ => pointwise x w)
  exact actual.2.differentiableAt.differentiableWithinAt

private theorem probe_in_strip (y : ℝ) : (probe y).value ∈ strip :=
  ⟨(probe y).rightHalf, (probe y).belowOne⟩

private theorem probe_continuous : Continuous (fun y : ℝ => (probe y).value) := by
  change Continuous (fun y : ℝ => (3/4 : ℂ) + ((2*Real.pi*y : ℝ) : ℂ) * Complex.I)
  fun_prop

private theorem probe_injective : Function.Injective (fun y : ℝ => (probe y).value) := by
  have read (y : ℝ) : (probe y).value.im = 2*Real.pi*y := by
    norm_num [probe, Complex.add_im, Complex.mul_im, Complex.div_im]
  intro a b equal
  have height := congrArg Complex.im equal
  rw [read, read] at height
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) height

/-- Every rational tail has one original K coordinate that reads both nonzero physical fields. -/
theorem common_price_in_tail (v w : BurnolPaAmbientCarrier) (vLive : v ≠ 0) (wLive : w ≠ 0)
    (cutoff : Nat) : ∃ t, PhysicalPriceGrid.price (cutoff+t) v ≠ 0 ∧
      PhysicalPriceGrid.price (cutoff+t) w ≠ 0 := by
  by_contra absent
  have quiet (t : Nat) : PhysicalPriceGrid.price (cutoff+t) v * PhysicalPriceGrid.price (cutoff+t) w = 0 := by
    by_cases zero : PhysicalPriceGrid.price (cutoff+t) v = 0
    · rw [zero, zero_mul]
    · have other : PhysicalPriceGrid.price (cutoff+t) w = 0 := by
        by_contra live
        exact absent ⟨t,zero,live⟩
      rw [other, mul_zero]
  let product (z : ℂ) := wholePrice v z * wholePrice w z
  have onLine : (fun y : ℝ => burnolCompletedMellinEvaluator (probe y) v *
      burnolCompletedMellinEvaluator (probe y) w) = fun _ => 0 := by
    apply Continuous.ext_on Rat.denseRange_cast ((continuous_probe_price v).mul (continuous_probe_price w)) continuous_const
    rintro _ ⟨q,rfl⟩
    let address := Nat.pair ((Denumerable.eqv ℚ) q) cutoff
    have after : cutoff ≤ address := Nat.right_le_pair _ _
    have time : cutoff+(address-cutoff) = address := by omega
    have height : PhysicalPriceGrid.height address = (q : ℝ) := by
      simp only [PhysicalPriceGrid.height, address, Nat.unpair_pair, Equiv.symm_apply_apply]
    have test := quiet (address-cutoff)
    rw [time] at test
    change burnolCompletedMellinEvaluator (probe (PhysicalPriceGrid.height address)) v *
      burnolCompletedMellinEvaluator (probe (PhysicalPriceGrid.height address)) w = 0 at test
    rw [height] at test
    exact test
  have along (y : ℝ) : product (probe y).value = 0 := by
    unfold product
    rw [original_price, original_price]
    exact congrFun onLine y
  have tends : Tendsto (fun y : ℝ => (probe y).value) (𝓝[≠] 0) (𝓝[≠] (probe 0).value) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨probe_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    exact eventually_mem_nhdsWithin.mono fun y hy => fun same => hy (probe_injective same)
  have often : ∃ᶠ z in 𝓝[≠] (probe 0).value, product z = 0 :=
    tends.frequently ((Eventually.of_forall along).frequently)
  have holomorphic : AnalyticOnNhd ℂ product strip := (whole_price_analytic v).mul (whole_price_analytic w)
  have productZero := holomorphic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    strip_connected (probe_in_strip 0) often
  have existsV : ∃ t, PhysicalPriceGrid.price (cutoff+t) v ≠ 0 := by
    by_contra noneLive
    apply vLive (PhysicalPriceGrid.tail_separates v cutoff ?_)
    intro t
    by_contra live
    exact noneLive ⟨t,live⟩
  obtain ⟨t,live⟩ := existsV
  let d := PhysicalPriceGrid.coordinate (cutoff+t)
  have dIn : d.value ∈ strip := ⟨d.rightHalf,d.belowOne⟩
  have nonzero : wholePrice v d.value ≠ 0 := by rw [original_price]; exact live
  have near : wholePrice w =ᶠ[𝓝 d.value] (0 : ℂ → ℂ) := by
    filter_upwards [strip_open.mem_nhds dIn, ((whole_price_analytic v) d.value dIn).continuousAt.eventually_ne nonzero]
      with z hz priced
    exact (mul_eq_zero.mp (show wholePrice v z * wholePrice w z = 0 from productZero hz)).resolve_left priced
  have wZero := (whole_price_analytic w).eqOn_zero_of_preconnected_of_eventuallyEq_zero strip_connected dIn near
  apply wLive (PhysicalPriceGrid.tail_separates w cutoff ?_)
  intro i
  let q := PhysicalPriceGrid.coordinate (cutoff+i)
  change burnolCompletedMellinEvaluator q w = 0
  rw [← original_price]
  exact wZero (show q.value ∈ strip from ⟨q.rightHalf,q.belowOne⟩)

end OriginalKFiniteOrderRelease.PositionGapCayley.PhysicalPriceJointTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
