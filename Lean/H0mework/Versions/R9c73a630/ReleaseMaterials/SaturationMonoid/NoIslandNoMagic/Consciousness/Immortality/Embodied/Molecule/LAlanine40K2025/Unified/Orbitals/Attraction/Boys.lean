import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open MeasureTheory Set Filter
open scoped intervalIntegral BigOperators
open scoped Topology
noncomputable section

/-- Boys function `F_n(T) = ∫₀¹ u^{2n} e^{−T u²} du`. -/
noncomputable def boys (n : ℕ) (T : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, u ^ (2 * n) * Real.exp (-T * u ^ 2)

/-- Whole half-line moment `∫₀^∞ u^{2n} e^{−T u²} du` in double-factorial form. -/
noncomputable def halfMoment (n : ℕ) (T : ℝ) : ℝ :=
  (∏ j ∈ Finset.range n, (2*j+1 : ℝ)) / 2^(n+1) * Real.sqrt Real.pi /
    (T^n * Real.sqrt T)

/-- Tail beyond `u = 1`: `∫₁^∞ u^{2n} e^{−T u²} du`. -/
noncomputable def boysTail (n : ℕ) (T : ℝ) : ℝ :=
  ∫ u in Set.Ioi (1:ℝ), u^(2*n) * Real.exp (-T*u^2)

private theorem powMulExpContinuous (k : ℕ) (a : ℝ) :
    Continuous fun u : ℝ => u ^ k * Real.exp (-a * u ^ 2) := by fun_prop

theorem boys_integrable (n : ℕ) (T : ℝ) :
    IntervalIntegrable (fun u : ℝ => u ^ (2 * n) * Real.exp (-T * u ^ 2)) volume 0 1 :=
  (powMulExpContinuous _ _).intervalIntegrable _ _

theorem boys_nonneg (n : ℕ) (T : ℝ) : 0 ≤ boys n T := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro u _
  rw [pow_mul]
  exact mul_nonneg (pow_nonneg (sq_nonneg u) _) (Real.exp_pos _).le

theorem boys_le (n : ℕ) (T : ℝ) (hT : 0 ≤ T) : boys n T ≤ 1/(2*n+1 : ℝ) := by
  have le : ∀ u ∈ Icc (0:ℝ) 1, u ^ (2*n) * Real.exp (-T*u^2) ≤ u^(2*n) := by
    intro u _
    exact mul_le_of_le_one_right
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) _)
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hT) (sq_nonneg u)))
  have mono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (boys_integrable n T) ((continuous_pow (2*n)).intervalIntegrable _ _) le
  have powint : (∫ u in (0:ℝ)..1, u^(2*n)) = 1/(2*n+1 : ℝ) := by
    rw [integral_pow]
    simp
  calc boys n T ≤ ∫ u in (0:ℝ)..1, u^(2*n) := mono
    _ = 1/(2*n+1 : ℝ) := powint

theorem boys_zero_arg (n : ℕ) : boys n 0 = 1/(2*n+1 : ℝ) := by
  simp only [boys, neg_zero, zero_mul, Real.exp_zero, mul_one]
  rw [integral_pow]
  simp

theorem exp_le_boys (n : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    Real.exp (-T)/(2*n+1 : ℝ) ≤ boys n T := by
  have scale : (∫ u in (0:ℝ)..1, Real.exp (-T)*u^(2*n)) = Real.exp (-T)/(2*n+1 : ℝ) := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  rw [← scale]
  apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
  · exact (continuous_const.mul (continuous_pow (2*n))).intervalIntegrable _ _
  · exact boys_integrable n T
  · intro u hu
    have hu0 : 0 ≤ u := hu.1
    have hu1 : u ≤ 1 := hu.2
    have hsq : u^2 ≤ 1 := by nlinarith
    have hexp : -T ≤ -T*u^2 := by nlinarith [hT]
    rw [mul_comm (u^(2*n))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp)
      (by rw [pow_mul]; exact pow_nonneg (sq_nonneg u) _)

/-- Integration by parts of `d/du [u^{2n+1} e^{−Tu²}]` on `[0,1]`. -/
theorem boys_recurrence (n : ℕ) (T : ℝ) :
    (2*n+1 : ℝ) * boys n T = 2*T * boys (n+1) T + Real.exp (-T) := by
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun u => u^(2*n+1)*Real.exp (-T*u^2))
        ((2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) - 2*T*u^(2*(n+1))*Real.exp (-T*u^2)) u := by
    intro u _
    have e1 : HasDerivAt (fun u : ℝ => -T*u^2) ((-T)*(2*u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul (-T)
    have m := (hasDerivAt_pow (2*n+1) u).mul e1.exp
    refine m.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have hint : IntervalIntegrable (fun u : ℝ =>
      (2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) - 2*T*u^(2*(n+1))*Real.exp (-T*u^2))
      volume 0 1 := by
    exact (by fun_prop : Continuous fun u : ℝ =>
      (2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) - 2*T*u^(2*(n+1))*Real.exp (-T*u^2)).intervalIntegrable _ _
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_congr
      (f := fun u : ℝ => (2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) -
          2*T*u^(2*(n+1))*Real.exp (-T*u^2))
      (g := fun u : ℝ => (2*n+1 : ℝ)*(u^(2*n)*Real.exp (-T*u^2)) -
          (2*T)*(u^(2*(n+1))*Real.exp (-T*u^2)))
      (fun u _ => by ring)] at eq
  rw [intervalIntegral.integral_sub ((boys_integrable n T).const_mul _)
      ((boys_integrable (n+1) T).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at eq
  simp only [one_pow, mul_one, one_mul, zero_pow (by omega : 2*n+1 ≠ 0), zero_mul,
    sub_zero] at eq
  have shape : (2*n+1 : ℝ)*boys n T - 2*T*boys (n+1) T = Real.exp (-T) := eq
  linarith

/-- Differentiating under the compact integral: `F_n' = −F_{n+1}`. -/
theorem boys_hasDerivAt (n : ℕ) (T : ℝ) :
    HasDerivAt (boys n) (-boys (n+1) T) T := by
  set F : ℝ → ℝ → ℝ := fun x u => u^(2*n)*Real.exp (-x*u^2) with hF
  set F' : ℝ → ℝ → ℝ := fun x u => -u^(2*n+2)*Real.exp (-x*u^2) with hF'
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (x₀ := T) (F := F) (F' := F')
    (s := Ioo (T-1) (T+1)) (bound := fun _ => Real.exp (abs T + 1))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    ?_ (boys_integrable n T) ?_ ?_ ?_ ?_
  · replace key := key.2
    have hf_eq : (fun x => ∫ u in (0:ℝ)..1, F x u) = boys n := by
      funext x; rfl
    have hd_eq : (∫ u in (0:ℝ)..1, F' T u) = -boys (n+1) T := by
      have e2 : F' T = fun u : ℝ => -(u^(2*(n+1))*Real.exp (-T*u^2)) := by
        funext u
        simp only [hF']
        rw [show 2*n+2 = 2*(n+1) from rfl, neg_mul]
      rw [e2, intervalIntegral.integral_neg]
      rfl
    rw [hf_eq, hd_eq] at key
    exact key
  · exact Filter.Eventually.of_forall fun x => (powMulExpContinuous _ _).aestronglyMeasurable
  · exact ((by fun_prop : Continuous fun u : ℝ => -u^(2*n+2)*Real.exp (-T*u^2))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro u hu x hx
    have hu01 : u ∈ Icc (0:ℝ) 1 := by
      rcases mem_uIoc.mp hu with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · exact ⟨h0.le, h1⟩
      · exact ⟨by linarith, by linarith⟩
    have hxabs : abs x ≤ abs T+1 := by
      rw [abs_le]
      constructor
      · nlinarith [hx.1, neg_le_abs T]
      · nlinarith [hx.2, le_abs_self T]
    have hu2 : u^2 ≤ 1 := by nlinarith [hu01.1, hu01.2]
    have hux : -x*u^2 ≤ abs T+1 := by
      calc -x*u^2 = -(x*u^2) := neg_mul _ _
        _ ≤ abs (x*u^2) := neg_le_abs _
        _ = abs x*u^2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
        _ ≤ abs x*1 := mul_le_mul_of_nonneg_left hu2 (abs_nonneg x)
        _ ≤ (abs T+1)*1 := mul_le_mul_of_nonneg_right hxabs (by norm_num)
        _ = abs T+1 := mul_one _
    calc ‖F' x u‖ = u^(2*n+2) * Real.exp (-x*u^2) := by
          rw [hF']
          simp only [Real.norm_eq_abs, abs_mul, abs_neg,
            abs_of_nonneg (pow_nonneg hu01.1 (2*n+2)), abs_of_nonneg (Real.exp_pos _).le]
      _ ≤ 1 * Real.exp (abs T+1) := by
          have hu22 : u^(2*n+2) ≤ 1 := pow_le_one₀ hu01.1 hu01.2
          exact mul_le_mul hu22 (Real.exp_le_exp.mpr hux) (Real.exp_pos _).le (by norm_num)
      _ = Real.exp (abs T+1) := one_mul _
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall ?_
    intro u _ x _
    have e1 : HasDerivAt (fun x : ℝ => -x*u^2) ((-1)*u^2) x :=
      ((hasDerivAt_id x).neg).mul_const (u^2)
    have m := (e1.exp).const_mul (u^(2*n))
    apply m.congr_deriv
    simp only [hF']
    rw [pow_add]
    ring

/-- `u^k e^{−Tu}` tends to `0` along `u → ∞` (for `T > 0` it decays exponentially). -/
private theorem tendsto_pow_mul_exp_neg_linear (k : ℕ) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun u : ℝ => u^k * Real.exp (-T*u)) atTop (𝓝 0) := by
  have scale : Tendsto (fun u : ℝ => (T^k)⁻¹ * ((T*u)^k * Real.exp (-(T*u))))
      atTop (𝓝 ((T^k)⁻¹ * 0)) :=
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (tendsto_id.const_mul_atTop hT)).const_mul _
  rw [mul_zero] at scale
  apply scale.congr' (Filter.Eventually.of_forall fun u => ?_)
  rw [mul_pow]
  field_simp [pow_ne_zero _ hT.ne']

/-- `u^k e^{−Tu²} → 0` as `u → ∞` for `T > 0`. -/
private theorem tendsto_pow_mul_exp_neg_sq (k : ℕ) (T : ℝ) (hT : 0 < T) :
    Tendsto (fun u : ℝ => u^k * Real.exp (-T*u^2)) atTop (𝓝 0) := by
  have hbig := tendsto_pow_mul_exp_neg_linear k T hT
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbig
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with u _
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with u hu
    have hle : -T*u^2 ≤ -T*u := by
      nlinarith [mul_nonneg hT.le (mul_nonneg (by linarith : (0:ℝ) ≤ u - 1) (by linarith : (0:ℝ) ≤ u))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)

/-- Integrability of `u^k e^{−Tu²}` on `(a,∞)` for `T > 0`. -/
private theorem integrableOn_pow_mul_exp_neg_sq (k : ℕ) (T : ℝ) (hT : 0 < T) (a : ℝ) :
    IntegrableOn (fun u : ℝ => u^k * Real.exp (-T*u^2)) (Ioi a) := by
  have rp : IntegrableOn (fun u : ℝ => u^(k : ℝ) * Real.exp (-T*u^2)) (Ioi (0:ℝ)) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hT (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (Nat.cast_nonneg k))
  have rpc : IntegrableOn (fun u : ℝ => u^k * Real.exp (-T*u^2)) (Ioi (0:ℝ)) := by
    apply rp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
    simp only [Real.rpow_natCast]
  rcases le_or_gt a 0 with ha | ha
  · have hcont : IntervalIntegrable (fun u : ℝ => u^k * Real.exp (-T*u^2)) volume a 0 :=
      (powMulExpContinuous _ _).intervalIntegrable _ _
    rw [← Ioc_union_Ioi_eq_Ioi ha]
    exact hcont.1.union rpc
  · exact rpc.mono_set (Ioi_subset_Ioi ha.le)

/-- `∫₀^∞ u^{2n} e^{−Tu²}` satisfies the odd-factorial recurrence in `n`. -/
private theorem halfLine_step (n : ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ u in Ioi (0:ℝ), u^(2*(n+1)) * Real.exp (-T*u^2)) =
      (2*n+1 : ℝ)/(2*T) * ∫ u in Ioi (0:ℝ), u^(2*n) * Real.exp (-T*u^2) := by
  have hderiv : ∀ u ∈ Ici (0:ℝ),
      HasDerivAt (fun u => u^(2*n+1)*Real.exp (-T*u^2))
        ((2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) - 2*T*u^(2*(n+1))*Real.exp (-T*u^2)) u := by
    intro u _
    have e1 : HasDerivAt (fun u : ℝ => -T*u^2) ((-T)*(2*u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul (-T)
    have m := (hasDerivAt_pow (2*n+1) u).mul e1.exp
    refine m.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    ring
  have hint0 : IntegrableOn (fun u : ℝ =>
      (2*n+1 : ℝ)*(u^(2*n)*Real.exp (-T*u^2)) - (2*T)*(u^(2*(n+1))*Real.exp (-T*u^2)))
      (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_sq (2*n) T hT 0 |>.const_mul _).sub
      (integrableOn_pow_mul_exp_neg_sq (2*(n+1)) T hT 0 |>.const_mul _)
  have hint : IntegrableOn (fun u : ℝ =>
      (2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) - 2*T*u^(2*(n+1))*Real.exp (-T*u^2))
      (Ioi 0) :=
    hint0.congr (ae_of_all _ fun u => by ring)
  have tend : Tendsto (fun u : ℝ => u^(2*n+1)*Real.exp (-T*u^2)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_sq (2*n+1) T hT
  have eq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint tend
  simp only [zero_pow (by omega : 2*n+1 ≠ 0), zero_mul, sub_zero] at eq
  rw [setIntegral_congr_fun (measurableSet_Ioi)
      (f := fun u : ℝ => (2*n+1 : ℝ)*u^(2*n)*Real.exp (-T*u^2) -
          2*T*u^(2*(n+1))*Real.exp (-T*u^2))
      (g := fun u : ℝ => (2*n+1 : ℝ)*(u^(2*n)*Real.exp (-T*u^2)) -
          (2*T)*(u^(2*(n+1))*Real.exp (-T*u^2)))
      (fun u _ => by ring)] at eq
  rw [integral_sub (integrableOn_pow_mul_exp_neg_sq (2*n) T hT 0 |>.const_mul _)
    (integrableOn_pow_mul_exp_neg_sq (2*(n+1)) T hT 0 |>.const_mul _),
    integral_const_mul, integral_const_mul] at eq
  have shape : (2*n+1 : ℝ)*(∫ u in Ioi (0:ℝ), u^(2*n)*Real.exp (-T*u^2)) -
      2*T*(∫ u in Ioi (0:ℝ), u^(2*(n+1))*Real.exp (-T*u^2)) = 0 := eq
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ)≠0) hT.ne')]
  linarith [shape]

/-- `∫₀^∞ e^{−Tu²}` is `√π/(2√T)`. -/
private theorem halfLine_zero (T : ℝ) (hT : 0 < T) :
    (∫ u in Ioi (0:ℝ), u^0 * Real.exp (-T*u^2)) = Real.sqrt Real.pi/(2*Real.sqrt T) := by
  simp only [pow_zero, one_mul]
  rw [integral_gaussian_Ioi]
  rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ Real.pi)]
  field_simp

theorem halfLine_moment (n : ℕ) (T : ℝ) (hT : 0 < T) :
    (∫ u in Ioi (0:ℝ), u^(2*n) * Real.exp (-T*u^2)) = halfMoment n T := by
  induction n with
  | zero =>
      rw [halfLine_zero T hT]
      simp only [halfMoment, Finset.range_zero, Finset.prod_empty, pow_zero, one_mul]
      ring
  | succ n ih =>
      rw [halfLine_step n T hT, ih]
      unfold halfMoment
      rw [Finset.prod_range_succ]
      have hT' : T ≠ 0 := hT.ne'
      field_simp
      ring

/-- `F_n = halfMoment − boysTail`: the `[0,1]`/`(1,∞)` split of the half-line moment. -/
theorem boys_asymptotic (n : ℕ) (T : ℝ) (hT : 0 < T) :
    boys n T = halfMoment n T - boysTail n T := by
  have split := setIntegral_union
    (show Disjoint (Ioc (0:ℝ) 1) (Ioi (1:ℝ)) from disjoint_left.mpr
      fun x hx1 hx2 => by linarith [hx1.2, show (1:ℝ) < x from hx2]) measurableSet_Ioi
    ((integrableOn_pow_mul_exp_neg_sq (2*n) T hT 0).mono_set Ioc_subset_Ioi_self)
    (integrableOn_pow_mul_exp_neg_sq (2*n) T hT 1)
  rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] at split
  have half := halfLine_moment n T hT
  unfold boys boysTail
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  linarith [split, half]

/-- Iteration of `boys_recurrence`: finite expansion with exact `boys (n+K)` remainder. -/
theorem boys_series (n K : ℕ) (T : ℝ) :
    boys n T =
      Real.exp (-T) *
        ∑ k ∈ Finset.range K, (2*T)^k / ∏ j ∈ Finset.range (k+1), (2*n+2*j+1 : ℝ) +
      (2*T)^K / (∏ j ∈ Finset.range K, (2*n+2*j+1 : ℝ)) * boys (n+K) T := by
  induction K with
  | zero => simp
  | succ K ih =>
      have hrec := boys_recurrence (n+K) T
      push_cast at hrec
      have hQ : (2*n+2*K+1 : ℝ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero (2*n+2*K)
      have hsub : boys (n+K) T =
          (2*T*boys (n+K+1) T + Real.exp (-T))/(2*n+2*K+1 : ℝ) := by
        rw [eq_div_iff hQ]
        linarith [hrec]
      have hP : (∏ j ∈ Finset.range K, (2*n+2*j+1 : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun j _ => by
          exact_mod_cast Nat.succ_ne_zero (2*n+2*j)
      rw [ih, hsub, Finset.sum_range_succ, Finset.prod_range_succ]
      field_simp [hP, hQ]
      ring

/-- The tail `∫₁^∞ u^{2n} e^{−Tu²}` is nonnegative. -/
theorem boysTail_nonneg (n : ℕ) (T : ℝ) (_hT : 0 < T) : 0 ≤ boysTail n T := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg (pow_nonneg (by linarith [show (1:ℝ) < u from hu]) _)
    (Real.exp_pos _).le

/-- Exact odd tail: `∫₁^∞ u^{2j+1} e^{−Tu²} = e^{−T} j!/(2T^{j+1}) · ∑_{k≤j} T^k/k!`. -/
private theorem oddTail_eval (j : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ u in Ioi (1:ℝ), u^(2*j+1) * Real.exp (-T*u^2) =
      Real.exp (-T) * (j.factorial : ℝ) / (2*T^(j+1)) *
        ∑ k ∈ Finset.range (j+1), T^k/(k.factorial : ℝ) := by
  induction j with
  | zero =>
      have hderiv : ∀ u ∈ Ici (1:ℝ),
          HasDerivAt (fun u : ℝ => -Real.exp (-T*u^2)/(2*T)) (u*Real.exp (-T*u^2)) u := by
        intro u _
        have e1 : HasDerivAt (fun u : ℝ => -T*u^2) ((-T)*(2*u)) u := by
          simpa using (hasDerivAt_pow 2 u).const_mul (-T)
        have m := (e1.exp).neg |>.div_const (2*T)
        refine m.congr_deriv ?_
        field_simp [hT.ne']
      have hint : IntegrableOn (fun u : ℝ => u*Real.exp (-T*u^2)) (Ioi 1) := by
        have h1 := integrableOn_pow_mul_exp_neg_sq 1 T hT 1
        apply h1.congr
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _
        simp only [pow_one]
      have tend : Tendsto (fun u : ℝ => -Real.exp (-T*u^2)/(2*T)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun u : ℝ => Real.exp (-T*u^2)) atTop (𝓝 0) := by
          have h := tendsto_pow_mul_exp_neg_sq 0 T hT
          simpa using h
        have := h0.neg.div_const (2*T)
        simpa [zero_div] using this
      have eq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint tend
      simp only [one_pow, mul_one, neg_div, sub_neg_eq_add, zero_add] at eq
      simp only [show (2*0+1 : ℕ) = 1 from rfl, pow_one, Finset.range_one,
        Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [eq]
      ring
  | succ j ih =>
      have hderiv : ∀ u ∈ Ici (1:ℝ),
          HasDerivAt (fun u : ℝ => u^(2*j+2)*Real.exp (-T*u^2))
            ((2*j+2 : ℝ)*(u^(2*j+1)*Real.exp (-T*u^2)) -
              (2*T)*(u^(2*j+3)*Real.exp (-T*u^2))) u := by
        intro u _
        have e1 : HasDerivAt (fun u : ℝ => -T*u^2) ((-T)*(2*u)) u := by
          simpa using (hasDerivAt_pow 2 u).const_mul (-T)
        have m := (hasDerivAt_pow (2*j+2) u).mul e1.exp
        refine m.congr_deriv ?_
        rw [show 2*j+2-1 = 2*j+1 from rfl]
        push_cast
        ring
      have hint : IntegrableOn (fun u : ℝ =>
          (2*j+2 : ℝ)*(u^(2*j+1)*Real.exp (-T*u^2)) -
            (2*T)*(u^(2*j+3)*Real.exp (-T*u^2))) (Ioi 1) :=
        (integrableOn_pow_mul_exp_neg_sq (2*j+1) T hT 1 |>.const_mul _).sub
          (integrableOn_pow_mul_exp_neg_sq (2*j+3) T hT 1 |>.const_mul _)
      have tend : Tendsto (fun u : ℝ => u^(2*j+2)*Real.exp (-T*u^2)) atTop (𝓝 0) :=
        tendsto_pow_mul_exp_neg_sq (2*j+2) T hT
      have eq := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint tend
      simp only [one_pow, mul_one, one_mul] at eq
      rw [integral_sub (integrableOn_pow_mul_exp_neg_sq (2*j+1) T hT 1 |>.const_mul _)
        (integrableOn_pow_mul_exp_neg_sq (2*j+3) T hT 1 |>.const_mul _),
        integral_const_mul, integral_const_mul] at eq
      set I : ℝ := ∫ u in Ioi (1:ℝ), u^(2*j+1)*Real.exp (-T*u^2) with hI
      set J : ℝ := ∫ u in Ioi (1:ℝ), u^(2*j+3)*Real.exp (-T*u^2) with hJ
      have eq' : (2*T)*J = (2*j+2 : ℝ)*I + Real.exp (-T) := by linarith [eq]
      have hstep : J = ((2*j+2 : ℝ)*I + Real.exp (-T))/(2*T) := by
        rw [eq_div_iff (mul_ne_zero (by norm_num : (2:ℝ)≠0) hT.ne'), mul_comm]
        exact eq'
      rw [show 2*(j+1)+1 = 2*j+3 from rfl]
      change _ = Real.exp (-T) * ((j+1).factorial : ℝ) / (2*T^(j+1+1)) *
        ∑ k ∈ Finset.range (j+1+1), T^k/(k.factorial : ℝ)
      rw [← hJ, hstep, ih]
      simp_rw [Finset.sum_range_succ]
      have hfact : ((j+1).factorial : ℝ) = (j+1)*(j.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [hfact]
      have hT' : T ≠ 0 := hT.ne'
      have hf0 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      field_simp [hT', hf0]
      ring

/-- Tail bound: `u^{2n} ≤ u^{2n+1}` on `u ≥ 1` plus the exact odd-power sum. -/
theorem boysTail_le (n : ℕ) (T : ℝ) (hT : 0 < T) :
    boysTail n T ≤
      Real.exp (-T) * (n.factorial : ℝ) / (2 * T^(n+1)) *
        ∑ k ∈ Finset.range (n+1), T^k/(k.factorial : ℝ) := by
  rw [← oddTail_eval n T hT]
  apply setIntegral_mono_on (integrableOn_pow_mul_exp_neg_sq (2*n) T hT 1)
    (integrableOn_pow_mul_exp_neg_sq (2*n+1) T hT 1) measurableSet_Ioi
  intro u hu
  have hu1 : (1:ℝ) ≤ u := le_of_lt (mem_Ioi.mp hu)
  have hu0 : (0:ℝ) ≤ u := by linarith
  have hkey : u^(2*n+1)*Real.exp (-T*u^2) - u^(2*n)*Real.exp (-T*u^2) =
      (u-1)*u^(2*n)*Real.exp (-T*u^2) := by rw [pow_succ]; ring
  nlinarith [mul_nonneg (sub_nonneg.mpr hu1)
    (mul_nonneg (pow_nonneg hu0 (2*n)) (Real.exp_pos (-T*u^2)).le), hkey]
