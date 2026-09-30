import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowJets
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
open scoped Topology ContDiff NNReal ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowKernelHalfDensity
open Set Filter MeasureTheory
open NativeForwardWindowSource (kernel kernel_smooth kernel_compact kernel_nonnegative)
noncomputable section

def rootKernel (x : ℝ) : ℝ := Real.sqrt (kernel x)

theorem square (x : ℝ) : rootKernel x ^ 2 = kernel x :=
  Real.sq_sqrt (kernel_nonnegative x)

theorem nonnegative (x : ℝ) : 0 ≤ rootKernel x := Real.sqrt_nonneg _

theorem continuous : Continuous rootKernel := Real.continuous_sqrt.comp kernel_smooth.continuous

theorem support : Function.support rootKernel = Function.support kernel := by
  ext x
  simp only [Function.mem_support,rootKernel,ne_eq]
  exact not_congr (Real.sqrt_eq_zero (kernel_nonnegative x))

theorem compact : HasCompactSupport rootKernel := by
  simpa only [HasCompactSupport,tsupport,support] using kernel_compact

theorem support_interval : tsupport rootKernel = Icc (-2 : ℝ) (-1) := by
  rw [tsupport,support,← tsupport,kernel,NativeForwardWindowSource.bump.tsupport_normed_eq]
  ext x
  simp only [Metric.mem_closedBall,Real.dist_eq,abs_le,NativeForwardWindowSource.bump,mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem smoothAt_of_nonzero (x : ℝ) (positive : kernel x ≠ 0) :
    ContDiffAt ℝ ∞ rootKernel x := kernel_smooth.contDiffAt.sqrt positive

theorem derivative_of_nonzero (x : ℝ) (positive : kernel x ≠ 0) :
    HasDerivAt rootKernel (deriv kernel x / (2 * rootKernel x)) x :=
  ((kernel_smooth.differentiable (by simp)).differentiableAt.hasDerivAt).sqrt positive

private theorem quadratic_upper {f : ℝ → ℝ} (smooth : ContDiff ℝ ∞ f)
    {C : ℝ} (bound : ∀ z,iteratedDeriv 2 f z ≤ C) (x y : ℝ) :
    f y ≤ f x + deriv f x * (y-x) + C*(y-x)^2/2 := by
  by_cases same : x=y
  · subst y
    simp
  have twice : ContDiff ℝ 2 f := smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  obtain ⟨z,_,eqn⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) same twice.contDiffOn
  have differentiable : HasDerivAt f (deriv f x) x :=
    ((smooth.differentiable (by simp)).differentiableAt.hasDerivAt)
  have within : derivWithin f (uIcc x y) x=deriv f x :=
    differentiable.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_uIcc same) x (left_mem_uIcc))
  norm_num [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_one,within,
    smul_eq_mul] at eqn
  have paid := mul_le_mul_of_nonneg_right (bound z) (sq_nonneg (y-x))
  nlinarith

theorem glaeser {f : ℝ → ℝ} (smooth : ContDiff ℝ ∞ f)
    (nonneg : ∀ x,0≤f x) {C : ℝ} (positive : 0<C)
    (bound : ∀ z,iteratedDeriv 2 f z ≤ C) (x : ℝ) :
    (deriv f x)^2 ≤ 2*C*f x := by
  have estimate := quadratic_upper smooth bound x (x-deriv f x/C)
  have paid := nonneg (x-deriv f x/C)
  have algebra : f x + deriv f x * (x-deriv f x/C-x) +
      C*(x-deriv f x/C-x)^2/2 = f x-(deriv f x)^2/(2*C) := by
    field_simp
    ring
  rw [algebra] at estimate
  have ratio : (deriv f x)^2/(2*C)≤f x := by linarith
  exact (div_le_iff₀ (by positivity : 0<2*C)).mp ratio |>.trans_eq (by ring)

private theorem sqrt_regularized_bound {f : ℝ → ℝ} (smooth : ContDiff ℝ ∞ f)
    (nonneg : ∀ x,0≤f x) {C : ℝ} (positive : 0<C)
    (bound : ∀ z,iteratedDeriv 2 f z ≤ C) {e : ℝ} (epos : 0<e) (x : ℝ) :
    ‖deriv (fun y => Real.sqrt (f y+e)) x‖ ≤ Real.sqrt C := by
  have hpos : 0<f x+e := by linarith [nonneg x]
  have derivative : HasDerivAt (fun y => Real.sqrt (f y+e))
      (deriv f x/(2*Real.sqrt (f x+e))) x :=
    (((smooth.differentiable (by simp)).differentiableAt.hasDerivAt).add_const e).sqrt hpos.ne'
  rw [derivative.deriv,Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : 0<2*Real.sqrt (f x+e))]
  apply (div_le_iff₀ (by positivity : 0<2*Real.sqrt (f x+e))).mpr
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (by positivity))).mp
  have source := glaeser smooth nonneg positive bound x
  rw [sq_abs,mul_pow,Real.sq_sqrt positive.le,mul_pow,Real.sq_sqrt hpos.le]
  nlinarith

theorem sqrt_lipschitz {f : ℝ → ℝ} (smooth : ContDiff ℝ ∞ f)
    (nonneg : ∀ x,0≤f x) {C : ℝ} (positive : 0<C)
    (bound : ∀ z,iteratedDeriv 2 f z ≤ C) :
    LipschitzWith ⟨Real.sqrt C,Real.sqrt_nonneg C⟩ (fun x => Real.sqrt (f x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖Real.sqrt (f x)-Real.sqrt (f y)‖ ≤ Real.sqrt C*‖x-y‖
  have paid (e : ℝ) (epos : 0<e) :
      ‖Real.sqrt (f x+e)-Real.sqrt (f y+e)‖ ≤ Real.sqrt C*‖x-y‖ := by
    have regular : Differentiable ℝ (fun z => Real.sqrt (f z+e)) :=
      fun z => ((smooth.differentiable (by simp) z).add_const e).sqrt (by linarith [nonneg z])
    exact convex_univ.norm_image_sub_le_of_norm_deriv_le (fun z _ => regular z)
      (fun z _ => sqrt_regularized_bound smooth nonneg positive bound epos z) (mem_univ y) (mem_univ x)
  have continuous : Continuous (fun e : ℝ => ‖Real.sqrt (f x+e)-Real.sqrt (f y+e)‖) := by fun_prop
  have limit := continuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have eventually : ∀ᶠ e : ℝ in 𝓝[>] (0:ℝ),
      ‖Real.sqrt (f x+e)-Real.sqrt (f y+e)‖ ≤ Real.sqrt C*‖x-y‖ :=
    eventually_nhdsWithin_of_forall fun e positive => paid e positive
  simpa only [add_zero] using le_of_tendsto limit eventually

theorem source_lipschitz : ∃ C : ℝ≥0, LipschitzWith C rootKernel := by
  obtain ⟨B,bounded⟩ := (NativeForwardWindowJets.kernelJet_smooth 2).continuous.bounded_above_of_compact_support
    (NativeForwardWindowJets.kernelJet_compact 2)
  have B0 : 0≤B := (norm_nonneg _).trans (bounded 0)
  refine ⟨⟨Real.sqrt (B+1),Real.sqrt_nonneg _⟩,?_⟩
  exact sqrt_lipschitz kernel_smooth kernel_nonnegative (C := B+1) (by linarith) (fun z =>
    (le_abs_self _).trans ((bounded z).trans (by linarith)))

theorem source_derivative : ∀ᵐ x : ℝ,HasDerivAt rootKernel (deriv rootKernel x) x := by
  obtain ⟨C,paid⟩ := source_lipschitz
  exact paid.ae_differentiableAt_real.mono fun _ h => h.hasDerivAt

theorem source_derivative_bound : ∃ C : ℝ,0≤C ∧ ∀ x,‖deriv rootKernel x‖≤C := by
  obtain ⟨C,paid⟩ := source_lipschitz
  exact ⟨C,C.coe_nonneg,fun _ => norm_deriv_le_of_lipschitz paid⟩

theorem root_memLp (p : ℝ≥0∞) : MemLp rootKernel p (volume : Measure ℝ) :=
  continuous.memLp_of_hasCompactSupport compact

theorem root_mass : (∫ x : ℝ,rootKernel x^2)=1 := by
  simp only [square]
  exact NativeForwardWindowSource.kernel_mass

theorem derivative_memLp (p : ℝ≥0∞) : MemLp (deriv rootKernel) p (volume : Measure ℝ) := by
  obtain ⟨C,_,paid⟩ := source_derivative_bound
  exact compact.deriv.memLp_of_bound (aestronglyMeasurable_deriv (𝕜 := ℝ) (F := ℝ) rootKernel volume)
    C (Eventually.of_forall paid)

theorem derivative_support : tsupport (deriv rootKernel) ⊆ Icc (-2 : ℝ) (-1) := by
  rw [← support_interval]
  exact tsupport_deriv_subset

theorem shifted_derivative (time : ℝ) :
    ∀ᵐ sample : ℝ,HasDerivAt (fun t => rootKernel (t-sample))
      (deriv rootKernel (time-sample)) time := by
  have shifted := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae source_derivative
  filter_upwards [shifted] with sample actual
  simpa only [mul_one,Function.comp_def,id_eq] using! actual.comp time ((hasDerivAt_id time).sub_const sample)

theorem source_gram_rate : ∀ᵐ x : ℝ,
    2*rootKernel x*deriv rootKernel x = deriv kernel x := by
  filter_upwards [source_derivative] with x actual
  have both := actual.pow 2
  have same : rootKernel^2=kernel := funext square
  rw [same] at both
  have original : HasDerivAt kernel (deriv kernel x) x :=
    (kernel_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  simpa using both.unique original

theorem shift_quotient_bound : ∃ C : ℝ,0≤C ∧∀ time sample displacement : ℝ,
    ‖displacement⁻¹*(rootKernel (time+displacement-sample)-rootKernel (time-sample))‖≤C := by
  obtain ⟨C,paid⟩ := source_lipschitz
  refine ⟨C,C.coe_nonneg,fun time sample displacement => ?_⟩
  by_cases zero : displacement=0
  · simp [zero]
  have bound := paid.dist_le_mul (time+displacement-sample) (time-sample)
  have sub : time+displacement-sample-(time-sample)=displacement := by ring
  rw [Real.dist_eq,Real.dist_eq,sub] at bound
  rw [norm_mul,norm_inv,Real.norm_eq_abs,Real.norm_eq_abs]
  have scaled := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (abs_nonneg displacement))
  exact scaled.trans_eq (by field_simp)

end
end SaturationMonoid.NavierStokes.NativeWindowKernelHalfDensity
