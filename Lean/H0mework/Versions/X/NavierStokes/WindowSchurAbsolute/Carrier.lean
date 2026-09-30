import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Source
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCarrier
open Set Filter MeasureTheory
noncomputable section

theorem curve_derivative {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure ℝ}
    (curve : ℝ → Lp E 2 μ) (point : ℝ → ℝ → E)
    (rate : Lp E 2 μ) (pointRate : ℝ → E) (time : ℝ) (bound : ℝ → ℝ)
    (bound_integrable : Integrable (fun lag => bound lag^2) μ)
    (read : ∀ t,curve t=ᵐ[μ] point t)
    (rateRead : rate=ᵐ[μ] pointRate)
    (derivative : ∀ᵐ lag ∂μ,HasDerivAt (fun t => point t lag) (pointRate lag) time)
    (domination : ∀ᶠ d in 𝓝[≠] (0 : ℝ),∀ᵐ lag ∂μ,
      ‖d⁻¹ • (point (time+d) lag-point time lag)-pointRate lag‖ ≤ bound lag) :
    HasDerivAt curve rate time := by
  let error (d lag : ℝ) := d⁻¹ • (point (time+d) lag-point time lag)-pointRate lag
  have measuredPoint (t : ℝ) : AEStronglyMeasurable (point t) μ :=
    (Lp.memLp (curve t)).aestronglyMeasurable.congr (read t)
  have measuredRate : AEStronglyMeasurable pointRate μ :=
    (Lp.memLp rate).aestronglyMeasurable.congr rateRead
  have measured (d : ℝ) : AEStronglyMeasurable (fun lag => ‖error d lag‖^2) μ :=
    (((measuredPoint (time+d)).sub (measuredPoint time)).const_smul d⁻¹ |>.sub measuredRate).norm.pow 2
  have bounded : ∀ᶠ d in 𝓝[≠] (0 : ℝ),∀ᵐ lag ∂μ,‖‖error d lag‖^2‖ ≤ bound lag^2 := by
    filter_upwards [domination] with d source
    filter_upwards [source] with lag paid
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) paid 2
  have convergence := tendsto_integral_filter_of_dominated_convergence
    (fun lag : ℝ => bound lag^2) (Eventually.of_forall measured) bounded bound_integrable (by
      filter_upwards [derivative] with lag actual
      have source := (tendsto_iff_norm_sub_tendsto_zero.mp actual.tendsto_slope_zero).pow 2
      simpa only [error,zero_pow (by decide : (2 : ℕ)≠0)] using! source)
  have identity (d : ℝ) : ‖d⁻¹ • (curve (time+d)-curve time)-rate‖^2=
      ∫ lag,‖error d lag‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (d⁻¹ • (curve (time+d)-curve time)) rate,
      Lp.coeFn_smul d⁻¹ (curve (time+d)-curve time),Lp.coeFn_sub (curve (time+d)) (curve time),
      read (time+d),read time,rateRead] with lag subtract scale difference first last actual
    rw [subtract,Pi.sub_apply,scale,Pi.smul_apply,difference,Pi.sub_apply,first,last,actual]
  have squares : Tendsto (fun d => ‖d⁻¹ • (curve (time+d)-curve time)-rate‖^2)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simp only [identity]
    simpa only [integral_zero] using! convergence
  have normLimit := Real.continuous_sqrt.continuousAt.tendsto.comp squares
  simp only [Function.comp_def,Real.sqrt_sq_eq_abs,@abs_norm (Lp E 2 μ) _,Real.sqrt_zero] at normLimit
  exact (hasDerivAt_iff_tendsto_slope_zero (F := Lp E 2 μ)).mpr (tendsto_iff_norm_sub_tendsto_zero.mpr normLimit)

section Kernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem shifted_memLp (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ)) (t : ℝ) :
    MemLp (fun s => a (t-s)) 2 (volume : Measure ℝ) :=
  aMem.comp_measurePreserving (Measure.measurePreserving_sub_left volume t)

theorem field_memLp (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (raw : ℝ → E) (rawMem : MemLp raw ∞ volume) (t : ℝ) :
    MemLp (fun s => a (t-s) • raw s) 2 volume :=
  rawMem.smul (p := (2 : ℝ≥0∞)) (shifted_memLp a aMem t)

def field (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (raw : ℝ → E) (rawMem : MemLp raw ∞ volume) (t : ℝ) : Lp E 2 (volume : Measure ℝ) :=
  (field_memLp a aMem raw rawMem t).toLp (fun s => a (t-s) • raw s)

theorem field_ae (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (raw : ℝ → E) (rawMem : MemLp raw ∞ volume) (t : ℝ) :
    field a aMem raw rawMem t =ᵐ[volume] fun s => a (t-s) • raw s :=
  (field_memLp a aMem raw rawMem t).coeFn_toLp

theorem field_norm_bound (a : ℝ → ℝ) (aMem : MemLp a 2 (volume : Measure ℝ))
    (raw : ℝ → E) (rawMem : MemLp raw ∞ volume) (t : ℝ) :
    ‖field a aMem raw rawMem t‖ ≤ ‖aMem.toLp a‖*‖rawMem.toLp raw‖ := by
  let kernel:=Lp.compMeasurePreserving (fun s : ℝ => t-s)
    (Measure.measurePreserving_sub_left volume t) (aMem.toLp a)
  let data:=rawMem.toLp raw
  have kernelRead : kernel=ᵐ[volume] fun s => a (t-s) :=
    (shifted_memLp a aMem t).coeFn_toLp
  have same : field a aMem raw rawMem t=(kernel • data : Lp E 2 (volume : Measure ℝ)) := by
    apply Lp.ext
    filter_upwards [field_ae a aMem raw rawMem t,Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) kernel data,
      kernelRead,rawMem.coeFn_toLp] with s original multiplied first last
    rw [original,multiplied]
    change a (t-s) • raw s=kernel s • data s
    rw [first,last]
  rw [same]
  have paid:=Lp.norm_smul_le (r := (2 : ℝ≥0∞)) kernel data
  have normed:‖kernel‖=‖aMem.toLp a‖:=Lp.norm_compMeasurePreserving _ _
  exact paid.trans_eq (congrArg (fun x : ℝ => x*‖data‖) normed)

private theorem field_domination (a a' : ℝ → ℝ) (C B : ℝ) (C0 : 0 ≤ C)
    (slopes : ∀ t s d : ℝ,‖d⁻¹*(a (t+d-s)-a (t-s))‖ ≤ C)
    (bound : ∀ x,‖a' x‖ ≤ C)
    (supported : ∀ x,x∉Icc (-2:ℝ) (-1) → a x=0)
    (rateSupported : ∀ x,x∉Icc (-2:ℝ) (-1) → a' x=0)
    (raw : ℝ → E) (rawBound : ∀ x,‖raw x‖ ≤ B) (t d s : ℝ) (small : |d| < 1) :
    ‖d⁻¹ • (a (t+d-s) • raw s-a (t-s) • raw s)-a' (t-s) • raw s‖ ≤
      (Icc t (t+3)).indicator (fun _ => 2*C*B) s := by
  classical
  by_cases inside:s∈Icc t (t+3)
  · rw [Set.indicator_of_mem inside,← sub_smul,smul_smul,← sub_smul,norm_smul]
    have scalar : ‖d⁻¹*(a (t+d-s)-a (t-s))-a' (t-s)‖ ≤ 2*C := by
      have triangle:=norm_sub_le (d⁻¹*(a (t+d-s)-a (t-s))) (a' (t-s))
      linarith only [triangle,slopes t s d,bound (t-s)]
    exact mul_le_mul scalar (rawBound s) (norm_nonneg _) (mul_nonneg (by norm_num) C0)
  · have old:t-s∉Icc (-2:ℝ) (-1) := by
      intro member
      apply inside
      constructor <;> linarith [member.1,member.2]
    have shifted:t+d-s∉Icc (-2:ℝ) (-1) := by
      intro member
      have ds: -1 < d ∧ d < 1:=abs_lt.mp small
      apply inside
      constructor <;> linarith [member.1,member.2,ds.1,ds.2]
    simp only [Set.indicator_of_notMem inside,supported _ old,supported _ shifted,
      rateSupported _ old,zero_smul,sub_self,smul_zero,norm_zero,le_refl]

theorem field_hasDerivAt (a a' : ℝ → ℝ)
    (aMem : MemLp a 2 (volume : Measure ℝ)) (rateMem : MemLp a' 2 (volume : Measure ℝ))
    (derivative : ∀ t : ℝ,∀ᵐ s : ℝ,HasDerivAt (fun r => a (r-s)) (a' (t-s)) t)
    (C : ℝ) (C0 : 0 ≤ C)
    (slopes : ∀ t s d : ℝ,‖d⁻¹*(a (t+d-s)-a (t-s))‖ ≤ C)
    (cap : ∀ x,‖a' x‖ ≤ C)
    (supported : ∀ x,x∉Icc (-2:ℝ) (-1) → a x=0)
    (rateSupported : ∀ x,x∉Icc (-2:ℝ) (-1) → a' x=0)
    (raw : ℝ → E) (rawMem : MemLp raw ∞ volume) (B : ℝ)
    (rawBound : ∀ x,‖raw x‖ ≤ B) (t : ℝ) :
    HasDerivAt (field a aMem raw rawMem)
      (field a' rateMem raw rawMem t) t := by
  let bound : ℝ → ℝ:=(Icc t (t+3)).indicator (fun _ => 2*C*B)
  have integrable : Integrable (fun s => bound s^2) (volume : Measure ℝ) := by
    have constant : IntegrableOn (fun _ : ℝ => (2*C*B)^2) (Icc t (t+3)) volume :=
      integrableOn_const (measure_Icc_lt_top.ne)
    have source : Integrable ((Icc t (t+3)).indicator (fun _ : ℝ => (2*C*B)^2)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr constant
    apply source.congr
    exact Eventually.of_forall fun s => by
      classical
      by_cases member:s∈Icc t (t+3) <;> simp [bound,Set.indicator,member]
  apply curve_derivative (μ := (volume : Measure ℝ))
    (field a aMem raw rawMem) (fun r s => a (r-s) • raw s)
    (field a' rateMem raw rawMem t) (fun s => a' (t-s) • raw s)
    t bound integrable (field_ae a aMem raw rawMem)
    (field_ae a' rateMem raw rawMem t)
  · exact (derivative t).mono fun s actual => actual.smul_const (raw s)
  · have near : ∀ᶠ d in 𝓝[≠] (0:ℝ),|d| < 1 :=
      (show ∀ᶠ d in 𝓝 (0:ℝ),|d| < 1 from
        ((continuous_abs.continuousAt.tendsto).eventually (gt_mem_nhds (by norm_num)))).filter_mono nhdsWithin_le_nhds
    filter_upwards [near] with d small
    exact Eventually.of_forall fun s =>
      field_domination a a' C B C0 slopes cap supported rateSupported raw rawBound t d s small

end Kernel
end
end SaturationMonoid.NavierStokes.NativeWindowAbsoluteTimeCarrier
