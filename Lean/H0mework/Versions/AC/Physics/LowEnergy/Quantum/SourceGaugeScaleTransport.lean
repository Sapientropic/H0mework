import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarGaugeScale
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoframeStrongJet
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceMovingJetFlux
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGaugeScaleTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceGaugeRadialPair SourceQuantumScalarOrbitDimensions
open MeasureTheory Filter Set Function
open scoped ContDiff Topology Distributions InnerProductSpace ENNReal
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def scaleEquiv (t : ℝ) : SourceCoordinateSlice ≃L[ℝ] SourceCoordinateSlice :=
  (ContinuousLinearEquiv.refl ℝ Coframe).prodCongr
    ((ContinuousLinearEquiv.refl ℝ scalarSlice).prodCongr
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := coordinateSlice)
        (Units.mk0 (Real.exp t) (Real.exp_ne_zero t))))

theorem scaleEquiv_apply (t : ℝ) (z : SourceCoordinateSlice) :
    scaleEquiv t z=gaugeScale (Real.exp t) z := rfl

theorem scale_chart_iff (r : ℝ) (hr : 0<r) (z : SourceCoordinateSlice) :
    gaugeScale r z∈physicalChart ↔ z∈physicalChart := by
  change (_ ∧ _ ∧ _ ∧ _ ∧ 0<firstGauge (r • (z.2.2 : Gauge)) ∧
    0<secondGauge (r • (z.2.2 : Gauge)) ∧ 0<jacobian (r • (z.2.2 : Gauge))) ↔ _
  rw [map_smul,map_smul,jacobian_scale,abs_of_pos hr]
  simp only [smul_eq_mul,mul_pos_iff_of_pos_left hr,mul_pos_iff_of_pos_left (pow_pos hr 3)]
  rfl

def pullback (t : ℝ) : End where
  toFun f :=
    { toFun := f ∘ scaleEquiv t
      contDiff' := f.contDiff.comp (scaleEquiv t).contDiff
      hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (scaleEquiv t).toHomeomorph
      tsupport_subset' := by
        change tsupport (f ∘ (scaleEquiv t).toHomeomorph) ⊆ _
        rw [tsupport_comp_eq_preimage f (scaleEquiv t).toHomeomorph]
        intro z hz
        exact (scale_chart_iff _ (Real.exp_pos _) z).mp (f.tsupport_subset hz) }
  map_add' f g := by ext z word; rfl
  map_smul' c f := by ext z word; rfl

/-- The exponent 18 is half the actual gauge Jacobian 33+3. -/
def coreFlow (t : ℝ) : End := (Real.exp (18*t) : ℂ) • pullback t

theorem coreFlow_apply (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    coreFlow t f z word=(Real.exp (18*t) : ℂ)*f (gaugeScale (Real.exp t) z) word := rfl

private theorem scale_add (s t : ℝ) (z : SourceCoordinateSlice) :
    gaugeScale (Real.exp t) (gaugeScale (Real.exp s) z)=gaugeScale (Real.exp (s+t)) z := by
  simp only [gaugeScale,Real.exp_add,mul_smul]
  rw [smul_comm]

theorem coreFlow_add (s t : ℝ) (f : QuantumTest) :
    coreFlow s (coreFlow t f)=coreFlow (s+t) f := by
  ext z word
  simp only [coreFlow_apply,scale_add]
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,←mul_add]

theorem coreFlow_zero (f : QuantumTest) : coreFlow 0 f=f := by
  ext z word
  simp only [coreFlow_apply,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,gauge_scale_one]

instance gauge_haar : coordinateGaugeMeasure.IsAddHaarMeasure := by
  unfold coordinateGaugeMeasure
  infer_instance

theorem configuration_scale_map (t : ℝ) :
    Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure=
      ENNReal.ofReal ((Real.exp t)^33)⁻¹ • GaussHistoryHilbert.configurationMeasure := by
  have hg := Measure.map_addHaar_smul coordinateGaugeMeasure (Real.exp_ne_zero t)
  rw [coordinateSlice_finrank,abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos t) 33))] at hg
  have hm := Measure.map_prod_map SourceQuantumScalarHilbert.sliceMeasure coordinateGaugeMeasure
    measurable_id (measurable_const_smul (Real.exp t))
  rw [Measure.map_id,hg,Measure.prod_smul_right] at hm
  have ho := Measure.map_prod_map coframeMeasure
    (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure)
    measurable_id (measurable_id.prodMap (measurable_const_smul (Real.exp t)))
  rw [Measure.map_id,←hm,Measure.prod_smul_right] at ho
  exact ho.symm

private theorem exp_pow (t : ℝ) (n : ℕ) : Real.exp t ^ n=Real.exp ((n : ℝ)*t) := by
  rw [Real.exp_nat_mul]

theorem densityPair_flow (t : ℝ) (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair (coreFlow t f) (coreFlow t g) z=
      ((Real.exp t)^33 : ℝ) • densityPair f g (scaleEquiv t z) := by
  simp only [densityPair_sum,coreFlow_apply,scaleEquiv_apply,Finset.smul_sum,
    GaussDensityCore.complexDensity,density_scale,abs_of_pos (Real.exp_pos t),Complex.ofReal_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro word _
  have h : Real.exp (18*t)^2=Real.exp t^33*Real.exp t^3 := by
    rw [exp_pow,exp_pow,exp_pow,←Real.exp_add]
    congr 1
    norm_num
    ring
  have hc := congrArg Complex.ofReal h
  simp only [Complex.ofReal_pow,Complex.ofReal_mul] at hc
  calc
    _ = ((Real.exp (18*t) : ℂ)^2)*(GaussDensityCore.density word.card z : ℂ)*
        star (f (gaugeScale (Real.exp t) z) word)*g (gaugeScale (Real.exp t) z) word := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hc]; simp only [Complex.ofReal_pow,Complex.star_def]; ring

theorem coreFlow_pair (t : ℝ) (f g : QuantumTest) :
    sourcePair (coreFlow t f) (coreFlow t g)=sourcePair f g := by
  rw [sourcePair_integral,sourcePair_integral]
  simp_rw [densityPair_flow]
  rw [integral_smul]
  have h := (scaleEquiv t).toHomeomorph.measurableEmbedding.integral_map
    (μ := GaussHistoryHilbert.configurationMeasure) (densityPair f g)
  change (∫ y,densityPair f g y ∂Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure)=
    (∫ x,densityPair f g (scaleEquiv t x) ∂GaussHistoryHilbert.configurationMeasure) at h
  rw [configuration_scale_map,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos (Real.exp_pos t) 33).le)] at h
  change (Real.exp t)^33 • (∫ z,densityPair f g (scaleEquiv t z)
    ∂GaussHistoryHilbert.configurationMeasure)=_
  rw [←h,smul_smul,mul_inv_cancel₀ (pow_ne_zero 33 (Real.exp_ne_zero t)),one_smul]

def generator : End := gaugeEulerAction+(18 : ℂ) • 1

theorem generator_apply (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    generator f z word=gaugeEulerAction f z word+18*f z word := rfl

/-- This is a coordinate derivative; strong Hilbert differentiation is paid separately below. -/
theorem coreFlow_generator (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    HasDerivAt (fun t : ℝ => coreFlow t f z word) (generator f z word) 0 := by
  have he : HasDerivAt Real.exp (1 : ℝ) 0 := by simpa only [Real.exp_zero] using Real.hasDerivAt_exp 0
  have hs : HasDerivAt (fun t : ℝ => gaugeScale (Real.exp t) z) (gaugeEuler z) 0 := by
    simpa only [Function.comp_def,one_smul] using! (gauge_scale_derivative z (Real.exp 0)).scomp 0 he
  have hf := ((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := z)
  have hcomp := hf.comp_hasDerivAt_of_eq 0 hs (by simp only [Real.exp_zero,gauge_scale_one])
  have ha : HasDerivAt (fun t : ℝ => (Real.exp (18*t) : ℂ)) (18 : ℂ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (18 : ℝ)).exp)
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa only [id_eq,mul_zero,mul_one,Real.exp_zero,one_mul,
      Complex.ofReal_ofNat,Function.comp_def,Complex.ofRealCLM_apply] using! hc
  have h := ha.mul hcomp
  simp only [Function.comp_def,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,gauge_scale_one] at h
  have hv : (18 : ℂ)*component word f z+fderiv ℝ (component word f) z (gaugeEuler z)=generator f z word := by
    rw [generator_apply,gauge_euler_component]
    exact add_comm _ _
  exact (h.congr_deriv hv).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))

def coreFlowEquiv (t : ℝ) : QuantumTest ≃ₗ[ℂ] QuantumTest where
  __ := coreFlow t
  invFun := coreFlow (-t)
  left_inv f := by
    change coreFlow (-t) (coreFlow t f)=f
    rw [coreFlow_add,neg_add_cancel,coreFlow_zero]
  right_inv f := by
    change coreFlow t (coreFlow (-t) f)=f
    rw [coreFlow_add,add_neg_cancel,coreFlow_zero]

theorem coreFlow_norm (t : ℝ) (f : QuantumTest) : ‖embed (coreFlow t f)‖=‖embed f‖ := by
  have h := congrArg Complex.re (coreFlow_pair t f f)
  change RCLike.re (inner ℂ (embed (coreFlow t f)) (embed (coreFlow t f)))=
    RCLike.re (inner ℂ (embed f) (embed f)) at h
  rw [←norm_sq_eq_re_inner (𝕜 := ℂ),←norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (embed (coreFlow t f)),norm_nonneg (embed f)]

def hilbertFlow (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  (coreFlowEquiv t).extendOfIsometry embed embed SourceCoframeScaleTransport.embed_dense
    SourceCoframeScaleTransport.embed_dense (coreFlow_norm t)

theorem hilbertFlow_on_core (t : ℝ) (f : QuantumTest) :
    hilbertFlow t (embed f)=embed (coreFlow t f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

theorem hilbertFlow_add (s t : ℝ) (f : H) :
    hilbertFlow s (hilbertFlow t f)=hilbertFlow (s+t) f := by
  refine SourceCoframeScaleTransport.embed_dense.induction_on
    (p := fun v : H => hilbertFlow s (hilbertFlow t v)=hilbertFlow (s+t) v) f ?_ ?_
  · exact isClosed_eq ((hilbertFlow s).continuous.comp (hilbertFlow t).continuous)
      (hilbertFlow (s+t)).continuous
  · intro g
    rw [hilbertFlow_on_core,hilbertFlow_on_core,hilbertFlow_on_core,coreFlow_add]

theorem hilbertFlow_zero (f : H) : hilbertFlow 0 f=f := by
  refine SourceCoframeScaleTransport.embed_dense.induction_on (p := fun v : H => hilbertFlow 0 v=v) f ?_ ?_
  · exact isClosed_eq (hilbertFlow 0).continuous continuous_id
  · intro g
    rw [hilbertFlow_on_core,coreFlow_zero]

theorem generator_flow (t : ℝ) (f : QuantumTest) : generator (coreFlow t f)=coreFlow t (generator f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h₁ := coreFlow_generator (coreFlow t f) z word
  have h₂ := (coreFlow_generator f (gaugeScale (Real.exp t) z) word).const_mul
    ((Real.exp (18*t) : ℂ))
  have he : (fun s : ℝ => coreFlow s (coreFlow t f) z word)=
      (fun s : ℝ => (Real.exp (18*t) : ℂ)*coreFlow s f (gaugeScale (Real.exp t) z) word) := by
    funext s
    rw [coreFlow_add,add_comm s t,←coreFlow_add t s f,coreFlow_apply]
  rw [he] at h₁
  exact h₁.unique h₂

theorem component_flow_derivative (f : QuantumTest) (z : SourceCoordinateSlice)
    (word : Occupation) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coreFlow s f z word) (coreFlow t (generator f) z word) t := by
  have h := (coreFlow_generator (coreFlow t f) z word).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  have he : (fun s : ℝ => coreFlow (s-t) (coreFlow t f) z word)=
      (fun s => coreFlow s f z word) := by
    funext s
    rw [coreFlow_add,sub_add_cancel]
  simp only [one_smul,Function.comp_def,id_eq] at h
  rw [he,generator_flow] at h
  exact h

theorem component_flow_continuous (f : QuantumTest) (word : Occupation) :
    Continuous (fun p : ℝ×SourceCoordinateSlice => coreFlow p.1 f p.2 word) := by
  change Continuous (fun p : ℝ×SourceCoordinateSlice =>
    (Real.exp (18*p.1) : ℂ)*f (gaugeScale (Real.exp p.1) p.2) word)
  have hf : Continuous (fun z : SourceCoordinateSlice => f z word) := (component word f).continuous
  have hs : Continuous (fun p : ℝ×SourceCoordinateSlice => gaugeScale (Real.exp p.1) p.2) := by
    unfold gaugeScale
    fun_prop
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (hf.comp hs)

private theorem density_continuous (N : ℕ) : Continuous (GaussDensityCore.complexDensity N) := by
  have hg : Continuous (fun z : SourceCoordinateSlice => (z.2.2 : Gauge)) := by fun_prop
  have hv : Continuous (fun z : SourceCoordinateSlice => z.1 0*z.1 2*z.1 5) := by fun_prop
  exact Complex.continuous_ofReal.comp
    ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))

private def kernel (f g : QuantumTest) (t : ℝ) (z : SourceCoordinateSlice) : ℂ :=
  densityPair f (coreFlow t g) z

private theorem kernel_continuous (f g : QuantumTest) :
    Continuous (fun p : ℝ×SourceCoordinateSlice => kernel f g p.1 p.2) := by
  have he : (fun p : ℝ×SourceCoordinateSlice => kernel f g p.1 p.2)=
      fun p => ∑ word : Occupation, GaussDensityCore.complexDensity word.card p.2*
        star (f p.2 word)*coreFlow p.1 g p.2 word := by
    funext p
    exact densityPair_sum _ _ _
  rw [he]
  apply continuous_finsetSum
  intro word _
  exact (((density_continuous word.card).comp continuous_snd).mul
    (((component word f).continuous.comp continuous_snd).star)).mul (component_flow_continuous g word)

private theorem kernel_derivative (f g : QuantumTest) (z : SourceCoordinateSlice) (t : ℝ) :
    HasDerivAt (fun s => kernel f g s z) (kernel f (generator g) t z) t := by
  have h := HasDerivAt.sum (u := (Finset.univ : Finset Occupation)) (fun word _ =>
    (component_flow_derivative g z word t).const_mul
      (GaussDensityCore.complexDensity word.card z*star (f z word)))
  have he : (fun s => kernel f g s z)=fun s => ∑ word : Occupation,
      GaussDensityCore.complexDensity word.card z*star (f z word)*coreFlow s g z word := by
    funext s
    exact densityPair_sum _ _ _
  rw [he]
  convert! h using 1
  · funext s
    simp only [Finset.sum_apply]
  · exact densityPair_sum _ _ _

private theorem kernel_zero (f g : QuantumTest) (t : ℝ) (z : SourceCoordinateSlice)
    (hz : z∉tsupport f) : kernel f g t z=0 := by
  unfold kernel densityPair
  rw [image_eq_zero_of_notMem_tsupport hz,map_zero,inner_zero_left]

/-- Original compact tests and the actual configuration measure pay differentiation under the integral. -/
theorem weak_flow_derivative (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sourcePair f (coreFlow s g))
      (sourcePair f (coreFlow t (generator g))) t := by
  let F := kernel f g
  let F' := kernel f (generator g)
  have hcont : Continuous (fun p : ℝ×SourceCoordinateSlice => F' p.1 p.2) :=
    kernel_continuous f (generator g)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod f.hasCompactSupport).exists_bound_of_continuousOn
    (hcont.continuousOn : ContinuousOn (fun p : ℝ×SourceCoordinateSlice => F' p.1 p.2)
      (Icc (t-1) (t+1)×ˢtsupport f))
  let bound : SourceCoordinateSlice → ℝ := (tsupport f).indicator (fun _ => C)
  have hbound : Integrable bound GaussHistoryHilbert.configurationMeasure :=
    (integrableOn_const (μ := GaussHistoryHilbert.configurationMeasure) (C := C) f.hasCompactSupport.measure_ne_top).integrable_indicator
      (isClosed_tsupport f).measurableSet
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := GaussHistoryHilbert.configurationMeasure) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (Filter.Eventually.of_forall (fun s => (densityPair_integrable f (coreFlow s g)).aestronglyMeasurable))
    (densityPair_integrable f (coreFlow t g))
    ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => by
      intro s hs
      by_cases hz : z∈tsupport f
      · change ‖F' s z‖≤(tsupport f).indicator (fun _ => C) z
        rw [Set.indicator_of_mem hz]
        exact hC (s,z) ⟨⟨hs.1.le,hs.2.le⟩,hz⟩
      · change ‖kernel f (generator g) s z‖≤(tsupport f).indicator (fun _ => C) z
        rw [kernel_zero f (generator g) s z hz,Set.indicator_of_notMem hz,norm_zero]))
    hbound (Filter.Eventually.of_forall (fun z s _ => kernel_derivative f g z s))
  have he : (fun s => ∫ z,F s z ∂GaussHistoryHilbert.configurationMeasure)=
      fun s => sourcePair f (coreFlow s g) := by
    funext s
    exact (sourcePair_integral f (coreFlow s g)).symm
  rw [he] at hd
  have hvalue : (∫ z,F' t z ∂GaussHistoryHilbert.configurationMeasure)=
      sourcePair f (coreFlow t (generator g)) := (sourcePair_integral _ _).symm
  rw [hvalue] at hd
  exact hd.2

theorem pair_difference_bound (f g : QuantumTest) (s t : ℝ) :
    ‖sourcePair f (coreFlow t g)-sourcePair f (coreFlow s g)‖≤
      (‖embed f‖*‖embed (generator g)‖)*‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (weak_flow_derivative f g u).hasDerivWithinAt)
    (fun u _ => ?_) convex_univ (mem_univ s) (mem_univ t)
  change ‖inner ℂ (embed f) (embed (coreFlow u (generator g)))‖≤_
  exact (norm_inner_le_norm _ _).trans_eq (by rw [coreFlow_norm])

theorem core_difference_bound (f : QuantumTest) (s t : ℝ) :
    ‖embed (coreFlow t f)-embed (coreFlow s f)‖≤‖embed (generator f)‖*‖t-s‖ := by
  let q := coreFlow t f-coreFlow s f
  have h := pair_difference_bound q f s t
  change ‖inner ℂ (embed q) (embed (coreFlow t f))-inner ℂ (embed q) (embed (coreFlow s f))‖≤_ at h
  rw [←inner_sub_right,←map_sub] at h
  change ‖inner ℂ (embed q) (embed q)‖≤(‖embed q‖*‖embed (generator f)‖)*‖t-s‖ at h
  rw [←inner_self_re_eq_norm,inner_self_eq_norm_sq] at h
  have hnonneg : 0≤‖embed (generator f)‖*‖t-s‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hn : ‖embed q‖≤‖embed (generator f)‖*‖t-s‖ := by
    nlinarith [norm_nonneg (embed q)]
  simpa only [q,map_sub] using hn

theorem core_continuous (f : QuantumTest) : Continuous (fun t : ℝ => embed (coreFlow t f)) := by
  have h : LipschitzWith ‖embed (generator f)‖₊ (fun t : ℝ => embed (coreFlow t f)) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [dist_eq_norm,coe_nnnorm] using core_difference_bound f t s
  exact h.continuous

private theorem velocity_continuous (f : QuantumTest) :
    Continuous (fun t : ℝ => embed (coreFlow t (generator f))) := core_continuous (generator f)

theorem core_integral (f : QuantumTest) (t : ℝ) :
    (∫ s in (0 : ℝ)..t,embed (coreFlow s (generator f)))=embed (coreFlow t f)-embed f := by
  apply ext_inner_left ℂ
  intro x
  refine SourceCoframeScaleTransport.embed_dense.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro g
  have hi := (velocity_continuous f).intervalIntegrable (μ := MeasureTheory.volume) 0 t
  have hmap := (innerSL ℂ (embed g)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,inner ℂ (embed g) (embed (coreFlow s (generator f))))=
    inner ℂ (embed g) (∫ s in (0 : ℝ)..t,embed (coreFlow s (generator f))) at hmap
  rw [←hmap,inner_sub_right]
  change (∫ s in (0 : ℝ)..t,sourcePair g (coreFlow s (generator f)))=
    sourcePair g (coreFlow t f)-sourcePair g f
  have hc : Continuous (fun s : ℝ => sourcePair g (coreFlow s (generator f))) :=
    continuous_const.inner (core_continuous (generator f))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => weak_flow_derivative g f s) (hc.intervalIntegrable 0 t)
  simpa only [coreFlow_zero] using! h

theorem strong_core_derivative (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => embed (coreFlow s f)) (embed (coreFlow t (generator f))) t := by
  have hc := velocity_continuous f
  let : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩
  have h := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun s : ℝ => embed (coreFlow s f))=
      fun s => embed f+∫ u in (0 : ℝ)..s,embed (coreFlow u (generator f)) := by
    funext s
    rw [core_integral]
    abel
  rw [he]
  exact h.const_add (embed f)

theorem hilbert_strong_continuous (x : H) : Continuous (fun t : ℝ => hilbertFlow t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨f,hf⟩ := SourceCoframeScaleTransport.embed_dense.exists_dist_lt x (show 0<ε/4 by positivity)
  obtain ⟨δ,hδ,hδt⟩ := Metric.continuousAt_iff.mp (core_continuous f).continuousAt
    (ε/2) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s hs
  have hm : dist (hilbertFlow s (embed f)) (hilbertFlow t (embed f))<ε/2 := by
    rw [hilbertFlow_on_core,hilbertFlow_on_core]
    exact hδt hs
  have h₁ := dist_triangle (hilbertFlow s x) (hilbertFlow s (embed f)) (hilbertFlow t x)
  have h₂ := dist_triangle (hilbertFlow s (embed f)) (hilbertFlow t (embed f)) (hilbertFlow t x)
  rw [(hilbertFlow s).isometry.dist_eq] at h₁
  rw [(hilbertFlow t).isometry.dist_eq,dist_comm (embed f) x] at h₂
  linarith

def strongJet (n : ℕ) (f : QuantumTest) (t : ℝ) : H := embed (coreFlow t ((generator^n) f))

theorem strong_jet_zero (f : QuantumTest) (t : ℝ) : strongJet 0 f t=embed (coreFlow t f) := by
  simp only [strongJet,pow_zero,Module.End.one_apply]

theorem strong_jet_derivative (n : ℕ) (f : QuantumTest) (t : ℝ) :
    HasDerivAt (strongJet n f) (strongJet (n+1) f t) t := by
  have hd : (generator^(n+1)) f=generator ((generator^n) f) := by rw [pow_succ']; rfl
  simpa only [strongJet,hd] using! strong_core_derivative ((generator^n) f) t

theorem strong_jet_norm (n : ℕ) (f : QuantumTest) (t : ℝ) :
    ‖strongJet n f t‖=‖embed ((generator^n) f)‖ := coreFlow_norm _ _

theorem finite_profile_derivative (F : GaussUnitaryHistory.Index) (z : ℂ)
    (n : ℕ) (f : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f s))
      (FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet (n+1) f t)) t := by
  exact ((FullYSourceResolventGraphSplice.finiteResolvent F z).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t (strong_jet_derivative n f t)

theorem finite_profile_bound (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0)
    (n : ℕ) (f : QuantumTest) (t : ℝ) :
    ‖FullYSourceResolventGraphSplice.finiteResolvent F z (strongJet n f t)‖≤
      (1/|z.im|)*‖embed ((generator^n) f)‖ := by
  have h := ((FullYSourceResolventGraphSplice.finiteResolvent F z).le_opNorm (strongJet n f t)).trans
    (mul_le_mul_of_nonneg_right (FullYSourceResolventGraphSplice.finite_resolvent_norm F z hz) (norm_nonneg _))
  simpa only [strong_jet_norm] using! h

/-- The new strong generator is the same actual Core derivation used by GaugeScale10. -/
theorem generator_commutator (A : End) :
    generator*A-A*generator=SourceScalarGaugeScale.deltaGauge A := by
  change (gaugeEulerAction+(18 : ℂ) • 1)*A-A*(gaugeEulerAction+(18 : ℂ) • 1)=
    gaugeEulerAction*A-A*gaugeEulerAction
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  abel

open GaussUnitaryHistory GaussDiagonalHistory SourceActualResolventEnergy SourceJointResidualEnergy
open FullYSourceResolventGraphSplice SourceRetardedIncrement SourceResolventBandLimit
open InnerProductSpace

/-- Every fixed gauge/coframe test jet has the original all-frequency budget, uniformly in F and time. -/
theorem fixed_jet_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f : QuantumTest) (t : ℝ) :
    (∫ w : ℝ, ‖finiteResolvent F (line μ w) (strongJet n f t)‖^2)=
      (Real.pi/μ)*‖embed ((generator^n) f)‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I,strong_jet_norm] using!
    actual_square_integral F μ hμ (strongJet n f t)

abbrev Op := H →L[ℂ] H

private theorem rank_bilinear :
    IsBoundedBilinearMap ℝ (fun p : H×H => rankOne ℂ p.1 p.2) where
  add_left x y z := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,add_apply,smul_add]
  smul_left c x y := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,smul_apply]; exact smul_comm _ _ _
  add_right x y z := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,add_apply,inner_add_left,add_smul]
  smul_right c x y := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,smul_apply]; rw [←algebraMap_smul ℂ c y,inner_smul_real_left,smul_assoc]
  bound := ⟨1,by norm_num,by intro x y; simp⟩

private theorem rank_derivative {f g : ℝ → H} {f' g' : H} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => rankOne ℂ (f t) (g t))
      (rankOne ℂ f' (g s)+rankOne ℂ (f s) g') s := by
  simpa only [IsBoundedBilinearMap.toContinuousLinearMap_apply,add_comm] using!
    (rank_bilinear.toContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => hf) (fun _ => hg))

def rankJet : ℕ → ℕ → ℕ → QuantumTest → QuantumTest → ℝ → Op
  | 0,r,s,f,g,t => rankOne ℂ (strongJet r f t) (strongJet s g t)
  | n+1,r,s,f,g,t => rankJet n (r+1) s f g t+rankJet n r (s+1) f g t

private theorem rank_jet_derivative (n r s : ℕ) (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (rankJet n r s f g) (rankJet (n+1) r s f g t) t := by
  induction n generalizing r s with
  | zero => exact rank_derivative (strong_jet_derivative r f t) (strong_jet_derivative s g t)
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

open SourceMovingJetFlux (eigenTest eigen_test_embed)

private theorem jet_zero_flow (f : QuantumTest) (t : ℝ) :
    strongJet 0 f t=hilbertFlow t (embed f) := by rw [strong_jet_zero,hilbertFlow_on_core]

private theorem conjugate_rank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    U.conjStarAlgEquiv (rankOne ℂ x y)=rankOne ℂ (U x) (U y) := by
  apply ContinuousLinearMap.ext
  intro z
  change U (inner ℂ y (U.symm z) • x)=inner ℂ (U y) z • U x
  rw [map_smul,←U.inner_map_map y (U.symm z),U.apply_symm_apply]

def projectionJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F,rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

def compressionOrbitJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
    rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

/-- The static identity is the entire escape-space resolvent, retained before taking derivatives. -/
def resolventOrbitJet (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  (if n=0 then -z⁻¹ • (1 : Op) else 0)+
  ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
    rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

theorem moving_projection_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (projectionJet F n) (projectionJet F (n+1) t) t := by
  unfold projectionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ => rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t) using 1
  funext s
  simp only [Finset.sum_apply]

theorem moving_compression_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (compressionOrbitJet F n) (compressionOrbitJet F (n+1) t) t := by
  unfold compressionOrbitJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t).const_smul
        (channelValue F (some i) : ℂ)) using 1
  funext s
  simp only [Finset.sum_apply,Pi.smul_apply]

theorem moving_resolvent_derivative (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (resolventOrbitJet F z n) (resolventOrbitJet F z (n+1) t) t := by
  have h := (hasDerivAt_const t (if n=0 then -z⁻¹ • (1 : Op) else 0)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t).const_smul
        (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹)))
  unfold resolventOrbitJet
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,zero_add]
  simp only [zero_add] at h
  convert! h using 1
  funext s
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply]

theorem actual_moving_projection (F : Index) (t : ℝ) :
    projectionJet F 0 t=(hilbertFlow t).conjStarAlgEquiv (supportProjection F) := by
  classical
  rw [supportProjection,(sourceBasis F).starProjection_eq_sum_rankOne,map_sum]
  simp only [projectionJet,rankJet,jet_zero_flow,eigen_test_embed,conjugate_rank]

private theorem compression_spectral (F : Index) :
    GaussGradedCompression.compression F=
      ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.compressionOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,eigen_test_embed] using!
    (SourceMovingJetFlux.compression_orbit_zero F).symm

private theorem resolvent_spectral (F : Index) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z= -z⁻¹ • (1 : Op)+
      ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.resolventOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,eigen_test_embed,if_true] using!
    (SourceMovingJetFlux.resolvent_orbit_zero F z hz).symm

private theorem conjugate_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (c : ι → ℂ) (v : ι → E)
    (hA : A=∑ i,c i • rankOne ℂ (v i) (v i)) :
    (∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_sum]
  simp only [map_smul,conjugate_rank]

private theorem conjugate_affine_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (a : ℂ) (c : ι → ℂ) (v : ι → E)
    (hA : A=a • (1 : E →L[ℂ] E)+∑ i,c i • rankOne ℂ (v i) (v i)) :
    a • (1 : E →L[ℂ] E)+(∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_add,map_smul,map_one,map_sum]
  simp only [map_smul,conjugate_rank]

theorem actual_moving_compression (F : Index) (t : ℝ) :
    compressionOrbitJet F 0 t=(hilbertFlow t).conjStarAlgEquiv (GaussGradedCompression.compression F) := by
  simpa only [compressionOrbitJet,rankJet,jet_zero_flow,eigen_test_embed] using!
    conjugate_spectral (E := H) (hilbertFlow t) (GaussGradedCompression.compression F)
      (fun i : SpectralIndex F => (channelValue F (some i) : ℂ))
      (fun i => (sourceBasis F i : H)) (compression_spectral F)

theorem actual_moving_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    resolventOrbitJet F z 0 t=(hilbertFlow t).conjStarAlgEquiv (finiteResolvent F z) := by
  simpa only [resolventOrbitJet,rankJet,jet_zero_flow,eigen_test_embed,if_true] using!
    conjugate_affine_spectral (E := H) (hilbertFlow t) (finiteResolvent F z) (-z⁻¹)
      (fun i : SpectralIndex F => (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹))
      (fun i => (sourceBasis F i : H)) (resolvent_spectral F z hz)

private theorem conjugate_zero (A : Op) : (hilbertFlow 0).conjStarAlgEquiv A=A := by
  apply ContinuousLinearMap.ext
  intro x
  change hilbertFlow 0 (A ((hilbertFlow 0).symm x))=A x
  have he : (hilbertFlow 0).symm x=x := by
    apply (hilbertFlow 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hilbertFlow_zero]
  rw [he,hilbertFlow_zero]

private theorem compression_zero (F : Index) : compressionOrbitJet F 0 0=GaussGradedCompression.compression F :=
  (actual_moving_compression F 0).trans (conjugate_zero _)

private theorem resolvent_zero (F : Index) (z : ℂ) (hz : z.im≠0) : resolventOrbitJet F z 0 0=finiteResolvent F z :=
  (actual_moving_resolvent F z hz 0).trans (conjugate_zero _)

/-- The complete first projection discrepancy is generated from the actual moving eigenframe. -/
def compressionCorrection (F : Index) : Op := compressionOrbitJet F 1 0-
  SourceJointScaleBudget.sourceCompression F
    (SourceScalarGaugeScale.deltaGauge GaussDiagonalHistory.diagonalAction)

theorem compression_correction_explicit (F : Index) :
    compressionCorrection F=
      (∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        (rankOne ℂ (embed (generator (eigenTest F i))) (sourceBasis F i : H)+
          rankOne ℂ (sourceBasis F i : H) (embed (generator (eigenTest F i)))))-
      SourceJointScaleBudget.sourceCompression F
        (SourceScalarGaugeScale.deltaGauge GaussDiagonalHistory.diagonalAction) := by
  simp only [compressionCorrection,compressionOrbitJet,rankJet,strongJet,Nat.zero_add,pow_one,pow_zero,
    Module.End.one_apply,coreFlow_zero,eigen_test_embed]

private theorem map_inverse_product {R S : Type*} [Ring R] [Ring S]
    [Module ℂ R] [Module ℂ S] [Star R] [Star S]
    (e : R ≃⋆ₐ[ℂ] S) (A B : R) (z : ℂ) (h : (A-z • (1 : R))*B=1) :
    (e A-z • (1 : S))*e B=1 := by
  simpa only [map_mul,map_sub,map_smul,map_one] using congrArg e h

private theorem inverse_product (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    (compressionOrbitJet F 0 t-z • (1 : Op))*resolventOrbitJet F z 0 t=1 := by
  have h := map_inverse_product (R := Op) (S := Op) (hilbertFlow t).conjStarAlgEquiv
    (GaussGradedCompression.compression F) (finiteResolvent F z) z
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [actual_moving_compression,actual_moving_resolvent F z hz] using! h

private theorem solve_inverse_derivative {R : Type*} [Ring R] (r l a u : R)
    (hr : r*l=1) (hd : a*r+l*u=0) : u= -r*a*r := by
  have h := congrArg (fun x : R => r*x) hd
  rw [mul_add,←mul_assoc r l u,hr,one_mul,mul_zero] at h
  exact (eq_neg_of_add_eq_zero_right h).trans (by noncomm_ring)

private theorem inverse_curve_source_flux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℝ → R) (a b l r d : R)
    (hA : HasDerivAt A a 0) (hB : HasDerivAt B b 0)
    (hA0 : A 0=l) (hB0 : B 0=r) (hr : r*l=1) (hp : ∀ t,A t*B t=1) :
    b= -r*d*r-r*(a-d)*r := by
  have hd := hA.mul hB
  have he : (fun t => A t*B t)=fun _ : ℝ => (1 : R) := funext hp
  change HasDerivAt (fun t => A t*B t) _ 0 at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const (0 : ℝ) (1 : R))
  rw [hA0,hB0] at hh
  rw [solve_inverse_derivative r l a b hr hh]
  noncomm_ring

/-- True bounded resolvent derivative, with the source derivative and every moving-projection term retained. -/
theorem actual_resolvent_source_flux (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventOrbitJet F z 1 0=
      -(finiteResolvent F z)*SourceJointScaleBudget.sourceCompression F
        (SourceScalarGaugeScale.deltaGauge GaussDiagonalHistory.diagonalAction)*finiteResolvent F z-
      finiteResolvent F z*compressionCorrection F*finiteResolvent F z := by
  have hc : HasDerivAt (fun t : ℝ => compressionOrbitJet F 0 t-z • (1 : Op))
      (compressionOrbitJet F 1 0) 0 := by
    simpa only [Nat.zero_add] using! (moving_compression_derivative F 0 0).sub_const (z • (1 : Op))
  have h0 : compressionOrbitJet F 0 0-z • (1 : Op)=GaussGradedCompression.compression F-z • (1 : Op) :=
    congrArg (fun A : Op => A-z • (1 : Op)) (compression_zero F)
  have hr : finiteResolvent F z*(GaussGradedCompression.compression F-z • (1 : Op))=1 :=
    resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz
  simpa only [compressionCorrection] using! inverse_curve_source_flux (R := Op)
    (fun t => compressionOrbitJet F 0 t-z • (1 : Op)) (resolventOrbitJet F z 0)
    (compressionOrbitJet F 1 0) (resolventOrbitJet F z 1 0)
    (GaussGradedCompression.compression F-z • (1 : Op)) (finiteResolvent F z)
    (SourceJointScaleBudget.sourceCompression F (SourceScalarGaugeScale.deltaGauge diagonalAction))
    hc (moving_resolvent_derivative F z 0 0) h0 (resolvent_zero F z hz) hr (inverse_product F z hz)

end LowEnergy.SourceGaugeScaleTransport
