import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarVirialBulk
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceGaugeScaleTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarAffineScaleTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarOrbitDimensions SourceScalarFlatJoint
open MeasureTheory Filter Set Function
open scoped ContDiff Topology Distributions InnerProductSpace ENNReal
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev vacuumSlice := SourceScalarVirialBulk.vacuumSlice
abbrev phiEuler := SourceScalarVirialBulk.phiEuler
abbrev phiEulerAction := SourceScalarVirialBulk.phiEulerAction

def scalarEquiv (t : ℝ) : scalarSlice ≃ₜ scalarSlice where
  toFun q := Real.exp t • (q+vacuumSlice)-vacuumSlice
  invFun q := Real.exp (-t) • (q+vacuumSlice)-vacuumSlice
  left_inv q := by
    simp only [sub_add_cancel,smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,
      one_smul,add_sub_cancel_right]
  right_inv q := by
    simp only [sub_add_cancel,smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,
      one_smul,add_sub_cancel_right]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def scaleEquiv (t : ℝ) : SourceCoordinateSlice ≃ₜ SourceCoordinateSlice :=
  (Homeomorph.refl Coframe).prodCongr ((scalarEquiv t).prodCongr (Homeomorph.refl coordinateSlice))

theorem scaleEquiv_apply (t : ℝ) (z : SourceCoordinateSlice) :
    scaleEquiv t z=(z.1,Real.exp t • (z.2.1+vacuumSlice)-vacuumSlice,z.2.2) := rfl

private theorem scalar_chart_scale (t : ℝ) (q : scalarSlice) :
    scalarEquiv t q∈scalarChart ↔ q∈scalarChart := by
  have hp : vacuum+((scalarEquiv t q : scalarSlice) : Scalar)=Real.exp t • (vacuum+(q : Scalar)) := by
    change vacuum+(Real.exp t • ((q : Scalar)+vacuum)-vacuum)=_
    module
  have hm := congrArg ContinuousLinearMap.toLinearMap
    (map_smul consistencyFamily (Real.exp t) (vacuum+(q : Scalar)))
  change consistency (Real.exp t • (vacuum+(q : Scalar)))=
    Real.exp t • consistency (vacuum+(q : Scalar)) at hm
  change (consistency (vacuum+((scalarEquiv t q : scalarSlice) : Scalar))).det≠0 ↔ _
  rw [hp,hm,LinearMap.det_smul]
  change (Real.exp t ^ Module.finrank ℝ broken * (consistency (vacuum+(q : Scalar))).det)≠0 ↔
    (consistency (vacuum+(q : Scalar))).det≠0
  constructor
  · exact fun h => (mul_ne_zero_iff.mp h).2
  · exact fun h => mul_ne_zero (pow_ne_zero _ (Real.exp_ne_zero t)) h

theorem scale_chart_iff (t : ℝ) (z : SourceCoordinateSlice) :
    scaleEquiv t z∈physicalChart ↔ z∈physicalChart := by
  change (_ ∧ _ ∧ _ ∧ scalarEquiv t z.2.1∈scalarChart ∧ _ ∧ _ ∧ _) ↔ _
  rw [scalar_chart_scale]
  rfl

private theorem scale_contDiff (t : ℝ) : ContDiff ℝ ∞ (scaleEquiv t) := by
  change ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    (z.1,Real.exp t • (z.2.1+vacuumSlice)-vacuumSlice,z.2.2))
  fun_prop

def pullback (t : ℝ) : End where
  toFun f :=
    { toFun := f ∘ scaleEquiv t
      contDiff' := f.contDiff.comp (scale_contDiff t)
      hasCompactSupport' := f.hasCompactSupport.comp_homeomorph (scaleEquiv t)
      tsupport_subset' := by
        change tsupport (f ∘ scaleEquiv t) ⊆ _
        rw [tsupport_comp_eq_preimage f (scaleEquiv t)]
        intro z hz
        exact (scale_chart_iff t z).mp (f.tsupport_subset hz) }
  map_add' f g := by ext z word; rfl
  map_smul' c f := by ext z word; rfl

/-- The scalar density is unchanged; the actual scalar61 Haar fixes the half exponent. -/
def coreFlow (t : ℝ) : End := (Real.exp ((61/2 : ℝ)*t) : ℂ) • pullback t

theorem coreFlow_apply (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    coreFlow t f z word=(Real.exp ((61/2 : ℝ)*t) : ℂ)*f (scaleEquiv t z) word := rfl

private theorem scale_add (s t : ℝ) (z : SourceCoordinateSlice) :
    scaleEquiv t (scaleEquiv s z)=scaleEquiv (s+t) z := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change Real.exp t • ((Real.exp s • (z.2.1+vacuumSlice)-vacuumSlice)+vacuumSlice)-vacuumSlice=_
      rw [sub_add_cancel,smul_smul,←Real.exp_add,add_comm t s]
      rfl
    · rfl

private theorem scale_zero (z : SourceCoordinateSlice) : scaleEquiv 0 z=z := by
  simp only [scaleEquiv_apply,Real.exp_zero,one_smul,add_sub_cancel_right]

theorem coreFlow_add (s t : ℝ) (f : QuantumTest) : coreFlow s (coreFlow t f)=coreFlow (s+t) f := by
  ext z word
  simp only [coreFlow_apply,scale_add]
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,←mul_add]

theorem coreFlow_zero (f : QuantumTest) : coreFlow 0 f=f := by
  ext z word
  simp only [coreFlow_apply,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,scale_zero]

instance scalar_haar : SourceQuantumScalarHilbert.sliceMeasure.IsAddHaarMeasure := by
  unfold SourceQuantumScalarHilbert.sliceMeasure
  infer_instance

private theorem scalar_scale_map (t : ℝ) :
    Measure.map (scalarEquiv t) SourceQuantumScalarHilbert.sliceMeasure=
      ENNReal.ofReal ((Real.exp t)^61)⁻¹ • SourceQuantumScalarHilbert.sliceMeasure := by
  let μ := SourceQuantumScalarHilbert.sliceMeasure
  have hs := Measure.map_addHaar_smul μ (Real.exp_ne_zero t)
  rw [scalarSlice_finrank,abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos t) 61))] at hs
  have ha : Measurable (fun q : scalarSlice => q+(-vacuumSlice)) := by fun_prop
  have hb : Measurable (fun q : scalarSlice => Real.exp t • q) := by fun_prop
  have hv : Measurable (fun q : scalarSlice => q+vacuumSlice) := by fun_prop
  calc
    _ = Measure.map (fun q : scalarSlice => q+(-vacuumSlice))
      (Measure.map (fun q : scalarSlice => Real.exp t • q) (Measure.map (fun q : scalarSlice => q+vacuumSlice) μ)) := by
      rw [Measure.map_map ha hb,Measure.map_map (ha.comp hb) hv]
      rfl
    _ = _ := by
      rw [map_add_right_eq_self μ vacuumSlice,hs,Measure.map_smul,map_add_right_eq_self μ (-vacuumSlice)]

theorem configuration_scale_map (t : ℝ) :
    Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure=
      ENNReal.ofReal ((Real.exp t)^61)⁻¹ • GaussHistoryHilbert.configurationMeasure := by
  have hm := Measure.map_prod_map SourceQuantumScalarHilbert.sliceMeasure coordinateGaugeMeasure
    (scalarEquiv t).measurable measurable_id
  rw [scalar_scale_map,Measure.map_id,Measure.prod_smul_left] at hm
  have ho := Measure.map_prod_map coframeMeasure
    (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure)
    measurable_id ((scalarEquiv t).measurable.prodMap measurable_id)
  rw [Measure.map_id,←hm,Measure.prod_smul_right] at ho
  exact ho.symm

private theorem exp_pow (t : ℝ) (n : ℕ) : Real.exp t ^ n=Real.exp ((n : ℝ)*t) := by
  rw [Real.exp_nat_mul]

private theorem density_scale (N : ℕ) (t : ℝ) (z : SourceCoordinateSlice) :
    GaussDensityCore.complexDensity N (scaleEquiv t z)=GaussDensityCore.complexDensity N z := rfl

theorem densityPair_flow (t : ℝ) (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair (coreFlow t f) (coreFlow t g) z=
      ((Real.exp t)^61 : ℝ) • densityPair f g (scaleEquiv t z) := by
  simp only [densityPair_sum,coreFlow_apply,Finset.smul_sum,density_scale,
    Complex.real_smul,star_mul,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro word _
  have h : Real.exp ((61/2 : ℝ)*t)^2=Real.exp t^61 := by
    rw [exp_pow,exp_pow]
    congr 1
    norm_num
    ring
  have hc := congrArg Complex.ofReal h
  simp only [Complex.ofReal_pow] at hc
  calc
    _ = ((Real.exp ((61/2 : ℝ)*t) : ℂ)^2)*GaussDensityCore.complexDensity word.card z*
        star (f (scaleEquiv t z) word)*g (scaleEquiv t z) word := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hc];simp only [Complex.ofReal_pow,Complex.star_def];ring

theorem coreFlow_pair (t : ℝ) (f g : QuantumTest) : sourcePair (coreFlow t f) (coreFlow t g)=sourcePair f g := by
  rw [sourcePair_integral,sourcePair_integral]
  simp_rw [densityPair_flow]
  rw [integral_smul]
  have h := (scaleEquiv t).measurableEmbedding.integral_map
    (μ := GaussHistoryHilbert.configurationMeasure) (densityPair f g)
  change (∫ y,densityPair f g y ∂Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure)=
    (∫ x,densityPair f g (scaleEquiv t x) ∂GaussHistoryHilbert.configurationMeasure) at h
  rw [configuration_scale_map,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos (Real.exp_pos t) 61).le)] at h
  change (Real.exp t)^61 • (∫ z,densityPair f g (scaleEquiv t z) ∂GaussHistoryHilbert.configurationMeasure)=_
  rw [←h,smul_smul,mul_inv_cancel₀ (pow_ne_zero 61 (Real.exp_ne_zero t)),one_smul]

def generator : End := phiEulerAction+(61/2 : ℂ) • 1

theorem generator_apply (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    generator f z word=phiEulerAction f z word+(61/2)*f z word := rfl

private theorem phi_component (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    phiEulerAction f z word=fderiv ℝ (component word f) z (phiEuler z) := by
  have h := congrArg (fun g : GaussDensityCore.ScalarTest => g z)
    (GaussCoframeCore.component_derivative (phiEuler z) f word)
  change GaussCoframeCore.derivative (phiEuler z) f z word=
    GaussDensityCore.derivative (phiEuler z) (component word f) z at h
  simp only [GaussCoframeCore.derivative_apply,GaussDensityCore.derivative_apply] at h
  exact (congrArg (fun v : FockFiber => v word) (SourceScalarVirialBulk.phi_euler_apply f z)).trans h

theorem coreFlow_generator (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    HasDerivAt (fun t : ℝ => coreFlow t f z word) (generator f z word) 0 := by
  have hs : HasDerivAt (fun t : ℝ => scaleEquiv t z) (phiEuler z) 0 := by
    change HasDerivAt (fun t : ℝ =>
      (z.1,Real.exp t • (z.2.1+vacuumSlice)-vacuumSlice,z.2.2)) (0,vacuumSlice+z.2.1,0) 0
    simpa only [Real.exp_zero,one_smul,add_comm] using!
      (hasDerivAt_const (0 : ℝ) z.1).prodMk
        ((((Real.hasDerivAt_exp 0).smul_const (z.2.1+vacuumSlice)).sub_const vacuumSlice).prodMk
          (hasDerivAt_const (0 : ℝ) z.2.2))
  have hf := ((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have hcomp := hf.comp_hasDerivAt_of_eq 0 hs (scale_zero z).symm
  have ha : HasDerivAt (fun t : ℝ => (Real.exp ((61/2 : ℝ)*t) : ℂ)) (61/2 : ℂ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (61/2 : ℝ)).exp)
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa only [id_eq,mul_zero,mul_one,Real.exp_zero,one_mul,Complex.ofReal_div,
      Complex.ofReal_ofNat,Function.comp_def,Complex.ofRealCLM_apply] using! hc
  have h := ha.mul hcomp
  simp only [Function.comp_def,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,scale_zero] at h
  have hv : (61/2 : ℂ)*component word f z+fderiv ℝ (component word f) z (phiEuler z)=generator f z word := by
    rw [generator_apply,phi_component]
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
  have h₂ := (coreFlow_generator f (scaleEquiv t z) word).const_mul
    ((Real.exp ((61/2 : ℝ)*t) : ℂ))
  have he : (fun s : ℝ => coreFlow s (coreFlow t f) z word)=
      (fun s : ℝ => (Real.exp ((61/2 : ℝ)*t) : ℂ)*coreFlow s f (scaleEquiv t z) word) := by
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
    (Real.exp ((61/2 : ℝ)*p.1) : ℂ)*f (scaleEquiv p.1 p.2) word)
  have hf : Continuous (fun z : SourceCoordinateSlice => f z word) := (component word f).continuous
  have hs : Continuous (fun p : ℝ×SourceCoordinateSlice => scaleEquiv p.1 p.2) := by
    simp only [scaleEquiv_apply]
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

/-- The strong generator returns the same original affine-scalar derivation used by the full source virial. -/
theorem generator_commutator (A : End) :
    generator*A-A*generator=SourceScalarVirialBulk.deltaPhi A := by
  change (phiEulerAction+(61/2 : ℂ) • 1)*A-A*(phiEulerAction+(61/2 : ℂ) • 1)=
    phiEulerAction*A-A*phiEulerAction
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  abel

open GaussUnitaryHistory GaussDiagonalHistory SourceActualResolventEnergy SourceJointResidualEnergy
open FullYSourceResolventGraphSplice SourceRetardedIncrement SourceResolventBandLimit
open InnerProductSpace

/-- Every fixed affine-scalar source jet has the original all-frequency budget, uniformly in F and time. -/
theorem fixed_jet_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (n : ℕ) (f : QuantumTest) (t : ℝ) :
    (∫ w : ℝ, ‖finiteResolvent F (line μ w) (strongJet n f t)‖^2)=
      (Real.pi/μ)*‖embed ((generator^n) f)‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I,strong_jet_norm] using!
    actual_square_integral F μ hμ (strongJet n f t)


end LowEnergy.SourceScalarAffineScaleTransport
