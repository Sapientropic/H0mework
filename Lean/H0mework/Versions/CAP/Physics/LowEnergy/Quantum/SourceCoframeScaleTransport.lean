import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScaleJetWard
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Operator.Extend

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceCoframeScaleTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent
open MeasureTheory Set Function
open scoped ContDiff Topology Distributions InnerProductSpace ENNReal

def rate (t : ℝ) : ℝ := Real.exp ((2/3 : ℝ)*t)

def scaleEquiv (t : ℝ) : SourceCoordinateSlice ≃L[ℝ] SourceCoordinateSlice :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Coframe) (Units.mk0 (rate t) (Real.exp_ne_zero _))).prodCongr
    (ContinuousLinearEquiv.refl ℝ _)

theorem scaleEquiv_apply (t : ℝ) (z : SourceCoordinateSlice) :
    scaleEquiv t z = scale (rate t) z := rfl

theorem scale_chart_iff (r : ℝ) (hr : 0 < r) (z : SourceCoordinateSlice) :
    scale r z ∈ physicalChart ↔ z ∈ physicalChart := by
  change (0 < r*z.1 0 ∧ 0 < r*z.1 2 ∧ 0 < r*z.1 5 ∧ _) ↔ _
  simp only [mul_pos_iff_of_pos_left hr]
  rfl

def pullback (t : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest where
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

def fiberAmplitude (t : ℝ) : FockFiber →ₗ[ℂ] FockFiber where
  toFun f := WithLp.toLp 2 (fun word => (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*f word)
  map_add' f g := by ext word; exact mul_add _ _ _
  map_smul' c f := by
    ext word
    change (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*(c*f word)=c*((Real.exp ((word.card+4 : ℝ)*t) : ℂ)*f word)
    ring

def coreFlow (t : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (TestFunction.postcompCLM (fiberAmplitude t).toContinuousLinearMap).toLinearMap.comp (pullback t)

theorem coreFlow_apply (t : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) (word : Occupation) :
    coreFlow t f z word = (Real.exp ((word.card+4 : ℝ)*t) : ℂ)*f (scale (rate t) z) word := rfl

theorem scale_add (s t : ℝ) (z : SourceCoordinateSlice) :
    scale (rate s) (scale (rate t) z) = scale (rate (s+t)) z := by
  have h : rate (s+t)=rate s*rate t := by unfold rate; rw [mul_add,Real.exp_add]
  simp only [scale,h,mul_smul]

theorem coreFlow_add (s t : ℝ) (f : QuantumTest) :
    coreFlow s (coreFlow t f)=coreFlow (s+t) f := by
  ext z word
  simp only [coreFlow_apply,scale_add]
  rw [←mul_assoc,←Complex.ofReal_mul,←Real.exp_add,←mul_add]
  rw [add_comm t s]

theorem coreFlow_zero (f : QuantumTest) : coreFlow 0 f=f := by
  ext z word
  simp [coreFlow_apply,rate,scale]

instance coframe_haar : coframeMeasure.IsAddHaarMeasure := by
  unfold coframeMeasure
  infer_instance

theorem configuration_scale_map (t : ℝ) :
    Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure =
      ENNReal.ofReal ((rate t)^6)⁻¹ • GaussHistoryHilbert.configurationMeasure := by
  have hd : Module.finrank ℝ Coframe = 6 := by simp [Coframe]
  have hc := Measure.map_addHaar_smul coframeMeasure (Real.exp_ne_zero ((2/3 : ℝ)*t))
  rw [hd,abs_of_pos (inv_pos.mpr (pow_pos (Real.exp_pos _) 6))] at hc
  have hm := Measure.map_prod_map coframeMeasure
    (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure)
    (measurable_const_smul (rate t)) measurable_id
  change Measure.map (fun x : Coframe => rate t • x) coframeMeasure =
    ENNReal.ofReal ((rate t)^6)⁻¹ • coframeMeasure at hc
  rw [Measure.map_id,hc,Measure.prod_smul_left] at hm
  change Measure.map (fun z : SourceCoordinateSlice => (rate t • z.1,z.2))
    (coframeMeasure.prod (SourceQuantumScalarHilbert.sliceMeasure.prod coordinateGaugeMeasure)) = _
  exact hm.symm

theorem coreFlow_generator (f : QuantumTest) (z : physicalChart) (word : Occupation) :
    HasDerivAt (fun t : ℝ => coreFlow t f z.val word)
      (Complex.I*dilation f z.val word) 0 := by
  have hr : HasDerivAt rate (2/3 : ℝ) 0 := by
    simpa only [rate,id_eq,mul_zero,Real.exp_zero,one_mul,mul_one] using! (((hasDerivAt_id (0 : ℝ)).const_mul (2/3 : ℝ)).exp)
  have hscale : HasDerivAt (fun t : ℝ => scale (rate t) z.val)
      ((2/3 : ℝ) • euler z.val) 0 := by
    simpa [scale,euler,smul_smul] using (hr.smul_const z.val.1).prodMk
      (hasDerivAt_const (0 : ℝ) z.val.2)
  have hf := ((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x := z.val)
  have hcomp := hf.comp_hasDerivAt_of_eq 0 hscale (by simp [scale,rate])
  have ha : HasDerivAt (fun t : ℝ => (Real.exp ((word.card+4 : ℝ)*t) : ℂ))
      (word.card+4 : ℂ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).const_mul (word.card+4 : ℝ)).exp)
    have hc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
    simpa only [id_eq,mul_zero,mul_one,Real.exp_zero,one_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_ofNat,Function.comp_def,Complex.ofRealCLM_apply] using! hc
  have h := ha.mul hcomp
  convert! h using 1
  rw [dilation_apply]
  simp [Function.comp_def,component,rate,scale,map_smul,Complex.real_smul]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem rate_pow (t : ℝ) (n : ℕ) : rate t ^ n = Real.exp ((n : ℝ)*(2/3 : ℝ)*t) := by
  unfold rate
  rw [←Real.exp_nat_mul]
  congr 1
  ring

theorem densityPair_flow (t : ℝ) (f g : QuantumTest) (z : SourceCoordinateSlice) :
    densityPair (coreFlow t f) (coreFlow t g) z =
      (rate t ^ 6 : ℝ) • densityPair f g (scaleEquiv t z) := by
  simp only [densityPair_sum,coreFlow_apply,scaleEquiv_apply,Finset.smul_sum,
    GaussDensityCore.complexDensity,density_scale,Complex.ofReal_mul,
    star_mul,Complex.star_def,Complex.conj_ofReal,Complex.real_smul]
  apply Finset.sum_congr rfl
  intro word _
  have h : (Real.exp ((word.card+4 : ℝ)*t))^2 =
      (rate t)^6*(rate t)^(3*(word.card+2)) := by
    rw [←Real.exp_nat_mul,rate_pow,rate_pow,←Real.exp_add]
    congr 1
    push_cast
    ring
  have hc := congrArg Complex.ofReal h
  simp only [Complex.ofReal_pow,Complex.ofReal_mul] at hc
  calc
    _ = ((Real.exp ((word.card+4 : ℝ)*t) : ℂ)^2)*
        (GaussDensityCore.density word.card z : ℂ)*star (f (scale (rate t) z) word)*
          g (scale (rate t) z) word := by simp only [Complex.star_def]; ring
    _ = _ := by rw [hc]; simp only [Complex.ofReal_pow,Complex.star_def]; ring

theorem coreFlow_pair (t : ℝ) (f g : QuantumTest) :
    sourcePair (coreFlow t f) (coreFlow t g)=sourcePair f g := by
  rw [sourcePair_integral,sourcePair_integral]
  simp_rw [densityPair_flow]
  rw [integral_smul]
  have h := (scaleEquiv t).toHomeomorph.measurableEmbedding.integral_map
    (μ := GaussHistoryHilbert.configurationMeasure) (densityPair f g)
  change (∫ y, densityPair f g y ∂Measure.map (scaleEquiv t) GaussHistoryHilbert.configurationMeasure) =
    (∫ x, densityPair f g (scaleEquiv t x) ∂GaussHistoryHilbert.configurationMeasure) at h
  have hp : 0 < rate t := Real.exp_pos _
  rw [configuration_scale_map,integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hp 6).le)] at h
  change (rate t)^6 • (∫ z, densityPair f g (scaleEquiv t z)
    ∂GaussHistoryHilbert.configurationMeasure) = _
  rw [←h,smul_smul,mul_inv_cancel₀ (pow_ne_zero 6 hp.ne'),one_smul]

def coreFlowEquiv (t : ℝ) : QuantumTest ≃ₗ[ℂ] QuantumTest where
  __ := coreFlow t
  invFun := coreFlow (-t)
  left_inv f := by
    change coreFlow (-t) (coreFlow t f)=f
    rw [coreFlow_add,neg_add_cancel,coreFlow_zero]
  right_inv f := by
    change coreFlow t (coreFlow (-t) f)=f
    rw [coreFlow_add,add_neg_cancel,coreFlow_zero]

theorem embed_dense : DenseRange embed := by
  have he : Set.range embed = (Core : Set H) := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      exact embed_mem_core g
    · intro h
      exact embed_surjective_core ⟨f,h⟩
  rw [DenseRange,he]
  exact fockTestDomain_dense

theorem coreFlow_norm (t : ℝ) (f : QuantumTest) : ‖embed (coreFlow t f)‖ = ‖embed f‖ := by
  have h := congrArg Complex.re (coreFlow_pair t f f)
  change (inner ℂ (embed (coreFlow t f)) (embed (coreFlow t f))).re =
    (inner ℂ (embed f) (embed f)).re at h
  change RCLike.re (inner ℂ (embed (coreFlow t f)) (embed (coreFlow t f))) =
    RCLike.re (inner ℂ (embed f) (embed f)) at h
  rw [←norm_sq_eq_re_inner (𝕜 := ℂ),←norm_sq_eq_re_inner (𝕜 := ℂ)] at h
  nlinarith [norm_nonneg (embed (coreFlow t f)),norm_nonneg (embed f)]

def hilbertFlow (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  (coreFlowEquiv t).extendOfIsometry embed embed embed_dense embed_dense (coreFlow_norm t)

theorem hilbertFlow_on_core (t : ℝ) (f : QuantumTest) :
    hilbertFlow t (embed f)=embed (coreFlow t f) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

theorem hilbertFlow_add (s t : ℝ) (f : H) :
    hilbertFlow s (hilbertFlow t f)=hilbertFlow (s+t) f := by
  refine embed_dense.induction_on (p := fun v : H => hilbertFlow s (hilbertFlow t v)=hilbertFlow (s+t) v) f ?_ ?_
  · exact isClosed_eq ((hilbertFlow s).continuous.comp (hilbertFlow t).continuous)
      (hilbertFlow (s+t)).continuous
  · intro g
    rw [hilbertFlow_on_core,hilbertFlow_on_core,hilbertFlow_on_core,coreFlow_add]

theorem hilbertFlow_zero (f : H) : hilbertFlow 0 f=f := by
  refine embed_dense.induction_on (p := fun v : H => hilbertFlow 0 v=v) f ?_ ?_
  · exact isClosed_eq (hilbertFlow 0).continuous continuous_id
  · intro g
    rw [hilbertFlow_on_core,coreFlow_zero]

end LowEnergy.SourceCoframeScaleTransport
