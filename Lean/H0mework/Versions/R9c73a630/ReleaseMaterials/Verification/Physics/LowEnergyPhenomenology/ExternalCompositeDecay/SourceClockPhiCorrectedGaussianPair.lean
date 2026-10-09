import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatLocalNativeGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileLocalNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCorrectedGaussianPair
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore ClockPhiConservativeHeatSource
open SourceClockPhiHeatHamiltonianCoefficient SourceClockPhiHeatLocalNativeGaussian
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatCovariancePhase
open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=gaussianReal 0 1
private abbrev config:=GaussHistoryHilbert.configurationMeasure
private def profile(t p q ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  (forwardRatio t z)^p*Real.exp (q*correctedCoefficient t ξ η z)
abbrev correctedProfileWeight(t:ℝ)(ht:0<t)(p q ξ η:ℝ):Op:=
  SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht
    (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) p q

private theorem density_multiply(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (f h:QuantumTest)(z:SourceCoordinateSlice):densityPair f (multiply b hb h) z=(b z:ℂ)*densityPair f h z:=by
  rw [densityPair_sum,densityPair_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _*star (f z word)*((b z:ℂ)*h z word)=_
  ring
private theorem density_offchart(f h:QuantumTest)(z:SourceCoordinateSlice)(hz:z∉physicalChart):densityPair f h z=0:=by
  have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun hx=>hz (f.tsupport_subset hx))
  simp only [densityPair,hf,map_zero,inner_zero_left]
private theorem log_measurable:Measurable Real.log:=
  measurable_of_continuousOn_compl_singleton 0 (fun x hx=>
    (Real.continuousAt_log (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hx)).continuousWithinAt)
private theorem power_measurable(p:ℝ):Measurable (fun x:ℝ=>x^p):=
  measurable_of_continuousOn_compl_singleton 0 (fun x hx=>
    (Real.continuousAt_rpow_const x p (.inl (by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hx))).continuousWithinAt)
private def angleGood(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  if 0<heatLog t z then clockPhase (heatLog t z) else 0
private theorem angleGood_measurable(t:ℝ):Measurable (angleGood t):=by
  have hV:Measurable GaussNativeEnergy.volume:=volume_smooth.continuous.measurable
  have hL:Measurable (heatLog t):=by
    exact log_measurable.comp (measurable_const.add (measurable_const.mul hV.inv))
  have hc:ContinuousOn clockPhase (Set.Ioi (0:ℝ)):=by
    intro x hx
    exact (clockPhase_smooth x hx).continuousAt.continuousWithinAt
  have hp:Measurable (Set.piecewise (Set.Ioi (0:ℝ)) clockPhase (fun _=>0)):=
    hc.measurable_piecewise continuousOn_const measurableSet_Ioi
  change Measurable (fun z=>Set.piecewise (Set.Ioi (0:ℝ)) clockPhase (fun _=>0) (heatLog t z))
  exact hp.comp hL
private def goodCoefficient(t ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatMean t z+Real.sqrt (heatVariance t z)*
    (ξ*Real.cos (angleGood t z)+η*Real.sin (angleGood t z))
private theorem goodCoefficient_chart(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    goodCoefficient t ξ η z.val=correctedCoefficient t ξ η z.val:=by
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  have hp:0<heatLog t z.val:=Real.log_pos (by
    change 1<1+18*t*reciprocalVolume z.val
    have h:0<18*t*reciprocalVolume z.val:=by positivity
    linarith)
  change heatMean t z.val+Real.sqrt (heatVariance t z.val)*
    (ξ*Real.cos (if 0<heatLog t z.val then clockPhase (heatLog t z.val) else 0)+
      η*Real.sin (if 0<heatLog t z.val then clockPhase (heatLog t z.val) else 0))=_
  rw [if_pos hp]
  rfl
private def goodProfile(t p q:ℝ)(x:SourceCoordinateSlice×(ℝ×ℝ)):ℝ:=
  (forwardRatio t x.1)^p*Real.exp (q*goodCoefficient t x.2.1 x.2.2 x.1)
private theorem goodProfile_measurable(t p q:ℝ):Measurable (goodProfile t p q):=by
  have hV:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>GaussNativeEnergy.volume x.1):=
    volume_smooth.continuous.measurable.comp measurable_fst
  have hR:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>forwardRatio t x.1):=
    (hV.add_const (18*t)).div hV
  have hL:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>heatLog t x.1):=by
    exact log_measurable.comp (measurable_const.add (measurable_const.mul hV.inv))
  have hθ:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>angleGood t x.1):=
    (angleGood_measurable t).comp measurable_fst
  have hξ:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>x.2.1):=
    measurable_fst.comp measurable_snd
  have hη:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>x.2.2):=
    measurable_snd.comp measurable_snd
  have hc:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>goodCoefficient t x.2.1 x.2.2 x.1):=
    (hL.neg.div_const 6).add
      ((Real.continuous_sqrt.measurable.comp (hL.div_const 9)).mul
        ((hξ.mul hθ.cos).add (hη.mul hθ.sin)))
  exact ((power_measurable p).comp hR).mul (Real.continuous_exp.measurable.comp (measurable_const.mul hc))
private theorem exponential_moment(t:ℝ)(ht:0<t)(q:ℝ)(z:physicalChart):
    Integrable (fun w:ℝ×ℝ=>Real.exp (q*correctedCoefficient t w.1 w.2 z.val)) (γ.prod γ)∧
      (∫w:ℝ×ℝ,Real.exp (q*correctedCoefficient t w.1 w.2 z.val) ∂γ.prod γ)=
        (forwardRatio t z.val)^(q*(q-3)/18):=by
  have h:=SourceClockPhiGaussianPlaneSource.actual_rotated_heat_exponential_moment
    (GaussNativeEnergy.volume z.val) t q (clockPhase (heatLog t z.val)) (volume_pos z) ht
  have he:heatLog t z.val=Real.log ((GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val):=by
    unfold heatLog reciprocalVolume
    congr 1
    field_simp [(volume_pos z).ne']
  change Integrable (fun w:ℝ×ℝ=>Real.exp (q*(heatMean t z.val+
      Real.sqrt (heatVariance t z.val)*(w.1*Real.cos (clockPhase (heatLog t z.val))+
        w.2*Real.sin (clockPhase (heatLog t z.val)))))) (γ.prod γ)∧
    (∫w:ℝ×ℝ,Real.exp (q*(heatMean t z.val+
      Real.sqrt (heatVariance t z.val)*(w.1*Real.cos (clockPhase (heatLog t z.val))+
        w.2*Real.sin (clockPhase (heatLog t z.val))))) ∂γ.prod γ)=
      (forwardRatio t z.val)^(q*(q-3)/18)
  simpa only [heatMean,heatVariance,he,forwardRatio,Real.rpow_eq_pow] using h
private def kernel(t p q:ℝ)(f h:QuantumTest)(x:SourceCoordinateSlice×(ℝ×ℝ)):ℂ:=
  (goodProfile t p q x:ℂ)*densityPair f h x.1
private theorem kernel_section(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun w:ℝ×ℝ=>kernel t p q f h (z,w)) (γ.prod γ):=by
  by_cases hz:z∈physicalChart
  · have hgood(w:ℝ×ℝ):goodCoefficient t w.1 w.2 z=correctedCoefficient t w.1 w.2 z:=
      goodCoefficient_chart t ht w.1 w.2 ⟨z,hz⟩
    have hi:=((exponential_moment t ht q ⟨z,hz⟩).1.const_mul ((forwardRatio t z)^p)).ofReal.mul_const (densityPair f h z)
    have he(w:ℝ×ℝ):kernel t p q f h (z,w)=
        ((((forwardRatio t z)^p*Real.exp (q*correctedCoefficient t w.1 w.2 z)):ℝ):ℂ)*densityPair f h z:=by
      simp only [kernel,goodProfile,hgood]
    exact hi.congr (Filter.Eventually.of_forall (fun w=>(he w).symm))
  · simp only [kernel,density_offchart f h z hz,mul_zero]
    exact integrable_const (0:ℂ)
private theorem kernel_integral(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫w:ℝ×ℝ,kernel t p q f h (z,w) ∂γ.prod γ)=
      densityPair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h) z:=by
  rw [gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hgood(w:ℝ×ℝ):goodCoefficient t w.1 w.2 z=correctedCoefficient t w.1 w.2 z:=
      goodCoefficient_chart t ht w.1 w.2 ⟨z,hz⟩
    have hm:=(exponential_moment t ht q ⟨z,hz⟩).2
    simp only [kernel,goodProfile,hgood,Complex.ofReal_mul]
    rw [integral_mul_const,integral_const_mul,integral_complex_ofReal,hm]
    rw [←Complex.ofReal_mul,←Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩)]
  · simp only [kernel,density_offchart f h z hz,mul_zero,integral_zero]
private theorem kernel_norm_integral(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest)(z:SourceCoordinateSlice):
    (∫w:ℝ×ℝ,‖kernel t p q f h (z,w)‖ ∂γ.prod γ)=
      ‖densityPair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h) z‖:=by
  rw [gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hgood(w:ℝ×ℝ):goodCoefficient t w.1 w.2 z=correctedCoefficient t w.1 w.2 z:=
      goodCoefficient_chart t ht w.1 w.2 ⟨z,hz⟩
    have hpos:∀w:ℝ×ℝ,0≤(forwardRatio t z)^p*Real.exp (q*goodCoefficient t w.1 w.2 z):=
      fun w=>mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
    have hm:=(exponential_moment t ht q ⟨z,hz⟩).2
    simp only [kernel,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [goodProfile]
    simp_rw [abs_of_nonneg (hpos _)]
    simp_rw [hgood]
    rw [integral_mul_const,integral_const_mul,hm]
    rw [←Real.rpow_add hr]
    rw [abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  · simp only [kernel,density_offchart f h z hz,mul_zero,norm_zero,integral_zero]

theorem actual_corrected_gaussian_weighted_source_pair(t:ℝ)(ht:0<t)(p q:ℝ)(f h:QuantumTest):
    Integrable (fun w:ℝ×ℝ=>sourcePair f (correctedProfileWeight t ht p q w.1 w.2 h)) (γ.prod γ)∧
      (∫w:ℝ×ℝ,sourcePair f (correctedProfileWeight t ht p q w.1 w.2 h) ∂γ.prod γ)=
        sourcePair f (gaussianProfileWeight t ht (p+q*(q-3)/18) h):=by
  have hm:AEStronglyMeasurable (kernel t p q f h) (config.prod (γ.prod γ)):=
    (Complex.continuous_ofReal.measurable.comp (goodProfile_measurable t p q)).aestronglyMeasurable.mul
      (densityPair_integrable f h).aestronglyMeasurable.comp_fst
  have hp:Integrable (kernel t p q f h) (config.prod (γ.prod γ)):=by
    apply (integrable_prod_iff hm).mpr
    constructor
    · exact Filter.Eventually.of_forall (kernel_section t ht p q f h)
    · exact (densityPair_integrable f (gaussianProfileWeight t ht (p+q*(q-3)/18) h)).norm.congr
        (Filter.Eventually.of_forall (fun z=>(kernel_norm_integral t ht p q f h z).symm))
  have he(w:ℝ×ℝ):sourcePair f (correctedProfileWeight t ht p q w.1 w.2 h)=
      ∫z,kernel t p q f h (z,w) ∂config:=by
    rw [sourcePair_integral]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z=>by
      change densityPair f (multiply (fun y=>(forwardRatio t y)^p*
        Real.exp (q*correctedCoefficient t w.1 w.2 y)) _ h) z=kernel t p q f h (z,w)
      rw [density_multiply]
      by_cases hz:z∈physicalChart
      · change (((((forwardRatio t z)^p*Real.exp (q*correctedCoefficient t w.1 w.2 z)):ℝ):ℂ)*densityPair f h z)=
          (((((forwardRatio t z)^p*Real.exp (q*goodCoefficient t w.1 w.2 z)):ℝ):ℂ)*densityPair f h z)
        rw [goodCoefficient_chart t ht w.1 w.2 ⟨z,hz⟩]
      · simp only [kernel,density_offchart f h z hz,mul_zero])
  refine ⟨hp.integral_prod_right.congr (Filter.Eventually.of_forall (fun w=>(he w).symm)),?_⟩
  simp_rw [he]
  have hs:Integrable (Function.uncurry (fun z w=>kernel t p q f h (z,w))) (config.prod (γ.prod γ)):=hp
  rw [←integral_integral_swap hs]
  simp_rw [kernel_integral t ht p q f h]
  exact (sourcePair_integral _ _).symm
end LowEnergy.SourceClockPhiCorrectedGaussianPair
