import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianLinearMoment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.GaussianProfileFirstMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore ClockPhiConservativeHeatSource
open SourceClockPhiHeatLocalNativeGaussian SourceClockPhiCorrectedGaussianPair
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatCovariancePhase FirstCurrentWholeVariance
open MeasureTheory ProbabilityTheory
open scoped Topology ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
private abbrev config:=GaussHistoryHilbert.configurationMeasure
attribute [local irreducible] sourcePair embed
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

private theorem coefficient_formula(t ξ η:ℝ)(z:SourceCoordinateSlice):
    correctedCoefficient t ξ η z=heatMean t z+Real.sqrt (heatVariance t z)*
      (ξ*Real.cos (clockPhase (heatLog t z))+η*Real.sin (clockPhase (heatLog t z))):=rfl

def sourceNoiseSlope(t:ℝ)(axis:Bool)(z:SourceCoordinateSlice):ℝ:=
  correctedCoefficient t (if axis then 0 else 1) (if axis then 1 else 0) z-correctedCoefficient t 0 0 z
private theorem slope_smooth(t:ℝ)(ht:0<t)(axis:Bool)(z:physicalChart):ContDiffAt ℝ ∞ (sourceNoiseSlope t axis) z.val:=
  (coefficient_smooth t ht _ _ z).sub (coefficient_smooth t ht 0 0 z)

theorem actual_source_noise_slope(t:ℝ)(axis:Bool)(z:SourceCoordinateSlice):
    sourceNoiseSlope t axis z=Real.sqrt (heatVariance t z)*
      (if axis then Real.sin (clockPhase (heatLog t z)) else Real.cos (clockPhase (heatLog t z))):=by
  cases axis <;> simp [sourceNoiseSlope,coefficient_formula]

def firstMomentAction(t:ℝ)(ht:0<t)(axis:Bool)(p q:ℝ):End:=
  multiply (fun z=>q*sourceNoiseSlope t axis z)
    (fun z=>contDiffAt_const.mul (slope_smooth t ht axis z))*
    gaussianProfileWeight t ht (p+q*(q-3)/18)

private theorem point_first_moment(t:ℝ)(ht:0<t)(axis:Bool)(q:ℝ)(z:physicalChart):
    Integrable (fun x:ℝ×ℝ=>noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z.val)) γ₂ ∧
    (∫x:ℝ×ℝ,noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z.val) ∂γ₂)=
      q*sourceNoiseSlope t axis z.val*(forwardRatio t z.val)^(q*(q-3)/18):=by
  let m:=q*heatMean t z.val
  let a:=q*Real.sqrt (heatVariance t z.val)*Real.cos (clockPhase (heatLog t z.val))
  let b:=q*Real.sqrt (heatVariance t z.val)*Real.sin (clockPhase (heatLog t z.val))
  have he(x:ℝ×ℝ):m+a*x.1+b*x.2=q*correctedCoefficient t x.1 x.2 z.val:=by
    dsimp only [m,a,b]
    rw [coefficient_formula]
    ring
  have hs:(if axis then b else a)=q*sourceNoiseSlope t axis z.val:=by
    rw [actual_source_noise_slope]
    cases axis <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> dsimp only [a,b] <;> ring
  have h:=actual_gaussian_plane_linear_exponential axis m a b
  simpa only [he,hs,(exponential_moment t ht q z).2] using h

private theorem point_norm_bound(t:ℝ)(ht:0<t)(axis:Bool)(q:ℝ)(z:physicalChart):
    (∫x:ℝ×ℝ,|noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z.val)| ∂γ₂)≤
      (1+(forwardRatio t z.val)^((2*q)*(2*q-3)/18))/2:=by
  have hi:Integrable (fun x:ℝ×ℝ=>|noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z.val)|) γ₂:=by
    simpa only [Real.norm_eq_abs] using (point_first_moment t ht axis q z).1.norm
  have hsq:=actual_noise_square axis
  have he:=exponential_moment t ht (2*q) z
  have hb(x:ℝ×ℝ):|noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z.val)|≤
      (noiseCoordinate axis x^2+Real.exp ((2*q)*correctedCoefficient t x.1 x.2 z.val))/2:=by
    let a:=noiseCoordinate axis x
    let b:=Real.exp (q*correctedCoefficient t x.1 x.2 z.val)
    have he2:Real.exp ((2*q)*correctedCoefficient t x.1 x.2 z.val)=b^2:=by
      dsimp [b]
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [he2,abs_mul,abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg (|a|-b),sq_abs a]
  have h:=integral_mono hi ((hsq.1.add he.1).div_const 2) hb
  rw [integral_div] at h
  simp only [Pi.add_apply] at h
  erw [integral_add hsq.1 he.1,hsq.2,he.2] at h
  exact h

private def momentKernel(t p q:ℝ)(axis:Bool)(f g:QuantumTest)(x:SourceCoordinateSlice×(ℝ×ℝ)):ℂ:=
  ((noiseCoordinate axis x.2*goodProfile t p q x:ℝ):ℂ)*densityPair f g x.1
private theorem moment_section(t:ℝ)(ht:0<t)(p q:ℝ)(axis:Bool)(f g:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun x:ℝ×ℝ=>momentKernel t p q axis f g (z,x)) γ₂:=by
  by_cases hz:z∈physicalChart
  · have hgood(x:ℝ×ℝ):goodCoefficient t x.1 x.2 z=correctedCoefficient t x.1 x.2 z:=goodCoefficient_chart t ht x.1 x.2 ⟨z,hz⟩
    have hi:=((point_first_moment t ht axis q ⟨z,hz⟩).1.const_mul ((forwardRatio t z)^p)).ofReal.mul_const (densityPair f g z)
    apply hi.congr
    exact Filter.Eventually.of_forall (fun x=>by
      change (((forwardRatio t z)^p*(noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z)):ℝ):ℂ)*densityPair f g z=
        ((noiseCoordinate axis x*((forwardRatio t z)^p*Real.exp (q*goodCoefficient t x.1 x.2 z)):ℝ):ℂ)*densityPair f g z
      rw [hgood]
      congr 2
      ring)
  · simp only [momentKernel,density_offchart f g z hz,mul_zero]
    exact integrable_const (0:ℂ)
private theorem moment_mean(t:ℝ)(ht:0<t)(p q:ℝ)(axis:Bool)(f g:QuantumTest)(z:SourceCoordinateSlice):
    (∫x:ℝ×ℝ,momentKernel t p q axis f g (z,x) ∂γ₂)=densityPair f (firstMomentAction t ht axis p q g) z:=by
  rw [firstMomentAction,Module.End.mul_apply,density_multiply,gaussianProfileWeight,density_multiply]
  by_cases hz:z∈physicalChart
  · have hgood(x:ℝ×ℝ):goodCoefficient t x.1 x.2 z=correctedCoefficient t x.1 x.2 z:=goodCoefficient_chart t ht x.1 x.2 ⟨z,hz⟩
    have he(x:ℝ×ℝ):momentKernel t p q axis f g (z,x)=
        (((forwardRatio t z)^p:ℝ):ℂ)*((noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ)*densityPair f g z:=by
      simp only [momentKernel,goodProfile,hgood,Complex.ofReal_mul]
      ring
    simp_rw [he]
    rw [integral_mul_const,integral_const_mul,integral_complex_ofReal,(point_first_moment t ht axis q ⟨z,hz⟩).2,
      Real.rpow_add (forward_ratio_pos t ht.le ⟨z,hz⟩)]
    push_cast
    ring
  · simp only [momentKernel,density_offchart f g z hz,mul_zero,integral_zero]
private theorem moment_norm_bound(t:ℝ)(ht:0<t)(p q:ℝ)(axis:Bool)(f g:QuantumTest)(z:SourceCoordinateSlice):
    (∫x:ℝ×ℝ,‖momentKernel t p q axis f g (z,x)‖ ∂γ₂)≤
      (‖densityPair f (gaussianProfileWeight t ht p g) z‖+
        ‖densityPair f (gaussianProfileWeight t ht (p+(2*q)*(2*q-3)/18) g) z‖)/2:=by
  rw [gaussianProfileWeight,gaussianProfileWeight,density_multiply,density_multiply]
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hgood(x:ℝ×ℝ):goodCoefficient t x.1 x.2 z=correctedCoefficient t x.1 x.2 z:=goodCoefficient_chart t ht x.1 x.2 ⟨z,hz⟩
    have he(x:ℝ×ℝ):‖momentKernel t p q axis f g (z,x)‖=
        ((forwardRatio t z)^p*‖densityPair f g z‖)*|noiseCoordinate axis x*Real.exp (q*correctedCoefficient t x.1 x.2 z)|:=by
      simp only [momentKernel,goodProfile,hgood,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hr p)]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    calc
      _≤((forwardRatio t z)^p*‖densityPair f g z‖)*((1+(forwardRatio t z)^((2*q)*(2*q-3)/18))/2):=
        mul_le_mul_of_nonneg_left (point_norm_bound t ht axis q ⟨z,hz⟩) (by positivity)
      _=_:=by
        rw [Real.rpow_add hr]
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos hr p),abs_of_pos (Real.rpow_pos_of_pos hr ((2*q)*(2*q-3)/18))]
        ring
  · simp only [momentKernel,density_offchart f g z hz,mul_zero,norm_zero,integral_zero,zero_add,zero_div,le_refl]

/-- The actual xi/eta weighted profile mean is obtained by source-density Fubini. Gaussian absolute integrability is paid by the generated double exponential moment and the exact unit second moment. -/
theorem actual_profile_first_moment(t:ℝ)(ht:0<t)(axis:Bool)(p q:ℝ)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(noiseCoordinate axis x:ℂ)*sourcePair f (correctedProfileWeight t ht p q x.1 x.2 g)) γ₂ ∧
    (∫x:ℝ×ℝ,(noiseCoordinate axis x:ℂ)*sourcePair f (correctedProfileWeight t ht p q x.1 x.2 g) ∂γ₂)=
      sourcePair f (firstMomentAction t ht axis p q g):=by
  have hn:Measurable (fun x:SourceCoordinateSlice×(ℝ×ℝ)=>noiseCoordinate axis x.2):=by cases axis <;> dsimp [noiseCoordinate] <;> fun_prop
  have hm:AEStronglyMeasurable (momentKernel t p q axis f g) (config.prod γ₂):=
    (Complex.continuous_ofReal.measurable.comp (hn.mul (goodProfile_measurable t p q))).aestronglyMeasurable.mul
      (densityPair_integrable f g).aestronglyMeasurable.comp_fst
  have hp:Integrable (momentKernel t p q axis f g) (config.prod γ₂):=by
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (moment_section t ht p q axis f g),?_⟩
    apply (((densityPair_integrable f (gaussianProfileWeight t ht p g)).norm.add
      (densityPair_integrable f (gaussianProfileWeight t ht (p+(2*q)*(2*q-3)/18) g)).norm).div_const 2).mono'
      hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
      exact moment_norm_bound t ht p q axis f g z)
  have he(x:ℝ×ℝ):(noiseCoordinate axis x:ℂ)*sourcePair f (correctedProfileWeight t ht p q x.1 x.2 g)=
      ∫z,momentKernel t p q axis f g (z,x) ∂config:=by
    rw [sourcePair_integral,←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z=>by
      change (noiseCoordinate axis x:ℂ)*densityPair f (multiply
        (fun y=>(forwardRatio t y)^p*Real.exp (q*correctedCoefficient t x.1 x.2 y)) _ g) z=momentKernel t p q axis f g (z,x)
      rw [density_multiply]
      by_cases hz:z∈physicalChart
      · simp only [momentKernel,goodProfile,goodCoefficient_chart t ht x.1 x.2 ⟨z,hz⟩,Complex.ofReal_mul]
        ring
      · simp only [momentKernel,density_offchart f g z hz,mul_zero])
  refine ⟨hp.integral_prod_right.congr (Filter.Eventually.of_forall (fun x=>(he x).symm)),?_⟩
  simp_rw [he]
  have hpu:Integrable (Function.uncurry (fun z x=>momentKernel t p q axis f g (z,x))) (config.prod γ₂):=hp
  rw [←integral_integral_swap hpu]
  exact (integral_congr_ae (μ:=config) (Filter.Eventually.of_forall
    (moment_mean t ht p q axis f g))).trans (sourcePair_integral _ _).symm

/-- Both original gain legs contribute exactly 1/3 to the source power before the actual two-noise first moment is taken. -/
theorem actual_gained_profile_first_moment(t:ℝ)(ht:0<t)(axis:Bool)(p q r s:ℝ)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(noiseCoordinate axis x:ℂ)*sourcePair
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (correctedProfileWeight t ht p q x.1 x.2 f))
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (correctedProfileWeight t ht r s x.1 x.2 g))) γ₂ ∧
    (∫x:ℝ×ℝ,(noiseCoordinate axis x:ℂ)*sourcePair
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (correctedProfileWeight t ht p q x.1 x.2 f))
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (correctedProfileWeight t ht r s x.1 x.2 g)) ∂γ₂)=
      sourcePair f (firstMomentAction t ht axis (p+r+1/3) (q+s) g):=by
  simp_rw [actual_gained_profile_pair]
  exact actual_profile_first_moment t ht axis (p+r+1/3) (q+s) f g
end LowEnergy.GaussianProfileFirstMoment
