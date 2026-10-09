import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianSecondIBP
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedGainFrequencyPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatSecondNativeSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource
open SourceClockPhiCombinedScalePressure SourceClockPhiForwardNativeReturn
open SourceClockPhiHeatNativeClosedGraph MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev D:End:=combinedGenerator
private abbrev A:End:=combinedConjugate
private def parameterGenerator(t:ℝ)(ht:0<t):End:=
  (show {L:End // ∀f:QuantumTest,∀ξ:ℝ,HasDerivAt (fun u=>embed (sourceHeatCore t ht u f))
    (embed (sourceHeatCore t ht ξ (L f))) ξ} from
    ⟨_,fun f ξ=>sourceHeat_strong_derivative t ht f ξ⟩).val
private theorem parameter_derivative(t:ℝ)(ht:0<t)(f:QuantumTest)(ξ:ℝ):
    HasDerivAt (fun u=>embed (sourceHeatCore t ht u f))
      (embed (sourceHeatCore t ht ξ (parameterGenerator t ht f))) ξ:=
  (show {L:End // ∀f:QuantumTest,∀ξ:ℝ,HasDerivAt (fun u=>embed (sourceHeatCore t ht u f))
    (embed (sourceHeatCore t ht ξ (L f))) ξ} from
    ⟨_,fun f ξ=>sourceHeat_strong_derivative t ht f ξ⟩).property f ξ
private theorem heat_continuous(t:ℝ)(ht:0<t)(f:QuantumTest):
    Continuous (fun ξ=>embed (sourceHeatCore t ht ξ f)):=
  continuous_iff_continuousAt.mpr (fun ξ=>(parameter_derivative t ht f ξ).continuousAt)
private theorem log_pos(t:ℝ)(ht:0<t)(z:physicalChart):0<heatLog t z.val:=by
  apply Real.log_pos
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  change 1<1+18*t*reciprocalVolume z.val
  have hp:0<18*t*reciprocalVolume z.val:=by positivity
  linarith
private theorem log_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (heatLog t) z.val:=by
  apply (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_const).mul (reciprocal_volume_smooth z))).log
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
  positivity
private def width(t:ℝ)(z:SourceCoordinateSlice):ℝ:=Real.sqrt (heatVariance t z)
private theorem width_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (width t) z.val:=
  ((log_smooth t ht z).div_const 9).sqrt (ne_of_gt (div_pos (log_pos t ht z) (by norm_num)))
private def widthAction(t:ℝ)(ht:0<t):End:=multiply (width t) (width_smooth t ht)
private theorem parameter_point(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart):
    parameterGenerator t ht f z.val=(width t z.val:ℂ) • D f z.val:=by
  change (((Real.sqrt (heatVariance t z.val)*GaussNativeEnergy.volume z.val:ℝ):ℂ) •
    (noiseGenerator 0 1 f z.val))=_
  simp only [noiseGenerator,Complex.ofReal_zero,Complex.ofReal_one,zero_smul,one_smul,zero_add]
  change ((Real.sqrt (heatVariance t z.val)*GaussNativeEnergy.volume z.val:ℝ):ℂ) •
    ((reciprocalVolume z.val:ℂ) • D f z.val)=_
  rw [smul_smul,←Complex.ofReal_mul]
  congr 1
  unfold reciprocalVolume width
  field_simp [(volume_pos z).ne']
private theorem parameter_action(t:ℝ)(ht:0<t):parameterGenerator t ht=widthAction t ht*D:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · exact parameter_point t ht f ⟨z,hz⟩
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem generator_multiplier(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀r s z,c (localMap r s z)=c z):Commute D (multiply c hc):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  let M:End:=multiply c hc
  have he:(fun u:ℝ=>noiseCore 0 u (M f) z word)=fun u=>M (noiseCore 0 u f) z word:=by
    funext u
    exact congrArg (fun T:End=>T f z word) (noise_real_multiplier 0 u c hc (hi 0 u)).eq
  have h1:=noise_linear_zero_jet 0 1 (M f) z word
  have h2:=(noise_linear_zero_jet 0 1 f z word).const_mul (c z:ℂ)
  simp only [mul_zero,mul_one] at h1 h2
  rw [he] at h1
  have h:=h1.unique h2
  simp only [noiseGenerator,Complex.ofReal_zero,Complex.ofReal_one,zero_smul,one_smul,zero_add] at h
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ)*D (M f) z word=(c z:ℂ)*((reciprocalVolume z:ℂ)*D f z word) at h
    have hu:(reciprocalVolume z:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (inv_pos.mpr (volume_pos ⟨z,hz⟩)).ne'
    change D (M f) z word=(c z:ℂ)*D f z word
    apply mul_left_cancel₀ hu
    calc _=(c z:ℂ)*((reciprocalVolume z:ℂ)*D f z word):=h
         _=_:=by ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    simp only [Module.End.mul_apply,h0,PiLp.zero_apply]
private def secondCoefficient(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  9/((GaussNativeEnergy.volume z+18*t)*heatLog t z)
private theorem second_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (secondCoefficient t) z.val:=by
  have hv:0<GaussNativeEnergy.volume z.val+18*t:=by linarith [volume_pos z]
  exact contDiffAt_const.div ((volume_smooth.contDiffAt.add contDiffAt_const).mul (log_smooth t ht z))
    (mul_pos hv (log_pos t ht z)).ne'
private def secondAction(t:ℝ)(ht:0<t):End:=multiply (secondCoefficient t) (second_smooth t ht)
private theorem second_price(t:ℝ)(ht:0<t)(z:physicalChart):|secondCoefficient t z.val|≤1/(2*t):=by
  have hv:=volume_pos z
  have hL:=log_pos t ht z
  have hlog:heatLog t z.val=Real.log ((GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val):=by
    unfold heatLog reciprocalVolume;congr 1;field_simp [hv.ne']
  have hp:=SourceClockPhiHeatClockPrice.clock_log_payment _ t hv ht.le
  rw [←hlog] at hp
  have hw:0<GaussNativeEnergy.volume z.val+18*t:=by positivity
  rw [secondCoefficient,abs_of_pos (div_pos (by norm_num) (mul_pos hw hL))]
  apply (div_le_div_iff₀ (mul_pos hw hL) (by positivity:0<2*t)).mpr
  linarith
private theorem second_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖embed (secondAction t ht f)‖≤(1/(2*t))*‖embed f‖:=by
  apply GaussBoundedMultiplier.action_bound
    (fun z=>(secondCoefficient t z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z=>(Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (second_smooth t ht z)).smul contDiffAt_const)
    (fun _ w=>(Commute.one_right (GaussFockWeights.weight w)).smul_right _) _ (by positivity) _ f
  intro z x
  change ‖(secondCoefficient t z.val:ℂ) • x‖≤(1/(2*t))*‖x‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (second_price t ht z) (norm_nonneg x)
private def firstAction(t:ℝ)(ht:0<t):End:=forwardAAction t ht.le*D
private theorem parameter_square(t:ℝ)(ht:0<t)(f:QuantumTest):
    parameterGenerator t ht (parameterGenerator t ht (secondAction t ht f))=
      firstAction t ht (firstAction t ht f):=by
  have hW:=LinearMap.congr_fun (generator_multiplier (width t) (width_smooth t ht) (fun _ _ _=>rfl)).eq
  have hB:=LinearMap.congr_fun (generator_multiplier (secondCoefficient t) (second_smooth t ht) (fun _ _ _=>rfl)).eq
  have hA:=LinearMap.congr_fun (generator_multiplier (forwardA t) (forwardA_smooth t ht.le) (fun _ _ _=>rfl)).eq
  simp only [Module.End.mul_apply] at hW hB hA
  change ∀x:QuantumTest,D (widthAction t ht x)=widthAction t ht (D x) at hW
  change ∀x:QuantumTest,D (secondAction t ht x)=secondAction t ht (D x) at hB
  change ∀x:QuantumTest,D (forwardAAction t ht.le x)=forwardAAction t ht.le (D x) at hA
  rw [parameter_action]
  change widthAction t ht (D (widthAction t ht (D (secondAction t ht f))))=
    forwardAAction t ht.le (D (forwardAAction t ht.le (D f)))
  rw [hW,hB,hB,hA]
  apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have hv:0<GaussNativeEnergy.volume z+18*t:=by linarith [volume_pos ⟨z,hz⟩]
    have hL:=log_pos t ht ⟨z,hz⟩
    have hw:(width t z)^2=heatLog t z/9:=Real.sq_sqrt (by unfold heatVariance;positivity)
    have ha:(forwardA t z)^2=(GaussNativeEnergy.volume z+18*t)⁻¹:=by
      unfold forwardA
      rw [inv_pow,Real.sq_sqrt hv.le]
    have he:width t z*(width t z*secondCoefficient t z)=forwardA t z*forwardA t z:=by
      unfold secondCoefficient
      rw [←mul_assoc,←pow_two,hw,←pow_two,ha]
      field_simp [hv.ne',hL.ne']
    change (width t z:ℂ) • ((width t z:ℂ) • ((secondCoefficient t z:ℂ) • D (D f) z))=
      (forwardA t z:ℂ) • ((forwardA t z:ℂ) • D (D f) z)
    simp only [smul_smul,←Complex.ofReal_mul,he]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem heat_square(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    A (A (sourceHeatCore t ht ξ f))=sourceHeatCore t ht ξ (firstAction t ht (firstAction t ht f)):=by
  rw [heat_A,heat_A]
  rfl

private theorem hermite_integrable_bound {E:Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F:ℝ→E)(hc:Continuous F)(C:ℝ)(hB:∀ξ,‖F ξ‖≤C):
    Integrable (fun ξ:ℝ=>((ξ:ℂ)^2-1) • F ξ) γ:=by
  let :SecondCountableTopologyEither ℝ E:=⟨Or.inl inferInstance⟩
  have h2:Integrable (fun ξ:ℝ=>ξ^2) γ:=(ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 2).integrable_sq
  have hi:Integrable (fun ξ:ℝ=>|ξ^2-1|) γ:=(h2.sub (integrable_const 1)).norm
  have hc0:Continuous (fun ξ:ℝ=>((ξ:ℂ)^2-1) • F ξ):=
    ((Complex.continuous_ofReal.pow 2).sub continuous_const).smul hc
  apply (hi.mul_const C).mono' hc0.aestronglyMeasurable
  filter_upwards [] with ξ
  change ‖((ξ:ℂ)^2-1) • F ξ‖≤|ξ^2-1| *C
  rw [norm_smul]
  have he:‖(ξ:ℂ)^2-1‖=|ξ^2-1|:=by
    rw [show (ξ:ℂ)^2-1=((ξ^2-1:ℝ):ℂ) by push_cast;rfl,Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  exact mul_le_mul_of_nonneg_left (hB ξ) (abs_nonneg _)
private theorem hermite_integrable(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun ξ:ℝ=>((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f)) γ:=
  hermite_integrable_bound _ (heat_continuous t ht f) (‖embed f‖)
    (fun ξ=>(sourceHeat_norm t ht ξ f).le)
private def hermiteMean(t:ℝ)(ht:0<t):QuantumTest→ₗ[ℂ]H where
  toFun f:=∫ξ:ℝ,((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f) ∂γ
  map_add' f g:=by
    simp only [map_add,smul_add]
    exact integral_add (hermite_integrable t ht f) (hermite_integrable t ht g)
  map_smul' c f:=by
    simp only [map_smul,RingHom.id_apply]
    have he:(fun ξ:ℝ=>((ξ:ℂ)^2-1) • c • embed (sourceHeatCore t ht ξ f))=
      fun ξ:ℝ=>c • ((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f):=by
      funext ξ;exact smul_comm _ _ _
    rw [he];exact integral_smul c _
private theorem hermite_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖hermiteMean t ht f‖≤2*‖embed f‖:=by
  calc
    _≤∫ξ:ℝ,‖((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f)‖ ∂γ:=norm_integral_le_integral_norm _
    _=(∫ξ:ℝ,|ξ^2-1| ∂γ)*‖embed f‖:=by
      have he(ξ:ℝ):‖((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f)‖=|ξ^2-1| *‖embed f‖:=by
        rw [norm_smul,sourceHeat_norm]
        rw [show (ξ:ℂ)^2-1=((ξ^2-1:ℝ):ℂ) by push_cast;rfl,Complex.norm_real,Real.norm_eq_abs]
      simp_rw [he]
      exact integral_mul_const _ _
    _≤2*‖embed f‖:=mul_le_mul_of_nonneg_right
      SourceClockPhiGaussianSecondIBP.standard_gaussian_hermite_abs_price (norm_nonneg _)
private theorem hermite_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatMeanCore t ht (parameterGenerator t ht (parameterGenerator t ht f))=hermiteMean t ht f:=by
  apply ext_inner_left ℂ;intro p
  let h:ℝ→ℂ:=fun ξ=>inner ℂ p (embed (sourceHeatCore t ht ξ f))
  let h':ℝ→ℂ:=fun ξ=>inner ℂ p (embed (sourceHeatCore t ht ξ (parameterGenerator t ht f)))
  let h'':ℝ→ℂ:=fun ξ=>inner ℂ p (embed (sourceHeatCore t ht ξ (parameterGenerator t ht (parameterGenerator t ht f))))
  have hd(ξ:ℝ):HasDerivAt h (h' ξ) ξ:=
    ((innerSL ℂ p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt ξ (parameter_derivative t ht f ξ)
  have hd'(ξ:ℝ):HasDerivAt h' (h'' ξ) ξ:=
    ((innerSL ℂ p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt ξ (parameter_derivative t ht (parameterGenerator t ht f) ξ)
  have hc':Continuous h':=continuous_const.inner (heat_continuous t ht (parameterGenerator t ht f))
  have hc'':Continuous h'':=continuous_const.inner (heat_continuous t ht (parameterGenerator t ht (parameterGenerator t ht f)))
  have hc:ContDiff ℝ 1 h:=contDiff_one_iff_deriv.mpr
    ⟨fun ξ=>(hd ξ).differentiableAt,by rw [show deriv h=h' from funext (fun ξ=>(hd ξ).deriv)];exact hc'⟩
  have hc1:ContDiff ℝ 1 h':=contDiff_one_iff_deriv.mpr
    ⟨fun ξ=>(hd' ξ).differentiableAt,by rw [show deriv h'=h'' from funext (fun ξ=>(hd' ξ).deriv)];exact hc''⟩
  have hb(q:QuantumTest)(ξ:ℝ):‖inner ℂ p (embed (sourceHeatCore t ht ξ q))‖≤‖p‖*‖embed q‖:=
    (norm_inner_le_norm _ _).trans_eq (by rw [sourceHeat_norm])
  have hi:=SourceClockPhiGaussianSecondIBP.standard_gaussian_complex_second_IBP h h' h'' _ _ _ hc hc1 hd hd'
    (hb f) (hb (parameterGenerator t ht f)) (hb (parameterGenerator t ht (parameterGenerator t ht f)))
  have hl:=(innerSL ℂ p).integral_comp_comm (sourceHeat_integrable t ht (parameterGenerator t ht (parameterGenerator t ht f)))
  have hr:=(innerSL ℂ p).integral_comp_comm (hermite_integrable t ht f)
  change (∫ξ,h'' ξ ∂γ)=inner ℂ p (heatMeanCore t ht (parameterGenerator t ht (parameterGenerator t ht f))) at hl
  change (∫ξ,inner ℂ p (((ξ:ℂ)^2-1) • embed (sourceHeatCore t ht ξ f)) ∂γ)=inner ℂ p (hermiteMean t ht f) at hr
  rw [←hl,←hr]
  simpa only [h,inner_smul_right] using hi
private def secondCore(t:ℝ)(ht:0<t):QuantumTest→ₗ[ℂ]H:=
  (hermiteMean t ht).comp (secondAction t ht)
private theorem secondCore_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖secondCore t ht f‖≤(1/t)*‖embed f‖:=by
  calc
    _≤2*‖embed (secondAction t ht f)‖:=hermite_bound t ht _
    _≤2*((1/(2*t))*‖embed f‖):=mul_le_mul_of_nonneg_left (second_bound t ht f) (by norm_num)
    _=(1/t)*‖embed f‖:=by ring

def heatASecondReader(t:ℝ)(ht:0<t):H→L[ℂ]H:=(secondCore t ht).extendOfNorm embed
private theorem secondReader_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatASecondReader t ht (embed f)=secondCore t ht f:=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense ⟨_,secondCore_bound t ht⟩ f
private theorem mean_readback(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatOperator t ht (embed f)=heatMeanCore t ht f:=by
  unfold heatOperator
  change (ContinuousLinearMap.extend _ Core.subtypeL) (Core.subtypeL (coreEquiv f))=heatMeanCore t ht f
  rw [ContinuousLinearMap.extend_eq _ GaussBoundedMultiplier.core_dense
    isometry_subtype_coe.isUniformInducing (coreEquiv f)]
  change heatMeanCore t ht (coreEquiv.symm (coreEquiv f))=heatMeanCore t ht f
  rw [coreEquiv.symm_apply_apply]
private theorem firstCore_graph(t:ℝ)(ht:0<t)(f:QuantumTest):
    (heatOperator t ht (embed f),heatMeanCore t ht (firstAction t ht f))∈
      SymmetricGraphClosure.closedGraph (realize A):=by
  have hi:Integrable (fun ξ=>embed (A (sourceHeatCore t ht ξ f))) γ:=by
    simp only [heat_A]
    exact sourceHeat_integrable t ht (firstAction t ht f)
  have h:=integral_core_graph A (fun ξ=>sourceHeatCore t ht ξ f) (sourceHeat_integrable t ht f) hi
  simp only [heat_A] at h
  rw [mean_readback]
  exact h
private theorem firstCore_readback(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatAReader t ht (embed f)=heatMeanCore t ht (firstAction t ht f):=by
  have h:=(actual_heat_native_smoothing t ht).2.2.2.2 (embed f)
  exact actual_A_closed_graph_singlevalued h.2.1.1 (firstCore_graph t ht f)
private theorem secondCore_graph(t:ℝ)(ht:0<t)(f:QuantumTest):
    (heatAReader t ht (embed f),secondCore t ht f)∈SymmetricGraphClosure.closedGraph (realize A):=by
  have hi:Integrable (fun ξ=>embed (A (sourceHeatCore t ht ξ f))) γ:=by
    simp only [heat_A];exact sourceHeat_integrable t ht (firstAction t ht f)
  have hi2:Integrable (fun ξ=>embed (A (A (sourceHeatCore t ht ξ f)))) γ:=by
    simp only [heat_square];exact sourceHeat_integrable t ht (firstAction t ht (firstAction t ht f))
  have h:=integral_core_graph A (fun ξ=>A (sourceHeatCore t ht ξ f)) hi hi2
  have he:=hermite_source t ht (secondAction t ht f)
  rw [parameter_square] at he
  simp only [heat_A] at h
  rw [firstCore_readback]
  change (heatMeanCore t ht (firstAction t ht f),hermiteMean t ht (secondAction t ht f))∈_
  rw [←he]
  exact h
private theorem all_second_graph(t:ℝ)(ht:0<t)(x:H):
    (heatAReader t ht x,heatASecondReader t ht x)∈SymmetricGraphClosure.closedGraph (realize A):=
  (SourceClockPhiHeatClosedGraphExtension.actual_closed_graph_dense_extension A (heatAReader t ht)
    (secondCore t ht) (1/t) (secondCore_bound t ht) (secondCore_graph t ht) x).1
private theorem squareCore_graph(t:ℝ)(ht:0<t)(f:QuantumTest):
    (heatOperator t ht (embed f),secondCore t ht f)∈SymmetricGraphClosure.closedGraph (realize (A*A)):=by
  have hi:Integrable (fun ξ=>embed ((A*A) (sourceHeatCore t ht ξ f))) γ:=by
    simp only [Module.End.mul_apply,heat_square]
    exact sourceHeat_integrable t ht (firstAction t ht (firstAction t ht f))
  have h:=integral_core_graph (A*A) (fun ξ=>sourceHeatCore t ht ξ f) (sourceHeat_integrable t ht f) hi
  have he:=hermite_source t ht (secondAction t ht f)
  rw [parameter_square] at he
  simp only [Module.End.mul_apply,heat_square] at h
  rw [mean_readback]
  change (heatMeanCore t ht f,hermiteMean t ht (secondAction t ht f))∈_
  rw [←he]
  exact h
private theorem all_square_graph(t:ℝ)(ht:0<t)(x:H):
    (heatOperator t ht x,heatASecondReader t ht x)∈SymmetricGraphClosure.closedGraph (realize (A*A)):=
  (SourceClockPhiHeatClosedGraphExtension.actual_closed_graph_dense_extension (A*A) (heatOperator t ht)
    (secondCore t ht) (1/t) (secondCore_bound t ht) (squareCore_graph t ht) x).1
private theorem second_dual(t:ℝ)(ht:0<t)(x:H)(h:QuantumTest):
    inner ℂ (heatAReader t ht x) (embed (A h))= -inner ℂ (heatASecondReader t ht x) (embed h):=by
  have hp:=SymmetricGraphClosure.closed_graph_pairing (realize A) (realize (-A))
    actual_A_formal_pair (all_second_graph t ht x) (coreEquiv h)
  change inner ℂ (heatASecondReader t ht x) (embed h)=
    inner ℂ (heatAReader t ht x) (embed (-A (coreEquiv.symm (coreEquiv h)))) at hp
  rw [coreEquiv.symm_apply_apply,map_neg,inner_neg_right] at hp
  have hn:=congrArg Neg.neg hp
  simpa only [neg_neg] using hn.symm

/-- Hermite two acts in the original A graph and pays the complete dual A leg on every Hilbert input. -/
theorem actual_heat_second_native_source(t:ℝ)(ht:0<t):
    ‖heatASecondReader t ht‖≤1/t ∧ ∀x:H,
      ((heatOperator t ht x,heatASecondReader t ht x)∈SymmetricGraphClosure.closedGraph (realize (A*A))) ∧
      ((heatAReader t ht x,heatASecondReader t ht x)∈SymmetricGraphClosure.closedGraph (realize A)) ∧
      ∀h:QuantumTest,inner ℂ (heatAReader t ht x) (embed (A h))=
        -inner ℂ (heatASecondReader t ht x) (embed h):=by
  refine ⟨LinearMap.opNorm_extendOfNorm_le SourceCoframeScaleTransport.embed_dense (by positivity)
    (secondCore_bound t ht),fun x=>⟨all_square_graph t ht x,all_second_graph t ht x,second_dual t ht x⟩⟩
private theorem second_dual_price(t:ℝ)(ht:0<t)(x:H)(h:QuantumTest):
    t*‖inner ℂ (heatAReader t ht x) (embed (A h))‖≤‖x‖*‖embed h‖:=by
  have hb:‖heatASecondReader t ht x‖≤(1/t)*‖x‖:=
    ((heatASecondReader t ht).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (actual_heat_second_native_source t ht).1 (norm_nonneg x))
  have hc:t*‖heatASecondReader t ht x‖≤‖x‖:=by
    calc _≤t*((1/t)*‖x‖):=mul_le_mul_of_nonneg_left hb ht.le
         _=‖x‖:=by field_simp [ht.ne']
  rw [second_dual,norm_neg]
  calc
    _≤t*(‖heatASecondReader t ht x‖*‖embed h‖):=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ht.le
    _=(t*‖heatASecondReader t ht x‖)*‖embed h‖:=by ring
    _≤‖x‖*‖embed h‖:=mul_le_mul_of_nonneg_right hc (norm_nonneg _)
open GaussDiagonalHistory GaussUnitaryHistory SourceLocalizedInverseFormPayment
open SourceClockPhiNormalizedScalarBudget ClockPhiMatchedGainFrequencyPayment
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    (actualFrequency advanced μ freq).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
private theorem frequency_norm_floor(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    μ≤‖actualFrequency advanced μ freq‖:=by
  have h:=Complex.abs_im_le_norm (actualFrequency advanced μ freq)
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,abs_neg,abs_of_pos hμ] using h
private theorem source_dual_price(t:ℝ)(ht:0<t)(μ:ℝ)(hμ:0<μ)(z:ℂ)(hz:μ≤‖z‖)
    (w v:QuantumTest)(he:z • w=v):
    t*‖inner ℂ (heatAReader t ht (embed w)) (embed (A v))‖≤‖embed v‖^2/μ:=by
  have hn:‖embed v‖=‖z‖*‖embed w‖:=by rw [←he,map_smul,norm_smul]
  have hw:μ*‖embed w‖≤‖embed v‖:=by
    rw [hn]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hp:‖embed w‖*‖embed v‖≤‖embed v‖^2/μ:=by
    apply (le_div_iff₀ hμ).mpr
    have hh:=mul_le_mul_of_nonneg_right hw (norm_nonneg (embed v))
    nlinarith only [hh]
  exact (second_dual_price t ht (embed w) v).trans hp

/-- The physical-frequency leg is paid with the same two fixed source inputs, after one cutoff for every positive heat time. -/
theorem actual_heat_physical_frequency_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,∀t:ℝ,∀ht:0<t,
      (∫⁻freq:ℝ,ENNReal.ofReal (t*‖inner ℂ
        (heatAReader t ht (embed (normalizedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)))
        (embed (A (shiftedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)))‖))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (μ*ε) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced t ht
  calc
    _≤∫⁻freq:ℝ,ENNReal.ofReal μ⁻¹*ENNReal.ofReal
        (‖embed (shiftedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)‖^2):=by
      apply lintegral_mono
      intro freq
      have hp:=source_dual_price t ht μ hμ (actualFrequency advanced μ freq)
        (frequency_norm_floor advanced μ hμ freq) _ _
        (hS m ell (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq)).1
      dsimp only
      rw [←ENNReal.ofReal_mul (inv_pos.mpr hμ).le]
      apply ENNReal.ofReal_le_ofReal
      simpa only [div_eq_mul_inv,mul_comm] using hp
    _=ENNReal.ofReal μ⁻¹*(∫⁻freq:ℝ,ENNReal.ofReal
        (‖embed (shiftedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)‖^2)):=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal μ⁻¹*ENNReal.ofReal (μ*ε):=
      mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _=ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul (inv_pos.mpr hμ).le]
      congr 1
      field_simp [hμ.ne']
end LowEnergy.ClockPhiHeatSecondNativeSource
