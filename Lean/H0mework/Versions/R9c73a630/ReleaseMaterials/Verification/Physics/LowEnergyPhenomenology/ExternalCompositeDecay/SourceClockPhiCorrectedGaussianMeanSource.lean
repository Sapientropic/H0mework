import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedHamiltonianWorkEvolution
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatSecondNativeSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedGaussianMeanSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open ClockPhiHeatCorrectedCovarianceSource ClockPhiHeatCovariancePhase ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
private abbrev γ:=gaussianReal 0 1

private theorem rotated_scalar_law(θ:ℝ):
    (γ.prod γ).map (fun x:ℝ×ℝ=>x.1*Real.cos θ+x.2*Real.sin θ)=γ:=by
  let X:ℝ×ℝ→ℝ:=fun x=>Real.cos θ*x.1
  let Y:ℝ×ℝ→ℝ:=fun x=>Real.sin θ*x.2
  have hXY:IndepFun X Y (γ.prod γ):=indepFun_prod (by fun_prop) (by fun_prop)
  have hX:(γ.prod γ).map X=gaussianReal 0 ⟨Real.cos θ^2,sq_nonneg _⟩:=by
    change (γ.prod γ).map ((fun x:ℝ=>Real.cos θ*x)∘Prod.fst)=_
    rw [←Measure.map_map (by fun_prop) measurable_fst]
    simp only [Measure.map_fst_prod,measure_univ,one_smul,gaussianReal_map_const_mul,mul_zero,mul_one]
    rfl
  have hY:(γ.prod γ).map Y=gaussianReal 0 ⟨Real.sin θ^2,sq_nonneg _⟩:=by
    change (γ.prod γ).map ((fun x:ℝ=>Real.sin θ*x)∘Prod.snd)=_
    rw [←Measure.map_map (by fun_prop) measurable_snd]
    simp only [Measure.map_snd_prod,measure_univ,one_smul,gaussianReal_map_const_mul,mul_zero,mul_one]
    rfl
  have hV:(⟨Real.cos θ^2,sq_nonneg _⟩:NNReal)+⟨Real.sin θ^2,sq_nonneg _⟩=1:=by
    apply NNReal.coe_injective
    change Real.cos θ^2+Real.sin θ^2=1
    exact Real.cos_sq_add_sin_sq θ
  simpa only [X,Y,Pi.add_apply,mul_comm,hV,zero_add] using! gaussianReal_add_gaussianReal_of_indepFun hXY hX hY

private theorem profile_point_continuous(t:ℝ)(z:SourceCoordinateSlice)(f:QuantumTest)(word:Occupation):
    Continuous (fun r:ℝ=>
      (Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ)*
        f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z) word):=by
  have hC:Continuous (fun r:ℝ=>combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z):=by
    simp only [combinedMap_apply]
    fun_prop
  have hF:Continuous (fun r:ℝ=>f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z) word):=
    (PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp (f.continuous.comp hC)
  exact (by fun_prop : Continuous (fun r:ℝ=>(Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ))).mul hF

theorem actual_corrected_profile_mean_point(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    (∫x:ℝ×ℝ,correctedProfileCore t ht x.1 x.2 f z word ∂γ.prod γ)=
      ∫r:ℝ,(Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ)*
        f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z) word ∂γ:=by
  let θ:=clockPhase (heatLog t z)
  let F:ℝ→ℂ:=fun r=>(Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ)*
    f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z) word
  have hF:Continuous F:=profile_point_continuous t z f word
  have hM:=rotated_scalar_law θ
  have hI:=integral_map (μ:=γ.prod γ) (φ:=fun x:ℝ×ℝ=>x.1*Real.cos θ+x.2*Real.sin θ)
    (by fun_prop) hF.aestronglyMeasurable
  rw [hM] at hI
  convert hI.symm using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x=>by
    change ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t x.1 x.2 z)):ℂ) •
      f (combinedMap (1*correctedCoefficient t x.1 x.2 z) z)) word=F (x.1*Real.cos θ+x.2*Real.sin θ)
    simp only [one_mul,PiLp.smul_apply,smul_eq_mul]
    rfl)

theorem actual_corrected_heat_mean_point(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    (∫x:ℝ×ℝ,correctedHeatCore t ht x.1 x.2 f z word ∂γ.prod γ)=
      ∫r:ℝ,sourceHeatCore t ht r f z word ∂γ:=by
  by_cases ha:18*t<volume z
  · have heC(x:ℝ×ℝ):correctedHeatCore t ht x.1 x.2 f z word=
        (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
          correctedProfileCore t ht x.1 x.2 f (backwardPoint t z) word:=by
      change (forwardValue t (correctedProfileCore t ht x.1 x.2 f) z) word=_
      rw [forwardValue,if_pos ha]
    have heO(r:ℝ):sourceHeatCore t ht r f z word=
        (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
          ((Real.exp ((25/2:ℝ)*(heatMean t (backwardPoint t z)+Real.sqrt (heatVariance t (backwardPoint t z))*r)):ℂ)*
            f (combinedMap (heatMean t (backwardPoint t z)+Real.sqrt (heatVariance t (backwardPoint t z))*r)
              (backwardPoint t z)) word):=by
      let c:ℝ:=heatMean t (backwardPoint t z)+Real.sqrt (heatVariance t (backwardPoint t z))*r
      change (forwardValue t _ z) word=_
      rw [forwardValue,if_pos ha]
      change (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
        ((Real.exp ((25/2:ℝ)*(1*c)):ℂ) • f (combinedMap (1*c) (backwardPoint t z))) word=_
      simp only [one_mul,PiLp.smul_apply,smul_eq_mul]
      rfl
    simp_rw [heC,heO]
    rw [integral_const_mul,actual_corrected_profile_mean_point]
    rw [←integral_const_mul]
  · have heC(x:ℝ×ℝ):correctedHeatCore t ht x.1 x.2 f z word=0:=by
      change (forwardValue t _ z) word=0
      simp only [forwardValue,if_neg ha,PiLp.zero_apply]
    have heO(r:ℝ):sourceHeatCore t ht r f z word=0:=by
      change (forwardValue t _ z) word=0
      simp only [forwardValue,if_neg ha,PiLp.zero_apply]
    simp only [heC,heO,integral_zero]

private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev config:=GaussHistoryHilbert.configurationMeasure

private theorem density_continuous(f g:QuantumTest):Continuous (densityPair f g):=by
  simp only [funext (densityPair_sum f g)]
  apply continuous_finsetSum
  intro word _
  have hc:Continuous (GaussDensityCore.complexDensity word.card):=by
    apply Complex.continuous_ofReal.comp
    exact (GaussHistoryHilbert.jacobian_continuous.comp (by fun_prop)).mul (by fun_prop)
  have hf:Continuous (fun z:SourceCoordinateSlice=>f z word):=
    (PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp f.continuous
  have hg:Continuous (fun z:SourceCoordinateSlice=>g z word):=
    (PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp g.continuous
  exact (hc.mul hf.star).mul hg

private theorem density_norm_bound(f g:QuantumTest)(z:SourceCoordinateSlice):
    ‖densityPair f g z‖≤(densityPair f f z).re+(densityPair g g z).re:=by
  by_cases hz:z∈physicalChart
  · let c:ℕ→ℝ:=fun N=>GaussDensityCore.density N z
    have hc(N:ℕ):0≤c N:=(GaussDensityCore.density_pos N ⟨z,hz⟩).le
    have he(p q:FockFiber):inner ℂ (GaussFockWeights.weight (fun N=>(c N:ℂ)) p) q=
        inner ℂ (GaussBoundedMultiplier.halfWeight c p) (GaussBoundedMultiplier.halfWeight c q):=by
      rw [←GaussBoundedMultiplier.halfWeight_square c hc]
      exact GaussBoundedMultiplier.halfWeight_pair c _ _
    change ‖inner ℂ (GaussFockWeights.weight (fun N=>(c N:ℂ)) (f z)) (g z)‖≤
      (inner ℂ (GaussFockWeights.weight (fun N=>(c N:ℂ)) (f z)) (f z)).re+
      (inner ℂ (GaussFockWeights.weight (fun N=>(c N:ℂ)) (g z)) (g z)).re
    have hself(v:FockFiber):(inner ℂ v v).re=‖v‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) v
    simp only [he,hself]
    apply (norm_inner_le_norm _ _).trans
    nlinarith [sq_nonneg (‖GaussBoundedMultiplier.halfWeight c (f z)‖-‖GaussBoundedMultiplier.halfWeight c (g z)‖)]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    have hg:g z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (g.tsupport_subset h))
    simp only [densityPair,hf,hg,map_zero,inner_zero_left,norm_zero,Complex.zero_re,add_zero,le_refl]

private theorem density_integral_norm_bound(f g:QuantumTest):
    (∫z,‖densityPair f g z‖ ∂config)≤‖embed f‖^2+‖embed g‖^2:=by
  have h:=integral_mono (densityPair_integrable f g).norm
    ((densityPair_integrable f f).re.add (densityPair_integrable g g).re) (density_norm_bound f g)
  simp only [Pi.add_apply] at h
  rw [integral_add (densityPair_integrable f f).re (densityPair_integrable g g).re,
    ←GaussBoundedMultiplier.norm_square_integral f,←GaussBoundedMultiplier.norm_square_integral g] at h
  exact h

private theorem joint_density_integrable {ι:Type*}[TopologicalSpace ι][TopologicalSpace.MetrizableSpace ι]
    [MeasurableSpace ι][SecondCountableTopology ι][OpensMeasurableSpace ι]
    (μ:Measure ι)[IsProbabilityMeasure μ](U:ι→End)
    (hp:∀f:QuantumTest,∀z:SourceCoordinateSlice,∀word:Occupation,Continuous (fun x:ι=>U x f z word))
    (hn:∀x:ι,∀f:QuantumTest,‖embed (U x f)‖=‖embed f‖)(p f:QuantumTest):
    Integrable (fun x:ι×SourceCoordinateSlice=>densityPair p (U x.1 f) x.2) (μ.prod config):=by
  have hcont(z:SourceCoordinateSlice):Continuous (fun x:ι=>densityPair p (U x f) z):=by
    simp_rw [densityPair_sum]
    apply continuous_finsetSum
    intro word _
    exact continuous_const.mul (hp f z word)
  have hm:StronglyMeasurable (fun x:ι×SourceCoordinateSlice=>densityPair p (U x.1 f) x.2):=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hcont
      (fun x=>(density_continuous p (U x f)).stronglyMeasurable)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x=>densityPair_integrable p (U x f)),?_⟩
  apply (integrable_const (‖embed p‖^2+‖embed f‖^2:ℝ)).mono'
    hm.norm.integral_prod_right'.aestronglyMeasurable
  exact Eventually.of_forall (fun x=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    simpa only [hn] using density_integral_norm_bound p (U x f))

private theorem profile_norm(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u z,c (combinedMap u z)=c z)(a:ℝ)(f:QuantumTest):
    ‖embed (clockProfileAction c hc hi a f)‖=‖embed f‖:=by
  have h:=congrArg Complex.re (clockProfileAction_pair c hc hi a f f)
  change (inner ℂ (embed (clockProfileAction c hc hi a f)) (embed (clockProfileAction c hc hi a f))).re=
    (inner ℂ (embed f) (embed f)).re at h
  have hself(v:H):(inner ℂ v v).re=‖v‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) v
  rw [hself,hself] at h
  nlinarith [norm_nonneg (embed f),norm_nonneg (embed (clockProfileAction c hc hi a f))]

private theorem strong_comp_continuous(F G:ℝ→End)
    (hF:∀f:QuantumTest,Continuous (fun r:ℝ=>embed (F r f)))
    (hG:∀f:QuantumTest,Continuous (fun r:ℝ=>embed (G r f)))
    (hN:∀r:ℝ,∀f:QuantumTest,‖embed (F r f)‖=‖embed f‖)(f:QuantumTest):
    Continuous (fun p:ℝ×ℝ=>embed (F p.1 (G p.2 f))):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨a,ha,haB⟩:=Metric.continuousAt_iff.mp ((hF (G p.2 f)).continuousAt) (ε/2) (by positivity)
  obtain ⟨b,hb,hbB⟩:=Metric.continuousAt_iff.mp ((hG f).continuousAt) (ε/2) (by positivity)
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro q hq
  change max (dist q.1 p.1) (dist q.2 p.2) < min a b at hq
  have hqa:dist q.1 p.1<a:=(le_max_left _ _).trans_lt ((lt_min_iff.mp hq).1)
  have hqb:dist q.2 p.2<b:=(le_max_right _ _).trans_lt ((lt_min_iff.mp hq).2)
  have he:dist (embed (F q.1 (G q.2 f))) (embed (F q.1 (G p.2 f)))=
      dist (embed (G q.2 f)) (embed (G p.2 f)):=by
    simp only [dist_eq_norm,←map_sub,hN]
  calc
    _≤dist (embed (F q.1 (G q.2 f))) (embed (F q.1 (G p.2 f)))+
        dist (embed (F q.1 (G p.2 f))) (embed (F p.1 (G p.2 f))):=dist_triangle _ _ _
    _<ε/2+ε/2:=by rw [he];exact add_lt_add (hbB hqb) (haB hqa)
    _=ε:=by ring

private def c0(t:ℝ):SourceCoordinateSlice→ℝ:=correctedCoefficient t 0 0
private def cx(t:ℝ)(z:SourceCoordinateSlice):ℝ:=correctedCoefficient t 1 0 z-c0 t z
private def cy(t:ℝ)(z:SourceCoordinateSlice):ℝ:=correctedCoefficient t 0 1 z-c0 t z
private theorem c0_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (c0 t) z.val:=coefficient_smooth t ht 0 0 z
private theorem cx_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (cx t) z.val:=
  (coefficient_smooth t ht 1 0 z).sub (c0_smooth t ht z)
private theorem cy_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (cy t) z.val:=
  (coefficient_smooth t ht 0 1 z).sub (c0_smooth t ht z)
private def P0(t:ℝ)(ht:0<t):End:=clockProfileAction (c0 t) (c0_smooth t ht) (fun _ _=>rfl) 1
private def Px(t:ℝ)(ht:0<t)(a:ℝ):End:=clockProfileAction (cx t) (cx_smooth t ht) (fun _ _=>rfl) a
private def Py(t:ℝ)(ht:0<t)(a:ℝ):End:=clockProfileAction (cy t) (cy_smooth t ht) (fun _ _=>rfl) a
private theorem coefficient_affine(t ξ η:ℝ)(z:SourceCoordinateSlice):
    c0 t z+ξ*cx t z+η*cy t z=correctedCoefficient t ξ η z:=by
  let m:=heatMean t z
  let w:=Real.sqrt (heatVariance t z)
  let a:=Real.cos (clockPhase (heatLog t z))
  let b:=Real.sin (clockPhase (heatLog t z))
  change (m+w*(0*a+0*b))+ξ*((m+w*(1*a+0*b))-(m+w*(0*a+0*b)))+
    η*((m+w*(0*a+1*b))-(m+w*(0*a+0*b)))=m+w*(ξ*a+η*b)
  ring
private theorem combined_add(a b:ℝ)(z:SourceCoordinateSlice):
    combinedMap a (combinedMap b z)=combinedMap (a+b) z:=by
  simp only [combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add]
  congr 2
  congr 1
  ring
private theorem corrected_profile_factor(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    correctedProfileCore t ht ξ η f=P0 t ht (Px t ht ξ (Py t ht η f)):=by
  apply DFunLike.ext
  intro z
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
      f (combinedMap (1*correctedCoefficient t ξ η z) z)=
    (Real.exp ((25/2:ℝ)*(1*c0 t z)):ℂ) •
      ((Real.exp ((25/2:ℝ)*(ξ*cx t z)):ℂ) •
        ((Real.exp ((25/2:ℝ)*(η*cy t z)):ℂ) •
          f (combinedMap (η*cy t z) (combinedMap (ξ*cx t z) (combinedMap (1*c0 t z) z)))))
  simp only [one_mul,smul_smul,←Complex.ofReal_mul,←Real.exp_add,combined_add]
  rw [←coefficient_affine t ξ η z]
  congr 2 <;> congr 1 <;> ring_nf

private theorem corrected_profile_continuous(t:ℝ)(ht:0<t)(f:QuantumTest):
    Continuous (fun x:ℝ×ℝ=>embed (correctedProfileCore t ht x.1 x.2 f)):=by
  let B:QuantumTest→ₗ[ℂ]H:=embed.comp (P0 t ht)
  have hB(q:QuantumTest):‖B q‖≤1*‖embed q‖:=by
    change ‖embed (P0 t ht q)‖≤_
    rw [P0,profile_norm,one_mul]
  have hc:=strong_comp_continuous (Px t ht) (Py t ht)
    (fun q=>clockProfileAction_continuous _ _ _ q)
    (fun q=>clockProfileAction_continuous _ _ _ q)
    (fun a q=>profile_norm _ _ _ a q) f
  have hh:Continuous (fun x:ℝ×ℝ=>SourceClockPhiHeatClosedGraphExtension.boundedOutput B
      (embed (Px t ht x.1 (Py t ht x.2 f)))):=
    (SourceClockPhiHeatClosedGraphExtension.boundedOutput B).continuous.comp hc
  simpa only [SourceClockPhiHeatClosedGraphExtension.bounded_output_on_core B 1 hB,
    B,LinearMap.comp_apply,←corrected_profile_factor] using hh

private theorem forward_norm(t:ℝ)(ht:0≤t)(f:QuantumTest):
    ‖embed (sourceForwardCore t ht f)‖=‖embed f‖:=by
  have h:=congrArg Complex.re (SourceClockPhiCoframeForwardPair.actual_forward_core_pair t ht f f)
  have hself(v:H):(inner ℂ v v).re=‖v‖^2:=inner_self_eq_norm_sq (𝕜:=ℂ) v
  change (inner ℂ (embed (sourceForwardCore t ht f)) (embed (sourceForwardCore t ht f))).re=
    (inner ℂ (embed f) (embed f)).re at h
  rw [hself,hself] at h
  nlinarith [norm_nonneg (embed f),norm_nonneg (embed (sourceForwardCore t ht f))]
private theorem corrected_heat_norm(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    ‖embed (correctedHeatCore t ht ξ η f)‖=‖embed f‖:=by
  change ‖embed (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η f))‖=_
  rw [forward_norm]
  exact profile_norm _ _ _ _ _
private theorem corrected_heat_continuous(t:ℝ)(ht:0<t)(f:QuantumTest):
    Continuous (fun x:ℝ×ℝ=>embed (correctedHeatCore t ht x.1 x.2 f)):=by
  let B:QuantumTest→ₗ[ℂ]H:=embed.comp (sourceForwardCore t ht.le)
  have hB(q:QuantumTest):‖B q‖≤1*‖embed q‖:=by
    change ‖embed (sourceForwardCore t ht.le q)‖≤_
    rw [forward_norm,one_mul]
  have h:Continuous (fun x:ℝ×ℝ=>SourceClockPhiHeatClosedGraphExtension.boundedOutput B
      (embed (correctedProfileCore t ht x.1 x.2 f))):=
    (SourceClockPhiHeatClosedGraphExtension.boundedOutput B).continuous.comp (corrected_profile_continuous t ht f)
  simpa only [SourceClockPhiHeatClosedGraphExtension.bounded_output_on_core B 1 hB,
    B,LinearMap.comp_apply] using! h

theorem actual_corrected_heat_integrable(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>embed (correctedHeatCore t ht x.1 x.2 f)) (γ.prod γ):=by
  let :SecondCountableTopologyEither (ℝ×ℝ) H:=⟨Or.inl inferInstance⟩
  exact (integrable_const (‖embed f‖:ℝ)).mono'
    (corrected_heat_continuous t ht f).aestronglyMeasurable
      (Eventually.of_forall (fun x=>le_of_eq (corrected_heat_norm t ht x.1 x.2 f)))

private def rawPoint(t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(r:ℝ):FockFiber:=
  (Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ) •
    f (combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z)
private theorem rawPoint_continuous(t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):Continuous (rawPoint t f z):=by
  have hm:Continuous (fun r:ℝ=>combinedMap (heatMean t z+Real.sqrt (heatVariance t z)*r) z):=by
    simp only [combinedMap_apply]
    fun_prop
  exact (by fun_prop : Continuous (fun r:ℝ=>(Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r)):ℂ))).smul
    (f.continuous.comp hm)
private theorem rawPoint_integrable(t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):Integrable (rawPoint t f z) γ:=by
  obtain ⟨C,hC⟩:=(f.hasCompactSupport.isCompact_range f.continuous).exists_bound_of_continuousOn continuous_id.continuousOn
  let M:=max C 0
  have hf(v:SourceCoordinateSlice):‖f v‖≤M:=(hC (f v) ⟨v,rfl⟩).trans (le_max_left _ _)
  let a:ℝ:=(25/2:ℝ)*Real.sqrt (heatVariance t z)
  let b:ℝ:=Real.exp ((25/2:ℝ)*heatMean t z)
  have hi:Integrable (fun r:ℝ=>(b*M)*Real.exp (a*r)) γ:=
    (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) a).const_mul (b*M)
  apply hi.mono' (rawPoint_continuous t f z).aestronglyMeasurable
  exact Eventually.of_forall (fun r=>by
    rw [rawPoint,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he:Real.exp ((25/2:ℝ)*(heatMean t z+Real.sqrt (heatVariance t z)*r))=b*Real.exp (a*r):=by
      dsimp only [a,b]
      rw [←Real.exp_add]
      congr 1
      ring
    rw [he]
    calc _≤(b*Real.exp (a*r))*M:=mul_le_mul_of_nonneg_left (hf _) (by dsimp [b];positivity)
         _=(b*M)*Real.exp (a*r):=by ring)
private theorem corrected_profile_raw_point(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    correctedProfileCore t ht x.1 x.2 f z=
      rawPoint t f z (x.1*Real.cos (clockPhase (heatLog t z))+x.2*Real.sin (clockPhase (heatLog t z))):=by
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t x.1 x.2 z)):ℂ) •
    f (combinedMap (1*correctedCoefficient t x.1 x.2 z) z)=_
  simp only [one_mul]
  rfl
private theorem corrected_profile_point_continuous(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Continuous (fun x:ℝ×ℝ=>correctedProfileCore t ht x.1 x.2 f z):=by
  simp only [corrected_profile_raw_point]
  exact (rawPoint_continuous t f z).comp (by fun_prop)
private theorem corrected_profile_point_integrable(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun x:ℝ×ℝ=>correctedProfileCore t ht x.1 x.2 f z) (γ.prod γ):=by
  let θ:=clockPhase (heatLog t z)
  have hi:Integrable (rawPoint t f z) ((γ.prod γ).map (fun x:ℝ×ℝ=>x.1*Real.cos θ+x.2*Real.sin θ)):=by
    rw [rotated_scalar_law]
    exact rawPoint_integrable t f z
  have h:Integrable (fun x:ℝ×ℝ=>rawPoint t f z (x.1*Real.cos θ+x.2*Real.sin θ)) (γ.prod γ):=
    (integrable_map_measure (rawPoint_continuous t f z).aestronglyMeasurable (by fun_prop)).mp hi
  simpa only [corrected_profile_raw_point,θ] using h

private def forwardFiber(t:ℝ)(z:SourceCoordinateSlice):FockFiber→L[ℂ]FockFiber:=
  if 18*t<volume z then GaussFockWeights.weight (fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ)) else 0
private theorem corrected_forward_point(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    correctedHeatCore t ht x.1 x.2 f z=
      forwardFiber t z (correctedProfileCore t ht x.1 x.2 f (backwardPoint t z)):=by
  apply PiLp.ext
  intro word
  change (forwardValue t (correctedProfileCore t ht x.1 x.2 f) z) word=_
  by_cases ha:18*t<volume z
  · simp only [forwardValue,forwardFiber,if_pos ha,GaussFockWeights.weight_apply]
  · simp only [forwardValue,forwardFiber,if_neg ha,zero_apply]
private theorem original_forward_point(t:ℝ)(ht:0<t)(r:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    sourceHeatCore t ht r f z=forwardFiber t z (rawPoint t f (backwardPoint t z) r):=by
  apply PiLp.ext
  intro word
  change (forwardValue t _ z) word=_
  by_cases ha:18*t<volume z
  · simp only [forwardValue,forwardFiber,if_pos ha,GaussFockWeights.weight_apply]
    change (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
      ((Real.exp ((25/2:ℝ)*(1*(heatMean t (backwardPoint t z)+Real.sqrt (heatVariance t (backwardPoint t z))*r))):ℂ) •
        f (combinedMap (1*(heatMean t (backwardPoint t z)+Real.sqrt (heatVariance t (backwardPoint t z))*r))
          (backwardPoint t z))) word=_
    simp only [one_mul]
    rfl
  · simp only [forwardValue,forwardFiber,if_neg ha,zero_apply]
private theorem corrected_heat_point_continuous(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Continuous (fun x:ℝ×ℝ=>correctedHeatCore t ht x.1 x.2 f z):=by
  simp only [corrected_forward_point]
  exact (forwardFiber t z).continuous.comp (corrected_profile_point_continuous t ht f _)
private theorem original_heat_point_continuous(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Continuous (fun r:ℝ=>sourceHeatCore t ht r f z):=by
  simp only [original_forward_point]
  exact (forwardFiber t z).continuous.comp (rawPoint_continuous t f _)
private theorem corrected_heat_point_integrable(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun x:ℝ×ℝ=>correctedHeatCore t ht x.1 x.2 f z) (γ.prod γ):=by
  simp only [corrected_forward_point]
  exact (forwardFiber t z).integrable_comp (corrected_profile_point_integrable t ht f _)
private theorem original_heat_point_integrable(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    Integrable (fun r:ℝ=>sourceHeatCore t ht r f z) γ:=by
  simp only [original_forward_point]
  exact (forwardFiber t z).integrable_comp (rawPoint_integrable t f _)
private theorem corrected_heat_mean_fiber(t:ℝ)(ht:0<t)(f:QuantumTest)(z:SourceCoordinateSlice):
    (∫x:ℝ×ℝ,correctedHeatCore t ht x.1 x.2 f z ∂γ.prod γ)=∫r:ℝ,sourceHeatCore t ht r f z ∂γ:=by
  apply PiLp.ext
  intro word
  rw [eval_integral_piLp (fun w=>(corrected_heat_point_integrable t ht f z).eval_piLp w),
    eval_integral_piLp (fun w=>(original_heat_point_integrable t ht f z).eval_piLp w)]
  exact actual_corrected_heat_mean_point t ht f z word

private theorem corrected_heat_weak_mean(t:ℝ)(ht:0<t)(p f:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair p (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ)=
      ∫r:ℝ,sourcePair p (sourceHeatCore t ht r f) ∂γ:=by
  have hC:=joint_density_integrable (γ.prod γ) (fun x:ℝ×ℝ=>correctedHeatCore t ht x.1 x.2)
    (fun q z word=>(PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp
      (corrected_heat_point_continuous t ht q z)) (fun x q=>corrected_heat_norm t ht x.1 x.2 q) p f
  have hO:=joint_density_integrable γ (fun r:ℝ=>sourceHeatCore t ht r)
    (fun q z word=>(PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp
      (original_heat_point_continuous t ht q z)) (fun r q=>sourceHeat_norm t ht r q) p f
  simp_rw [sourcePair_integral]
  rw [integral_integral_swap (μ:=γ.prod γ) (ν:=config)
      (f:=fun (x:ℝ×ℝ) (z:SourceCoordinateSlice)=>densityPair p (correctedHeatCore t ht x.1 x.2 f) z) hC,
    integral_integral_swap (μ:=γ) (ν:=config)
      (f:=fun (r:ℝ) (z:SourceCoordinateSlice)=>densityPair p (sourceHeatCore t ht r f) z) hO]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z=>by
    dsimp only [densityPair]
    rw [integral_inner (𝕜:=ℂ) (corrected_heat_point_integrable t ht f z),
      integral_inner (𝕜:=ℂ) (original_heat_point_integrable t ht f z),corrected_heat_mean_fiber])

theorem actual_corrected_heat_mean_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    (∫x:ℝ×ℝ,embed (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ)=heatOperator t ht (embed f):=by
  apply SourceCoframeScaleTransport.embed_dense.eq_of_inner_right ℂ
  intro p
  rw [←integral_inner (actual_corrected_heat_integrable t ht f),actual_heat_operator_core]
  change (∫x:ℝ×ℝ,sourcePair p (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ)=
    inner ℂ (embed p) (∫r:ℝ,embed (sourceHeatCore t ht r f) ∂γ)
  rw [←integral_inner (sourceHeat_integrable t ht f)]
  exact corrected_heat_weak_mean t ht p f

theorem actual_corrected_complete_mean_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>embed (correctedCompleteCore t ht x.1 x.2 f)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)=
      heatOperator t ht (embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)):=
  ⟨actual_corrected_heat_integrable t ht _,actual_corrected_heat_mean_source t ht _⟩

private abbrev A:=SourceClockPhiCombinedScalePressure.combinedConjugate
private theorem corrected_mean_A_pair(t:ℝ)(ht:0<t)(f h:QuantumTest):
    inner ℂ (∫x:ℝ×ℝ,embed (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ) (embed (A h))=
      -inner ℂ (heatAReader t ht (embed f)) (embed h):=by
  rw [actual_corrected_heat_mean_source]
  have hA:=((actual_heat_native_smoothing t ht).2.2.2.2 (embed f)).2.1.1
  have hp:=SymmetricGraphClosure.closed_graph_pairing (realize A) (realize (-A))
    SourceClockPhiHeatNativeClosedGraph.actual_A_formal_pair hA (coreEquiv h)
  change inner ℂ (heatAReader t ht (embed f)) (embed h)=
    inner ℂ (heatOperator t ht (embed f)) (embed (-A (coreEquiv.symm (coreEquiv h)))) at hp
  rw [coreEquiv.symm_apply_apply,map_neg,inner_neg_right] at hp
  have hh:=congrArg Neg.neg hp
  simpa only [neg_neg] using hh.symm

theorem actual_corrected_mean_A_squared_source(t:ℝ)(ht:0<t)(f:QuantumTest):
    ((∫x:ℝ×ℝ,embed (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ),
      ClockPhiHeatSecondNativeSource.heatASecondReader t ht (embed f))∈
        SymmetricGraphClosure.closedGraph (realize (A*A)) ∧
    ∀h:QuantumTest,
      inner ℂ (∫x:ℝ×ℝ,embed (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ) (embed ((A*A) h))=
        inner ℂ (ClockPhiHeatSecondNativeSource.heatASecondReader t ht (embed f)) (embed h):=by
  have hS:=(ClockPhiHeatSecondNativeSource.actual_heat_second_native_source t ht).2 (embed f)
  constructor
  · rw [actual_corrected_heat_mean_source]
    exact hS.1
  · intro h
    change inner ℂ _ (embed (A (A h)))=_
    rw [corrected_mean_A_pair,(hS.2.2 h),neg_neg]

open GaussDiagonalHistory GaussUnitaryHistory SourceLocalizedInverseFormPayment
open SourceClockPhiNormalizedScalarBudget ClockPhiMatchedGainFrequencyPayment
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    (actualFrequency advanced μ freq).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'

theorem actual_corrected_mean_physical_frequency_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,∀t:ℝ,∀ht:0<t,
      (∫⁻freq:ℝ,ENNReal.ofReal (t*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedHeatCore t ht x.1 x.2
          (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)) ∂γ.prod γ)
        (embed ((A*A) (shiftedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)))‖))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=ClockPhiHeatSecondNativeSource.actual_heat_physical_frequency_common_payment μ hμ g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced t ht
  simpa only [Module.End.mul_apply,corrected_mean_A_pair,norm_neg] using hF advanced t ht

private theorem complete_mean_second_price(t:ℝ)(ht:0<t)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖≤
      ‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖*‖embed h‖:=by
  let v:=embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  let B:=ClockPhiHeatSecondNativeSource.heatASecondReader t ht
  have he:inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))=inner ℂ (B v) (embed h):=
    (actual_corrected_mean_A_squared_source t ht (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).2 h
  have hn:‖B v‖≤(1/t)*‖v‖:=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (ClockPhiHeatSecondNativeSource.actual_heat_second_native_source t ht).1 (norm_nonneg _))
  have hb:t*‖B v‖≤‖v‖:=by
    calc _≤t*((1/t)*‖v‖):=mul_le_mul_of_nonneg_left hn ht.le
         _=‖v‖:=by field_simp [ht.ne']
  rw [he]
  calc
    _≤t*(‖B v‖*‖embed h‖):=mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ht.le
    _=(t*‖B v‖)*‖embed h‖:=by ring
    _≤‖v‖*‖embed h‖:=mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem complete_mean_small_time_price(t:ℝ)(ht:0<t)(ht1:t≤1)(η:ℝ)(hη:0<η)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖≤η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+
        2*η*‖embed f‖^2+‖embed h‖^2/(4*η):=by
  let G:=‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖
  let H:=‖embed h‖
  have hG:=SourceClockPhiCompleteHeatGainPayment.actual_complete_heat_gain_payment t ht 1 (by norm_num) 0 f
  change ‖embed (sourceHeatCore t ht 0 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))‖^2≤_ at hG
  rw [sourceHeat_norm] at hG
  have hG':G^2≤SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+2*‖embed f‖^2:=by
    dsimp only [G]
    norm_num only [one_mul,div_one] at hG
    have ht2:t^2≤1:=by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg ‖embed f‖)]
  have hy:G*H≤η*G^2+H^2/(4*η):=by
    have he:(4*η)*(η*G^2+H^2/(4*η))=4*η^2*G^2+H^2:=by
      field_simp [hη.ne']
    have hh:(4*η)*(G*H)≤(4*η)*(η*G^2+H^2/(4*η)):=by
      rw [he]
      nlinarith [sq_nonneg (2*η*G-H)]
    exact (mul_le_mul_iff_right₀ (by positivity:0<4*η)).mp hh
  have he:=mul_le_mul_of_nonneg_left hG' hη.le
  have hP:=complete_mean_second_price t ht f h
  change _≤G*H at hP
  dsimp only [H] at hy
  nlinarith

private theorem frequency_norm_floor(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    μ≤‖actualFrequency advanced μ freq‖:=by
  have h:=Complex.abs_im_le_norm (actualFrequency advanced μ freq)
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,abs_neg,abs_of_pos hμ] using h

private theorem complete_mean_source_price(t:ℝ)(ht:0<t)(ht1:t≤1)(η μ:ℝ)(hη:0<η)(hμ:0<μ)
    (z:ℂ)(hz:μ≤‖z‖)(f h:QuantumTest)(he:z • f=h):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖-η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f≤
        (2*η/μ^2+1/(4*η))*‖embed h‖^2:=by
  have hn:‖embed h‖=‖z‖*‖embed f‖:=by rw [←he,map_smul,norm_smul]
  have hF:μ*‖embed f‖≤‖embed h‖:=by
    rw [hn]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hsq:‖embed f‖^2≤‖embed h‖^2/μ^2:=by
    apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
    have hh:=mul_self_le_mul_self (by positivity:0≤μ*‖embed f‖) hF
    nlinarith only [hh]
  have hp:=complete_mean_small_time_price t ht ht1 η hη f h
  have hmul:=mul_le_mul_of_nonneg_left hsq (by positivity:0≤2*η)
  have heq:2*η*(‖embed h‖^2/μ^2)+‖embed h‖^2/(4*η)=
      (2*η/μ^2+1/(4*η))*‖embed h‖^2:=by ring
  linarith only [hp,hmul,heq]

theorem actual_corrected_complete_mean_physical_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,∀t:ℝ,∀ht:0<t,t≤1→
      (∫⁻freq:ℝ,ENNReal.ofReal (t*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2
          (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)) ∂γ.prod γ)
        (embed ((A*A) (shiftedState m ell F (actualFrequency advanced μ freq)
          (frequency_nonreal advanced μ hμ freq) g)))‖-
        η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
          (normalizedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)))≤ENNReal.ofReal ε:=by
  intro ε hε
  let C:ℝ:=2*η/μ^2+1/(4*η)
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced t ht ht1
  calc
    _≤∫⁻freq:ℝ,ENNReal.ofReal C*ENNReal.ofReal
      (‖embed (shiftedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)‖^2):=by
      apply lintegral_mono
      intro freq
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (complete_mean_source_price t ht ht1 η μ hη hμ _
        (frequency_norm_floor advanced μ hμ freq) _ _
        (hS m ell _ (frequency_nonreal advanced μ hμ freq)).1)
    _=ENNReal.ofReal C*(∫⁻freq:ℝ,ENNReal.ofReal
      (‖embed (shiftedState m ell F (actualFrequency advanced μ freq) (frequency_nonreal advanced μ hμ freq) g)‖^2)):=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)):=mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _≤ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      exact (div_le_iff₀ (by positivity:C+1>0)).mpr (by nlinarith)

end LowEnergy.ClockPhiCorrectedGaussianMeanSource
