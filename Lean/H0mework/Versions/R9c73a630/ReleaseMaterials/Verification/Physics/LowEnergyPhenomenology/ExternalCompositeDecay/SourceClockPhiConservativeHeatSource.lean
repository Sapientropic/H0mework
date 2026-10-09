import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardPair
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Convex.Integral
import H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianComplexIBP
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClockPrice
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCoefficientProduct
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatClosedGraphExtension
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeClosedGraph
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusNormalizedFluxBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiConservativeHeatSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare
open ClockPhiMatchedNoiseCore SourceClockPhiCoframeForwardCore SourceClockPhiCoframeForwardPair
open SourceClockPhiCombinedScalePressure MeasureTheory Set Filter
open SourceClockPhiForwardNativeReturn
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private structure ClockProfile where
  value:SourceCoordinateSlice→ℝ
  smooth:∀z:physicalChart,ContDiffAt ℝ ∞ value z.val
  invariant:∀t:ℝ,∀z:SourceCoordinateSlice,value (combinedMap t z)=value z
private theorem combined_zero(z:SourceCoordinateSlice):combinedMap 0 z=z:=by
  simp only [combinedMap_apply,Real.exp_zero,neg_zero,one_smul,add_sub_cancel_right]
private theorem combined_add(t s:ℝ)(z:SourceCoordinateSlice):combinedMap t (combinedMap s z)=combinedMap (t+s) z:=by
  simp only [combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add]
  congr 2
  congr 1
  ring
private theorem combined_chart(t:ℝ)(z:SourceCoordinateSlice):combinedMap t z∈physicalChart ↔ z∈physicalChart:=
  (SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-t)) (Real.exp_pos _)
    (SourceScalarAffineScaleTransport.scaleEquiv t z)).trans
      (SourceScalarAffineScaleTransport.scale_chart_iff t z)
private theorem combined_smooth:ContDiff ℝ ∞ (fun p:ℝ×SourceCoordinateSlice=>combinedMap p.1 p.2):=by
  simp only [combinedMap_apply]
  fun_prop
private def profileMap(c:ClockProfile)(α:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (α*c.value z) z
private theorem profileMap_add(c:ClockProfile)(α β:ℝ)(z:SourceCoordinateSlice):
    profileMap c α (profileMap c β z)=profileMap c (α+β) z:=by
  simp only [profileMap,c.invariant,combined_add,add_mul]
private theorem profileMap_zero(c:ClockProfile)(z:SourceCoordinateSlice):profileMap c 0 z=z:=by
  simp only [profileMap,zero_mul,combined_zero]
private theorem profileMap_inverse(c:ClockProfile)(α:ℝ)(z:SourceCoordinateSlice):
    profileMap c (-α) (profileMap c α z)=z:=by
  rw [profileMap_add,neg_add_cancel,profileMap_zero]
private theorem profileMap_chart(c:ClockProfile)(α:ℝ)(z:SourceCoordinateSlice):
    profileMap c α z∈physicalChart ↔ z∈physicalChart:=combined_chart _ _
private theorem profileMap_smooth(c:ClockProfile)(α:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (profileMap c α) z.val:=by
  have hp:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(α*c.value x,x)) z.val:=
    (contDiffAt_const.mul (c.smooth z)).prodMk contDiffAt_id
  have hc:=combined_smooth.contDiffAt (x:=(α*c.value z.val,z.val))
  exact ContDiffAt.comp (f:=fun x:SourceCoordinateSlice=>(α*c.value x,x)) z.val hc hp
private def profileValue(c:ClockProfile)(α:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):FockFiber:=
  (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) • f (profileMap c α z)
private def profileSupport(c:ClockProfile)(α:ℝ)(f:QuantumTest):Set SourceCoordinateSlice:=
  profileMap c (-α) '' tsupport f
private theorem profileSupport_compact(c:ClockProfile)(α:ℝ)(f:QuantumTest):IsCompact (profileSupport c α f):=by
  apply f.hasCompactSupport.image_of_continuousOn
  intro z hz
  exact (profileMap_smooth c (-α) ⟨z,f.tsupport_subset hz⟩).continuousAt.continuousWithinAt
private theorem profileSupport_chart(c:ClockProfile)(α:ℝ)(f:QuantumTest):profileSupport c α f⊆physicalChart:=by
  rintro z ⟨x,hx,rfl⟩
  exact (profileMap_chart c (-α) x).mpr (f.tsupport_subset hx)
private theorem profile_support(c:ClockProfile)(α:ℝ)(f:QuantumTest):tsupport (profileValue c α f)⊆profileSupport c α f:=by
  apply closure_minimal _ (profileSupport_compact c α f).isClosed
  intro z hz
  have hf:f (profileMap c α z)≠0:=by
    intro h
    exact hz (by simp only [profileValue,h,smul_zero])
  exact ⟨profileMap c α z,subset_tsupport f hf,profileMap_inverse c α z⟩
private theorem profile_smooth(c:ClockProfile)(α:ℝ)(f:QuantumTest):ContDiff ℝ ∞ (profileValue c α f):=by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz:z∈profileSupport c α f
  · have hp:=c.smooth ⟨z,profileSupport_chart c α f hz⟩
    have hm:=profileMap_smooth c α ⟨z,profileSupport_chart c α f hz⟩
    have he:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(Real.exp ((25/2:ℝ)*(α*c.value x)):ℂ)) z:=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z ((contDiffAt_const.mul (contDiffAt_const.mul hp)).exp)
    exact he.smul (f.contDiff.contDiffAt.comp z hm)
  · apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [(profileSupport_compact c α f).isClosed.isOpen_compl.mem_nhds hz] with x hx
    exact image_eq_zero_of_notMem_tsupport (fun h=>hx (profile_support c α f h))
private def profileCore(c:ClockProfile)(α:ℝ):End where
  toFun f:=
    {toFun:=profileValue c α f
     contDiff':=profile_smooth c α f
     hasCompactSupport':=(profileSupport_compact c α f).of_isClosed_subset isClosed_closure (profile_support c α f)
     tsupport_subset':=(profile_support c α f).trans (profileSupport_chart c α f)}
  map_add' f g:=by
    apply DFunLike.ext;intro z
    exact smul_add _ _ _
  map_smul' a f:=by
    apply DFunLike.ext;intro z
    change (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) • (a • f (profileMap c α z))=_
    exact smul_comm _ _ _
private theorem profileCore_zero(c:ClockProfile)(f:QuantumTest):profileCore c 0 f=f:=by
  apply DFunLike.ext;intro z
  change profileValue c 0 f z=f z
  simp only [profileValue,zero_mul,mul_zero,Real.exp_zero,Complex.ofReal_one,one_smul,profileMap_zero]
private theorem profileCore_add(c:ClockProfile)(α β:ℝ)(f:QuantumTest):
    profileCore c α (profileCore c β f)=profileCore c (α+β) f:=by
  apply DFunLike.ext;intro z
  change (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) •
    ((Real.exp ((25/2:ℝ)*(β*c.value (profileMap c α z))):ℂ) • f (profileMap c β (profileMap c α z)))=_
  simp only [profileMap,c.invariant,combined_add,smul_smul,←Complex.ofReal_mul,←Real.exp_add]
  congr 2
  · congr 1
    ring
  · congr 1
    ring
private def profileCoefficient(c:ClockProfile)(z:SourceCoordinateSlice):ℝ:=c.value z*GaussNativeEnergy.volume z
private theorem profileCoefficient_smooth(c:ClockProfile)(z:physicalChart):
    ContDiffAt ℝ ∞ (profileCoefficient c) z.val:=(c.smooth z).mul GaussNativeEnergy.volume_smooth.contDiffAt
private def profileGenerator(c:ClockProfile):End:=
  multiply (profileCoefficient c) (profileCoefficient_smooth c)*noiseGenerator 0 1
private theorem profile_multiply_commute(c:ClockProfile):
    Commute (noiseGenerator 0 1) (multiply (profileCoefficient c) (profileCoefficient_smooth c)):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  let M:=multiply (profileCoefficient c) (profileCoefficient_smooth c)
  have he:(fun u:ℝ=>noiseCore 0 u (M f) z word)=fun u:ℝ=>M (noiseCore 0 u f) z word:=by
    funext u
    have h:=noise_real_multiplier 0 u (profileCoefficient c) (profileCoefficient_smooth c) (fun x=>by
      change c.value (combinedMap _ x)*GaussNativeEnergy.volume x=c.value x*GaussNativeEnergy.volume x
      rw [c.invariant])
    exact congrArg (fun T:End=>T f z word) h.eq
  have h1:=noise_linear_zero_jet 0 1 (M f) z word
  have h1':HasDerivAt (fun u:ℝ=>noiseCore 0 u (M f) z word) (noiseGenerator 0 1 (M f) z word) 0:=by
    simpa only [mul_zero,mul_one] using! h1
  rw [he] at h1'
  have h2:HasDerivAt (fun u:ℝ=>M (noiseCore 0 u f) z word) (M (noiseGenerator 0 1 f) z word) 0:=by
    have h:=(noise_linear_zero_jet 0 1 f z word).const_mul (profileCoefficient c z:ℂ)
    simpa only [mul_zero,mul_one] using! h
  exact h1'.unique h2
private theorem profile_generator_pair(c:ClockProfile)(f g:QuantumTest):
    sourcePair f (profileGenerator c g)= -sourcePair (profileGenerator c f) g:=by
  change sourcePair f (multiply (profileCoefficient c) (profileCoefficient_smooth c) (noiseGenerator 0 1 g))=
    -sourcePair (multiply (profileCoefficient c) (profileCoefficient_smooth c) (noiseGenerator 0 1 f)) g
  rw [multiply_pair,noiseGenerator_pair]
  have h:=LinearMap.congr_fun (profile_multiply_commute c).eq f
  simpa only [Module.End.mul_apply] using congrArg (fun q:QuantumTest=> -sourcePair q g) h

private theorem profile_point(c:ClockProfile)(u:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    profileCore c u f z=noiseCore 0 (u*profileCoefficient c z) f z:=by
  by_cases hz:z∈physicalChart
  · have hp:parameter 0 (u*profileCoefficient c z) z=u*c.value z:=by
      unfold parameter profileCoefficient reciprocalVolume
      simp only [zero_mul,zero_add]
      field_simp [(GaussNativeEnergy.volume_pos ⟨z,hz⟩).ne']
    change (Real.exp ((25/2:ℝ)*(u*c.value z)):ℂ) • f (combinedMap (u*c.value z) z)=
      (Real.exp ((25/2:ℝ)*parameter 0 (u*profileCoefficient c z) z):ℂ) •
        f (combinedMap (parameter 0 (u*profileCoefficient c z) z) z)
    rw [hp]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem profile_generator_point(c:ClockProfile)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    noiseGenerator 0 (profileCoefficient c z) f z word=profileGenerator c f z word:=by
  simp only [profileGenerator,noiseGenerator,Complex.ofReal_zero,zero_smul,zero_add,Complex.ofReal_one,one_smul]
  rfl
private theorem profile_zero_jet(c:ClockProfile)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    HasDerivAt (fun u:ℝ=>profileCore c u f z word) (profileGenerator c f z word) 0:=by
  have h:=noise_linear_zero_jet 0 (profileCoefficient c z) f z word
  rw [profile_generator_point] at h
  simpa only [mul_zero,profile_point] using! h
private theorem profile_generator_flow(c:ClockProfile)(α:ℝ)(f:QuantumTest):
    profileGenerator c (profileCore c α f)=profileCore c α (profileGenerator c f):=by
  apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  have h1:=profile_zero_jet c (profileCore c α f) z word
  have h2:HasDerivAt (fun u:ℝ=>profileCore c α (profileCore c u f) z word)
      (profileCore c α (profileGenerator c f) z word) 0:=
    (profile_zero_jet c f (profileMap c α z) word).const_mul (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ)
  have he:(fun u:ℝ=>profileCore c u (profileCore c α f) z word)=
      fun u:ℝ=>profileCore c α (profileCore c u f) z word:=by
    funext u
    rw [profileCore_add,profileCore_add,add_comm u α]
  rw [he] at h1
  exact h1.unique h2
private theorem profile_jet(c:ClockProfile)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation)(α:ℝ):
    HasDerivAt (fun u:ℝ=>profileCore c u f z word) (profileCore c α (profileGenerator c f) z word) α:=by
  have h0:=profile_zero_jet c (profileCore c α f) z word
  rw [profile_generator_flow] at h0
  have h:=h0.scomp_of_eq α ((hasDerivAt_id α).sub_const α) (by simp)
  apply (h.congr_deriv (by simp only [one_smul])).congr_of_eventuallyEq
  exact Eventually.of_forall (fun u=>by simp only [Function.comp_def,id_eq,profileCore_add,sub_add_cancel])
private theorem profile_joint_map_smooth(c:ClockProfile)(p:ℝ×SourceCoordinateSlice)(hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>profileMap c q.1 q.2) p:=by
  have hc:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>c.value q.2) p:=
    ContDiffAt.comp (f:=fun q:ℝ×SourceCoordinateSlice=>q.2) p (c.smooth ⟨p.2,hp⟩) contDiffAt_snd
  have hi:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>(q.1*c.value q.2,q.2)) p:=
    (contDiffAt_fst.mul hc).prodMk contDiffAt_snd
  exact ContDiffAt.comp (f:=fun q:ℝ×SourceCoordinateSlice=>(q.1*c.value q.2,q.2)) p
    (combined_smooth.contDiffAt (x:=(p.1*c.value p.2,p.2))) hi
private def profileCommon(c:ClockProfile)(lo hi:ℝ)(f:QuantumTest):Set SourceCoordinateSlice:=
  (fun p:ℝ×SourceCoordinateSlice=>profileMap c (-p.1) p.2) '' (Icc lo hi×ˢtsupport f)
private theorem profileCommon_compact(c:ClockProfile)(lo hi:ℝ)(f:QuantumTest):IsCompact (profileCommon c lo hi f):=by
  apply (isCompact_Icc.prod f.hasCompactSupport).image_of_continuousOn
  intro p hp
  have h:=profile_joint_map_smooth c (-p.1,p.2) (f.tsupport_subset hp.2)
  have hn:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>(-q.1,q.2)) p:=by fun_prop
  exact (ContDiffAt.comp (f:=fun q:ℝ×SourceCoordinateSlice=>(-q.1,q.2)) p h hn).continuousAt.continuousWithinAt
private theorem profileCommon_chart(c:ClockProfile)(lo hi:ℝ)(f:QuantumTest):profileCommon c lo hi f⊆physicalChart:=by
  rintro z ⟨p,hp,rfl⟩
  exact (profileMap_chart c (-p.1) p.2).mpr (f.tsupport_subset hp.2)
private theorem profile_common_support(c:ClockProfile)(lo hi u:ℝ)(f:QuantumTest)(hu:u∈Icc lo hi):
    tsupport (profileCore c u f)⊆profileCommon c lo hi f:=by
  intro z hz
  rcases profile_support c u f hz with ⟨x,hx,rfl⟩
  exact ⟨(u,x),⟨hu,hx⟩,rfl⟩
private theorem profile_joint_smooth(c:ClockProfile)(f:QuantumTest):
    ContDiff ℝ ∞ (fun p:ℝ×SourceCoordinateSlice=>profileCore c p.1 f p.2):=by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp:p.2∈physicalChart
  · have hc:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>c.value q.2) p:=
      ContDiffAt.comp (f:=fun q:ℝ×SourceCoordinateSlice=>q.2) p (c.smooth ⟨p.2,hp⟩) contDiffAt_snd
    have ha:ContDiffAt ℝ ∞ (fun q:ℝ×SourceCoordinateSlice=>(Real.exp ((25/2:ℝ)*(q.1*c.value q.2)):ℂ)) p:=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p ((contDiffAt_const.mul (contDiffAt_fst.mul hc)).exp)
    exact ha.smul (f.contDiff.contDiffAt.comp p (profile_joint_map_smooth c p hp))
  · let K:=profileCommon c (p.1-1) (p.1+1) f
    have hK:IsCompact K:=profileCommon_compact c _ _ f
    have hz:p.2∉K:=fun h=>hp (profileCommon_chart c _ _ f h)
    have hu:{q:ℝ×SourceCoordinateSlice|q.1∈Ioo (p.1-1) (p.1+1)}∈𝓝 p:=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds (by constructor <;> linarith)
    have hk:{q:ℝ×SourceCoordinateSlice|q.2∉K}∈𝓝 p:=
      (hK.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hz
    apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [hu,hk] with q hq hk
    exact image_eq_zero_of_notMem_tsupport (fun h=>hk
      (profile_common_support c (p.1-1) (p.1+1) q.1 f ⟨hq.1.le,hq.2.le⟩ h))

private theorem density_continuous(N:ℕ):Continuous (GaussDensityCore.complexDensity N):=by
  have hg:Continuous (fun z:SourceCoordinateSlice=>(z.2.2:SourceQuantumConfigurationHilbert.Gauge)):=by fun_prop
  have hv:Continuous (fun z:SourceCoordinateSlice=>z.1 0*z.1 2*z.1 5):=by fun_prop
  exact Complex.continuous_ofReal.comp ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))
private theorem profile_component_continuous(c:ClockProfile)(f:QuantumTest)(word:Occupation):
    Continuous (fun p:ℝ×SourceCoordinateSlice=>profileCore c p.1 f p.2 word):=
  (PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous.comp (profile_joint_smooth c f).continuous
private def pairKernel(c:ClockProfile)(f g:QuantumTest)(t:ℝ)(z:SourceCoordinateSlice):ℂ:=
  densityPair (profileCore c t f) (profileCore c t g) z
private theorem pairKernel_continuous(c:ClockProfile)(f g:QuantumTest):
    Continuous (fun p:ℝ×SourceCoordinateSlice=>pairKernel c f g p.1 p.2):=by
  have he:(fun p:ℝ×SourceCoordinateSlice=>pairKernel c f g p.1 p.2)=
      fun p=>∑word:Occupation,GaussDensityCore.complexDensity word.card p.2*
        star (profileCore c p.1 f p.2 word)*profileCore c p.1 g p.2 word:=by
    funext p
    exact densityPair_sum _ _ _
  rw [he]
  apply continuous_finsetSum
  intro word _
  exact (((density_continuous word.card).comp continuous_snd).mul
    (profile_component_continuous c f word).star).mul (profile_component_continuous c g word)
private theorem pairKernel_derivative(c:ClockProfile)(f g:QuantumTest)(z:SourceCoordinateSlice)(t:ℝ):
    HasDerivAt (fun u:ℝ=>pairKernel c f g u z)
      (pairKernel c (profileGenerator c f) g t z+pairKernel c f (profileGenerator c g) t z) t:=by
  have hw(word:Occupation):HasDerivAt
      (fun u:ℝ=>GaussDensityCore.complexDensity word.card z*
        star (profileCore c u f z word)*profileCore c u g z word)
      (GaussDensityCore.complexDensity word.card z*
        star (profileCore c t (profileGenerator c f) z word)*profileCore c t g z word+
       GaussDensityCore.complexDensity word.card z*
        star (profileCore c t f z word)*profileCore c t (profileGenerator c g) z word) t:=by
    have hf:=profile_jet c f z word t
    have hg:=profile_jet c g z word t
    have h:=((hf.star).const_mul (GaussDensityCore.complexDensity word.card z)).mul hg
    exact h.congr_deriv (by ring)
  have h:=HasDerivAt.sum (u:=(Finset.univ:Finset Occupation)) (fun word _=>hw word)
  have hd:(∑word:Occupation,
      (GaussDensityCore.complexDensity word.card z*
        star (profileCore c t (profileGenerator c f) z word)*profileCore c t g z word+
       GaussDensityCore.complexDensity word.card z*
        star (profileCore c t f z word)*profileCore c t (profileGenerator c g) z word))=
      pairKernel c (profileGenerator c f) g t z+pairKernel c f (profileGenerator c g) t z:=by
    rw [Finset.sum_add_distrib]
    simp only [pairKernel,densityPair_sum]
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Eventually.of_forall (fun u=>by
    dsimp only
    simp only [Finset.sum_apply]
    exact densityPair_sum _ _ _)
private theorem pairKernel_zero(c:ClockProfile)(f g:QuantumTest)(t:ℝ)(z:SourceCoordinateSlice)
    (hz:z∉tsupport (profileCore c t f)):pairKernel c f g t z=0:=by
  unfold pairKernel densityPair
  rw [image_eq_zero_of_notMem_tsupport hz,map_zero,inner_zero_left]
private theorem profile_pair_derivative(c:ClockProfile)(f g:QuantumTest)(t:ℝ):
    HasDerivAt (fun u:ℝ=>sourcePair (profileCore c u f) (profileCore c u g)) 0 t:=by
  let K:Set SourceCoordinateSlice:=profileCommon c (t-1) (t+1) f∪profileCommon c (t-1) (t+1) (profileGenerator c f)
  have hK:IsCompact K:=(profileCommon_compact c _ _ f).union (profileCommon_compact c _ _ (profileGenerator c f))
  let F:=pairKernel c f g
  let F':=fun u z=>pairKernel c (profileGenerator c f) g u z+pairKernel c f (profileGenerator c g) u z
  have hcont:Continuous (fun p:ℝ×SourceCoordinateSlice=>F' p.1 p.2):=
    (pairKernel_continuous c (profileGenerator c f) g).add (pairKernel_continuous c f (profileGenerator c g))
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hcont.continuousOn:ContinuousOn (fun p:ℝ×SourceCoordinateSlice=>F' p.1 p.2) (Icc (t-1) (t+1)×ˢK))
  let bound:SourceCoordinateSlice→ℝ:=K.indicator (fun _=>C)
  have hbound:Integrable bound GaussHistoryHilbert.configurationMeasure:=
    (integrableOn_const (μ:=GaussHistoryHilbert.configurationMeasure) (C:=C) hK.measure_ne_top).integrable_indicator hK.isClosed.measurableSet
  have hd:=hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=GaussHistoryHilbert.configurationMeasure) (F:=F) (F':=F') (bound:=bound)
    (Ioo_mem_nhds (by linarith:t-1<t) (by linarith:t<t+1))
    (Eventually.of_forall (fun u=>(densityPair_integrable (profileCore c u f) (profileCore c u g)).aestronglyMeasurable))
    (densityPair_integrable (profileCore c t f) (profileCore c t g))
    ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun z=>by
      intro u hu
      by_cases hz:z∈K
      · change ‖F' u z‖≤K.indicator (fun _=>C) z
        rw [Set.indicator_of_mem hz]
        exact hC (u,z) ⟨⟨hu.1.le,hu.2.le⟩,hz⟩
      · have hf:z∉tsupport (profileCore c u f):=fun h=>hz (Or.inl
          (profile_common_support c (t-1) (t+1) u f ⟨hu.1.le,hu.2.le⟩ h))
        have hgf:z∉tsupport (profileCore c u (profileGenerator c f)):=fun h=>hz (Or.inr
          (profile_common_support c (t-1) (t+1) u (profileGenerator c f) ⟨hu.1.le,hu.2.le⟩ h))
        change ‖pairKernel c (profileGenerator c f) g u z+pairKernel c f (profileGenerator c g) u z‖≤K.indicator (fun _=>C) z
        rw [pairKernel_zero c _ _ u z hgf,pairKernel_zero c _ _ u z hf,
          Set.indicator_of_notMem hz,add_zero,norm_zero]))
    hbound (Eventually.of_forall (fun z u _=>pairKernel_derivative c f g z u))
  have he:(fun u=>∫z,F u z ∂GaussHistoryHilbert.configurationMeasure)=
      fun u=>sourcePair (profileCore c u f) (profileCore c u g):=by
    funext u
    exact (sourcePair_integral _ _).symm
  rw [he] at hd
  have hv:(∫z,F' t z ∂GaussHistoryHilbert.configurationMeasure)=0:=by
    change (∫z,densityPair (profileCore c t (profileGenerator c f)) (profileCore c t g) z+
      densityPair (profileCore c t f) (profileCore c t (profileGenerator c g)) z ∂GaussHistoryHilbert.configurationMeasure)=0
    rw [integral_add (densityPair_integrable _ _) (densityPair_integrable _ _),
      ←sourcePair_integral,←sourcePair_integral,←profile_generator_flow,←profile_generator_flow,profile_generator_pair]
    ring
  rw [hv] at hd
  exact hd.2
private theorem profileCore_pair(c:ClockProfile)(α:ℝ)(f g:QuantumTest):
    sourcePair (profileCore c α f) (profileCore c α g)=sourcePair f g:=by
  have h:=is_const_of_deriv_eq_zero
    (fun t=>(profile_pair_derivative c f g t).differentiableAt)
    (fun t=>(profile_pair_derivative c f g t).deriv) α 0
  simpa only [profileCore_zero] using! h
private theorem profileCore_norm(c:ClockProfile)(α:ℝ)(f:QuantumTest):
    ‖embed (profileCore c α f)‖=‖embed f‖:=by
  have h:=congrArg (fun z:ℂ=>‖z‖) (profileCore_pair c α f f)
  change ‖inner ℂ (embed (profileCore c α f)) (embed (profileCore c α f))‖=‖inner ℂ (embed f) (embed f)‖ at h
  rw [←inner_self_re_eq_norm,inner_self_eq_norm_sq,←inner_self_re_eq_norm,inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (embed (profileCore c α f)),norm_nonneg (embed f)]

private theorem profile_weak_derivative(c:ClockProfile)(p f:QuantumTest)(t:ℝ):
    HasDerivAt (fun u:ℝ=>sourcePair p (profileCore c u f))
      (sourcePair p (profileCore c t (profileGenerator c f))) t:=by
  let F:Occupation→(ℝ×SourceCoordinateSlice)→ℂ:=fun word q=>profileCore c q.1 f q.2 word
  let G:Occupation→(ℝ×SourceCoordinateSlice)→ℂ:=fun word q=>profileCore c q.1 (profileGenerator c f) q.2 word
  have h:=fixedKernel_integral_derivative p F G
    (fun word=>profile_component_continuous c f word)
    (fun word=>profile_component_continuous c (profileGenerator c f) word)
    (fun word u z=>profile_jet c f z word u) t
  have he(u:ℝ):(∫z,fixedKernel p F (u,z) ∂GaussHistoryHilbert.configurationMeasure)=sourcePair p (profileCore c u f):=by
    rw [sourcePair_integral]
    congr 1
    funext z
    simp only [fixedKernel,F,densityPair_sum]
  have hg:(∫z,fixedKernel p G (t,z) ∂GaussHistoryHilbert.configurationMeasure)=sourcePair p (profileCore c t (profileGenerator c f)):=by
    rw [sourcePair_integral]
    congr 1
    funext z
    simp only [fixedKernel,G,densityPair_sum]
  simp_rw [he] at h
  rw [hg] at h
  exact h
private theorem profile_pair_difference(c:ClockProfile)(p f:QuantumTest)(s t:ℝ):
    ‖sourcePair p (profileCore c t f)-sourcePair p (profileCore c s f)‖≤
      (‖embed p‖*‖embed (profileGenerator c f)‖)*‖t-s‖:=by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _=>(profile_weak_derivative c p f u).hasDerivWithinAt)
    (fun u _=>?_) convex_univ (mem_univ s) (mem_univ t)
  change ‖inner ℂ (embed p) (embed (profileCore c u (profileGenerator c f)))‖≤_
  exact (norm_inner_le_norm _ _).trans_eq (by rw [profileCore_norm])
private theorem profile_core_difference(c:ClockProfile)(f:QuantumTest)(s t:ℝ):
    ‖embed (profileCore c t f)-embed (profileCore c s f)‖≤‖embed (profileGenerator c f)‖*‖t-s‖:=by
  let q:=profileCore c t f-profileCore c s f
  have h:=profile_pair_difference c q f s t
  change ‖inner ℂ (embed q) (embed (profileCore c t f))-inner ℂ (embed q) (embed (profileCore c s f))‖≤_ at h
  rw [←inner_sub_right,←map_sub] at h
  change ‖inner ℂ (embed q) (embed q)‖≤(‖embed q‖*‖embed (profileGenerator c f)‖)*‖t-s‖ at h
  rw [←inner_self_re_eq_norm,inner_self_eq_norm_sq] at h
  have hp:0≤‖embed (profileGenerator c f)‖*‖t-s‖:=mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hn:‖embed q‖≤‖embed (profileGenerator c f)‖*‖t-s‖:=by nlinarith [norm_nonneg (embed q)]
  simpa only [q,map_sub] using hn
private theorem profile_core_continuous(c:ClockProfile)(f:QuantumTest):
    Continuous (fun t:ℝ=>embed (profileCore c t f)):=by
  have h:LipschitzWith ‖embed (profileGenerator c f)‖₊ (fun t:ℝ=>embed (profileCore c t f)):=by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    simpa only [dist_eq_norm,coe_nnnorm] using profile_core_difference c f u t
  exact h.continuous

private def unitProfile:ClockProfile where
  value:=fun _=>1
  smooth _:=contDiffAt_const
  invariant _ _:=rfl
private theorem profile_generator_value(c:ClockProfile)(f:QuantumTest)(z:physicalChart):
    profileGenerator c f z.val=(c.value z.val:ℂ) • combinedGenerator f z.val:=by
  change (profileCoefficient c z.val:ℂ) • (noiseGenerator 0 1 f z.val)=_
  simp only [noiseGenerator,Complex.ofReal_zero,zero_smul,zero_add,Complex.ofReal_one,one_smul]
  change (profileCoefficient c z.val:ℂ) • ((reciprocalVolume z.val:ℂ) • combinedGenerator f z.val)=_
  have hv:profileCoefficient c z.val*reciprocalVolume z.val=c.value z.val:=by
    unfold profileCoefficient reciprocalVolume
    field_simp [(GaussNativeEnergy.volume_pos z).ne']
  rw [smul_smul,←Complex.ofReal_mul,hv]
private theorem unit_generator:profileGenerator unitProfile=combinedGenerator:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · simpa only [unitProfile,Complex.ofReal_one,one_smul] using profile_generator_value unitProfile f ⟨z,hz⟩
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem profileCore_commute(c d:ClockProfile)(α β:ℝ):Commute (profileCore c α) (profileCore d β):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) •
    ((Real.exp ((25/2:ℝ)*(β*d.value (profileMap c α z))):ℂ) • f (profileMap d β (profileMap c α z)))=
    (Real.exp ((25/2:ℝ)*(β*d.value z)):ℂ) •
    ((Real.exp ((25/2:ℝ)*(α*c.value (profileMap d β z))):ℂ) • f (profileMap c α (profileMap d β z)))
  simp only [profileMap,c.invariant,d.invariant,combined_add,smul_smul]
  rw [add_comm (β*d.value z) (α*c.value z),mul_comm]
private theorem profile_generator_commute(c d:ClockProfile)(β:ℝ):Commute (profileGenerator c) (profileCore d β):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  have h1:=profile_zero_jet c (profileCore d β f) z word
  have h2:HasDerivAt (fun u:ℝ=>profileCore d β (profileCore c u f) z word)
      (profileCore d β (profileGenerator c f) z word) 0:=
    (profile_zero_jet c f (profileMap d β z) word).const_mul (Real.exp ((25/2:ℝ)*(β*d.value z)):ℂ)
  have he:(fun u:ℝ=>profileCore c u (profileCore d β f) z word)=
      fun u:ℝ=>profileCore d β (profileCore c u f) z word:=by
    funext u
    exact congrArg (fun T:End=>T f z word) (profileCore_commute c d u β).eq
  rw [he] at h1
  exact h1.unique h2
private theorem D_profile(c:ClockProfile)(α:ℝ):Commute combinedGenerator (profileCore c α):=by
  rw [←unit_generator]
  exact profile_generator_commute unitProfile c α
private theorem profile_multiplier(c:ClockProfile)(α:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀s:ℝ,∀z:SourceCoordinateSlice,b (combinedMap s z)=b z):
    Commute (profileCore c α) (multiply b hb):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) • ((b (profileMap c α z):ℂ) • f (profileMap c α z))=
    (b z:ℂ) • ((Real.exp ((25/2:ℝ)*(α*c.value z)):ℂ) • f (profileMap c α z))
  unfold profileMap
  rw [hi]
  exact smul_comm _ _ _
private theorem generator_multiplier(c:ClockProfile)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀s:ℝ,∀z:SourceCoordinateSlice,b (combinedMap s z)=b z):
    Commute (profileGenerator c) (multiply b hb):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z;apply PiLp.ext;intro word
  have h1:=profile_zero_jet c (multiply b hb f) z word
  have h2:HasDerivAt (fun u:ℝ=>multiply b hb (profileCore c u f) z word)
      (multiply b hb (profileGenerator c f) z word) 0:=
    (profile_zero_jet c f z word).const_mul (b z:ℂ)
  have he:(fun u:ℝ=>profileCore c u (multiply b hb f) z word)=
      fun u:ℝ=>multiply b hb (profileCore c u f) z word:=by
    funext u
    exact congrArg (fun T:End=>T f z word) (profile_multiplier c u b hb hi).eq
  rw [he] at h1
  exact h1.unique h2

def heatLog(t:ℝ)(z:SourceCoordinateSlice):ℝ:=Real.log (1+18*t*reciprocalVolume z)
def heatMean(t:ℝ)(z:SourceCoordinateSlice):ℝ:= -heatLog t z/6
def heatVariance(t:ℝ)(z:SourceCoordinateSlice):ℝ:=heatLog t z/9
private theorem heatLog_pos(t:ℝ)(ht:0<t)(z:physicalChart):0<heatLog t z.val:=by
  apply Real.log_pos
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (GaussNativeEnergy.volume_pos z)
  change 1<1+18*t*reciprocalVolume z.val
  have hp:0<18*t*reciprocalVolume z.val:=by positivity
  linarith
private theorem heatLog_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (heatLog t) z.val:=by
  apply (contDiffAt_const.add ((contDiffAt_const.mul contDiffAt_const).mul (reciprocal_volume_smooth z))).log
  have hu:0<reciprocalVolume z.val:=inv_pos.mpr (GaussNativeEnergy.volume_pos z)
  positivity
private def heatProfile(t:ℝ)(ht:0<t)(ξ:ℝ):ClockProfile where
  value z:=heatMean t z+Real.sqrt (heatVariance t z)*ξ
  smooth z:=by
    have hL:=heatLog_smooth t ht z
    exact ((hL.neg).div_const 6).add
      (((hL.div_const 9).sqrt (by exact ne_of_gt (div_pos (heatLog_pos t ht z) (by norm_num)))).mul contDiffAt_const)
  invariant _ _:=rfl

def sourceHeatCore(t:ℝ)(ht:0<t)(ξ:ℝ):End:=
  sourceForwardCore t ht.le*profileCore (heatProfile t ht ξ) 1

private def meanProfile(t:ℝ)(ht:0<t):ClockProfile where
  value:=heatMean t
  smooth z:=((heatLog_smooth t ht z).neg).div_const 6
  invariant _ _:=rfl
private def widthProfile(t:ℝ)(ht:0<t):ClockProfile where
  value z:=Real.sqrt (heatVariance t z)
  smooth z:=((heatLog_smooth t ht z).div_const 9).sqrt
    (ne_of_gt (div_pos (heatLog_pos t ht z) (by norm_num)))
  invariant _ _:=rfl
private theorem heat_profile_factor(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    profileCore (heatProfile t ht ξ) 1 f=
      profileCore (meanProfile t ht) 1 (profileCore (widthProfile t ht) ξ f):=by
  apply DFunLike.ext;intro z
  have hm(s:ℝ):heatMean t (combinedMap s z)=heatMean t z:=rfl
  have hv(s:ℝ):heatVariance t (combinedMap s z)=heatVariance t z:=rfl
  change (Real.exp ((25/2:ℝ)*(1*(heatMean t z+Real.sqrt (heatVariance t z)*ξ))):ℂ) •
      f (combinedMap (1*(heatMean t z+Real.sqrt (heatVariance t z)*ξ)) z)=
    (Real.exp ((25/2:ℝ)*(1*heatMean t z)):ℂ) •
      ((Real.exp ((25/2:ℝ)*(ξ*Real.sqrt (heatVariance t (combinedMap (1*heatMean t z) z)))):ℂ) •
        f (combinedMap (ξ*Real.sqrt (heatVariance t (combinedMap (1*heatMean t z) z)))
          (combinedMap (1*heatMean t z) z)))
  simp only [one_mul,hv,smul_smul,←Complex.ofReal_mul,←Real.exp_add,combined_add]
  congr 2
  · congr 1
    ring
  · congr 1
    ring
private def heatOuter(t:ℝ)(ht:0<t):End:=sourceForwardCore t ht.le*profileCore (meanProfile t ht) 1
private theorem sourceHeat_factor(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    sourceHeatCore t ht ξ f=heatOuter t ht (profileCore (widthProfile t ht) ξ f):=by
  change sourceForwardCore t ht.le (profileCore (heatProfile t ht ξ) 1 f)=_
  rw [heat_profile_factor]
  rfl
private theorem forward_norm(t:ℝ)(ht:0≤t)(f:QuantumTest):‖embed (sourceForwardCore t ht f)‖=‖embed f‖:=by
  have h:=congrArg (fun z:ℂ=>‖z‖) (actual_forward_core_pair t ht f f)
  change ‖inner ℂ (embed (sourceForwardCore t ht f)) (embed (sourceForwardCore t ht f))‖=‖inner ℂ (embed f) (embed f)‖ at h
  rw [←inner_self_re_eq_norm,inner_self_eq_norm_sq,←inner_self_re_eq_norm,inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (embed (sourceForwardCore t ht f)),norm_nonneg (embed f)]
private theorem heatOuter_norm(t:ℝ)(ht:0<t)(f:QuantumTest):‖embed (heatOuter t ht f)‖=‖embed f‖:=by
  change ‖embed (sourceForwardCore t ht.le (profileCore (meanProfile t ht) 1 f))‖=_
  rw [forward_norm,profileCore_norm]
theorem sourceHeat_norm(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):‖embed (sourceHeatCore t ht ξ f)‖=‖embed f‖:=by
  rw [sourceHeat_factor,heatOuter_norm,profileCore_norm]
private theorem sourceHeat_continuous(t:ℝ)(ht:0<t)(f:QuantumTest):
    Continuous (fun ξ:ℝ=>embed (sourceHeatCore t ht ξ f)):=by
  have h:LipschitzWith ‖embed (profileGenerator (widthProfile t ht) f)‖₊
      (fun ξ:ℝ=>embed (sourceHeatCore t ht ξ f)):=by
    apply LipschitzWith.of_dist_le_mul
    intro ξ η
    simp only [dist_eq_norm,coe_nnnorm,sourceHeat_factor]
    rw [←map_sub,←map_sub,heatOuter_norm,map_sub]
    exact profile_core_difference (widthProfile t ht) f η ξ
  exact h.continuous
private abbrev gaussian:=ProbabilityTheory.gaussianReal 0 1
theorem sourceHeat_integrable(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun ξ:ℝ=>embed (sourceHeatCore t ht ξ f)) gaussian:=by
  let : SecondCountableTopologyEither ℝ H := ⟨Or.inl inferInstance⟩
  apply (integrable_const (‖embed f‖:ℝ)).mono'
    (sourceHeat_continuous t ht f).aestronglyMeasurable
  exact Eventually.of_forall (fun ξ=>by rw [sourceHeat_norm])
def heatMeanCore(t:ℝ)(ht:0<t):QuantumTest→ₗ[ℂ]H where
  toFun f:=∫ξ:ℝ,embed (sourceHeatCore t ht ξ f) ∂gaussian
  map_add' f g:=by
    simp only [map_add]
    exact integral_add (sourceHeat_integrable t ht f) (sourceHeat_integrable t ht g)
  map_smul' c f:=by
    simp only [map_smul,RingHom.id_apply]
    exact integral_smul c _
private theorem heatMeanCore_bound(t:ℝ)(ht:0<t)(f:QuantumTest):‖heatMeanCore t ht f‖≤‖embed f‖:=by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp only [sourceHeat_norm]
  simp
private def heatCoreMap(t:ℝ)(ht:0<t):Core→ₗ[ℂ]H:=
  (heatMeanCore t ht).comp coreEquiv.symm.toLinearMap
private theorem heatCoreMap_bound(t:ℝ)(ht:0<t)(x:Core):‖heatCoreMap t ht x‖≤1*‖x‖:=by
  obtain ⟨f,rfl⟩:=coreEquiv.surjective x
  change ‖heatMeanCore t ht (coreEquiv.symm (coreEquiv f))‖≤1*‖embed f‖
  rw [coreEquiv.symm_apply_apply,one_mul]
  exact heatMeanCore_bound t ht f
def heatOperator(t:ℝ)(ht:0<t):H→L[ℂ]H:=
  ((heatCoreMap t ht).mkContinuous 1 (heatCoreMap_bound t ht)).extend Core.subtypeL
private theorem heatOperator_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatOperator t ht (embed f)=heatMeanCore t ht f:=by
  have h:=ContinuousLinearMap.extend_eq ((heatCoreMap t ht).mkContinuous 1 (heatCoreMap_bound t ht))
    GaussBoundedMultiplier.core_dense isometry_subtype_coe.isUniformInducing (coreEquiv f)
  change heatOperator t ht (embed f)=heatMeanCore t ht (coreEquiv.symm (coreEquiv f)) at h
  simpa only [coreEquiv.symm_apply_apply] using h
private theorem heatOperator_norm(t:ℝ)(ht:0<t):‖heatOperator t ht‖≤1:=by
  let T:Core→L[ℂ]H:=(heatCoreMap t ht).mkContinuous 1 (heatCoreMap_bound t ht)
  have he:=T.opNorm_extend_le (e:=Core.subtypeL) (N:=(1:NNReal))
    GaussBoundedMultiplier.core_dense (fun x=>by simp)
  have hb:‖T‖≤1:=(heatCoreMap t ht).mkContinuous_norm_le (by norm_num) (heatCoreMap_bound t ht)
  exact he.trans (by simpa using hb)

theorem integral_core_graph(L:End)(f:ℝ→QuantumTest)
    (hf:Integrable (fun ξ=>embed (f ξ)) gaussian)
    (hLf:Integrable (fun ξ=>embed (L (f ξ))) gaussian):
    ((∫ξ,embed (f ξ) ∂gaussian),(∫ξ,embed (L (f ξ)) ∂gaussian))∈
      SymmetricGraphClosure.closedGraph (realize L):=by
  let : NormedAddCommGroup (H×H) := Prod.normedAddCommGroup
  let : NormedSpace ℝ (H×H) := Prod.normedSpace
  let K:=SymmetricGraphClosure.closedGraph (realize L)
  have hm:∀ᵐ ξ∂gaussian,(embed (f ξ),embed (L (f ξ)))∈K:=by
    apply Eventually.of_forall
    intro ξ
    have h:(((coreEquiv (f ξ):Core):H),realize L (coreEquiv (f ξ)))∈(realize L).graph:=
      (realize L).mem_graph (coreEquiv (f ξ))
    have hh:=((realize L).graph.le_topologicalClosure h)
    change (embed (f ξ),embed (L (coreEquiv.symm (coreEquiv (f ξ)))))∈K at hh
    simpa only [coreEquiv.symm_apply_apply] using hh
  have hc:IsClosed (K:Set (H×H)):=(realize L).graph.isClosed_topologicalClosure
  have hi:Integrable (fun ξ=>(embed (f ξ),embed (L (f ξ)))) gaussian:=hf.prodMk hLf
  have h:∫ξ,(embed (f ξ),embed (L (f ξ))) ∂gaussian∈K:=
    (K.restrictScalars ℝ).convex.integral_mem hc hm hi
  simpa only [integral_pair hf hLf] using h

private theorem profile_integral(c:ClockProfile)(f:QuantumTest)(t:ℝ):
    (∫u in (0:ℝ)..t,embed (profileCore c u (profileGenerator c f)))=
      embed (profileCore c t f)-embed f:=by
  apply ext_inner_left ℂ;intro x
  refine SourceCoframeScaleTransport.embed_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro p
  have hi:=(profile_core_continuous c (profileGenerator c f)).intervalIntegrable (μ:=MeasureTheory.volume) 0 t
  have hm:=(innerSL ℂ (embed p)).intervalIntegral_comp_comm hi
  change (∫u in (0:ℝ)..t,inner ℂ (embed p) (embed (profileCore c u (profileGenerator c f))))=
    inner ℂ (embed p) (∫u in (0:ℝ)..t,embed (profileCore c u (profileGenerator c f))) at hm
  rw [←hm,inner_sub_right]
  change (∫u in (0:ℝ)..t,sourcePair p (profileCore c u (profileGenerator c f)))=
    sourcePair p (profileCore c t f)-sourcePair p f
  have hc:Continuous (fun u:ℝ=>sourcePair p (profileCore c u (profileGenerator c f))):=
    continuous_const.inner (profile_core_continuous c (profileGenerator c f))
  have h:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _=>profile_weak_derivative c p f u) (hc.intervalIntegrable 0 t)
  simpa only [profileCore_zero] using! h
private theorem profile_strong_derivative(c:ClockProfile)(f:QuantumTest)(t:ℝ):
    HasDerivAt (fun u:ℝ=>embed (profileCore c u f)) (embed (profileCore c t (profileGenerator c f))) t:=by
  have hc:=profile_core_continuous c (profileGenerator c f)
  let :SecondCountableTopologyEither ℝ H:=⟨Or.inl inferInstance⟩
  have h:=intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he:(fun u:ℝ=>embed (profileCore c u f))=
      fun u=>embed f+∫v in (0:ℝ)..u,embed (profileCore c v (profileGenerator c f)):=by
    funext u;rw [profile_integral];abel
  rw [he]
  exact h.const_add (embed f)
private def outerHilbert(t:ℝ)(ht:0<t):H→L[ℂ]H:=
  (embed.comp (heatOuter t ht)).extendOfNorm embed
private theorem outerHilbert_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    outerHilbert t ht (embed f)=embed (heatOuter t ht f):=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense
    ⟨1,fun g=>by simp only [LinearMap.comp_apply,one_mul,heatOuter_norm,le_refl]⟩ f
theorem sourceHeat_strong_derivative(t:ℝ)(ht:0<t)(f:QuantumTest)(ξ:ℝ):
    HasDerivAt (fun u:ℝ=>embed (sourceHeatCore t ht u f))
      (embed (sourceHeatCore t ht ξ (profileGenerator (widthProfile t ht) f))) ξ:=by
  have h:=((outerHilbert t ht).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt ξ
    (profile_strong_derivative (widthProfile t ht) f ξ)
  simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',outerHilbert_core,←sourceHeat_factor] using! h
theorem weighted_heat_integrable(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun ξ:ℝ=>(ξ:ℂ) • embed (sourceHeatCore t ht ξ f)) gaussian:=by
  let :SecondCountableTopologyEither ℝ H:=⟨Or.inl inferInstance⟩
  have h1:Integrable (fun x:ℝ=>x) gaussian:=
    (ProbabilityTheory.memLp_id_gaussianReal (μ:=0) (v:=1) 1).integrable (by norm_num)
  have hi:Integrable (fun x:ℝ=>|x|) gaussian:=by exact h1.norm
  apply (hi.mul_const (‖embed f‖)).mono'
    ((Complex.continuous_ofReal.smul (sourceHeat_continuous t ht f)).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖(ξ:ℂ) • embed (sourceHeatCore t ht ξ f)‖≤|ξ| * ‖embed f‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,sourceHeat_norm]
def weightedHeatMeanCore(t:ℝ)(ht:0<t):QuantumTest→ₗ[ℂ]H where
  toFun f:=∫ξ:ℝ,(ξ:ℂ) • embed (sourceHeatCore t ht ξ f) ∂gaussian
  map_add' f g:=by
    simp only [map_add,smul_add]
    exact integral_add (weighted_heat_integrable t ht f) (weighted_heat_integrable t ht g)
  map_smul' c f:=by
    simp only [map_smul,RingHom.id_apply]
    have he:(fun ξ:ℝ=>(ξ:ℂ) • c • embed (sourceHeatCore t ht ξ f))=
        fun ξ:ℝ=>c • (ξ:ℂ) • embed (sourceHeatCore t ht ξ f):=by
      funext ξ;exact smul_comm (ξ:ℂ) c _
    rw [he]
    exact integral_smul c _
private theorem weightedHeatMeanCore_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖weightedHeatMeanCore t ht f‖≤‖embed f‖:=by
  calc
    _≤∫ξ:ℝ,‖(ξ:ℂ) • embed (sourceHeatCore t ht ξ f)‖ ∂gaussian:=norm_integral_le_integral_norm _
    _=(∫ξ:ℝ,|ξ| ∂gaussian)*‖embed f‖:=by
      simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,sourceHeat_norm]
      exact integral_mul_const _ _
    _≤1*‖embed f‖:=mul_le_mul_of_nonneg_right
      SourceClockPhiGaussianComplexIBP.standard_gaussian_abs_moment_le_one (norm_nonneg _)
    _=‖embed f‖:=one_mul _
private theorem gaussian_state_derivative(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatMeanCore t ht (profileGenerator (widthProfile t ht) f)=weightedHeatMeanCore t ht f:=by
  apply ext_inner_left ℂ;intro p
  let h:ℝ→ℂ:=fun ξ=>inner ℂ p (embed (sourceHeatCore t ht ξ f))
  let h':ℝ→ℂ:=fun ξ=>inner ℂ p (embed (sourceHeatCore t ht ξ (profileGenerator (widthProfile t ht) f)))
  have hd(ξ:ℝ):HasDerivAt h (h' ξ) ξ:=
    ((innerSL ℂ p).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt ξ (sourceHeat_strong_derivative t ht f ξ)
  have hc':Continuous h':=continuous_const.inner (sourceHeat_continuous t ht (profileGenerator (widthProfile t ht) f))
  have hc:ContDiff ℝ 1 h:=contDiff_one_iff_deriv.mpr
    ⟨fun ξ=>(hd ξ).differentiableAt,by
      have he:deriv h=h':=funext (fun ξ=>(hd ξ).deriv)
      rw [he];exact hc'⟩
  have hb(ξ:ℝ):‖h ξ‖≤‖p‖*‖embed f‖:=
    (norm_inner_le_norm _ _).trans_eq (by rw [sourceHeat_norm])
  have hb'(ξ:ℝ):‖h' ξ‖≤‖p‖*‖embed (profileGenerator (widthProfile t ht) f)‖:=
    (norm_inner_le_norm _ _).trans_eq (by rw [sourceHeat_norm])
  have hi:=SourceClockPhiGaussianComplexIBP.standard_gaussian_complex_IBP h h' _ _ hc hd hb hb'
  have hl:=(innerSL ℂ p).integral_comp_comm (sourceHeat_integrable t ht (profileGenerator (widthProfile t ht) f))
  have hr:=(innerSL ℂ p).integral_comp_comm (weighted_heat_integrable t ht f)
  change (∫ξ,h' ξ ∂gaussian)=inner ℂ p (heatMeanCore t ht (profileGenerator (widthProfile t ht) f)) at hl
  change (∫ξ,inner ℂ p ((ξ:ℂ) • embed (sourceHeatCore t ht ξ f)) ∂gaussian)=inner ℂ p (weightedHeatMeanCore t ht f) at hr
  rw [←hl,←hr]
  simpa only [h,inner_smul_right] using hi

private theorem heatLog_volume(t:ℝ)(_ht:0<t)(z:physicalChart):
    heatLog t z.val=Real.log ((GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val):=by
  unfold heatLog
  congr 1
  unfold reciprocalVolume
  field_simp [(GaussNativeEnergy.volume_pos z).ne']
private def gaussianA(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  3/Real.sqrt ((GaussNativeEnergy.volume z+18*t)*heatLog t z)
private def gaussianUD(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  forwardA t z*gaussianA t z
private theorem gaussianA_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (gaussianA t) z.val:=by
  have hw:0<GaussNativeEnergy.volume z.val+18*t:=by linarith [GaussNativeEnergy.volume_pos z]
  exact contDiffAt_const.div
    (((volume_smooth.contDiffAt.add contDiffAt_const).mul (heatLog_smooth t ht z)).sqrt
      (mul_pos hw (heatLog_pos t ht z)).ne')
    (Real.sqrt_pos.mpr (mul_pos hw (heatLog_pos t ht z))).ne'
private theorem gaussianUD_smooth(t:ℝ)(ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (gaussianUD t) z.val:=
  (forwardA_smooth t ht.le z).mul (gaussianA_smooth t ht z)
private def gaussianAAction(t:ℝ)(ht:0<t):End:=multiply (gaussianA t) (gaussianA_smooth t ht)
private def gaussianUDAction(t:ℝ)(ht:0<t):End:=multiply (gaussianUD t) (gaussianUD_smooth t ht)
private theorem multiplier_bound(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(C:ℝ)(hC:0≤C)
    (hb:∀z:physicalChart,|c z.val|≤C)(f:QuantumTest):
    ‖embed (multiply c hc f)‖≤C*‖embed f‖:=by
  apply GaussBoundedMultiplier.action_bound
    (fun z=>(c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z=>(Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (hc z)).smul contDiffAt_const)
    (fun _ w=>(Commute.one_right (GaussFockWeights.weight w)).smul_right _) C hC _ f
  intro z x
  change ‖(c z.val:ℂ) • x‖≤C*‖x‖
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg x)
private theorem coefficient_prices(t:ℝ)(ht:0<t)(z:physicalChart):
    |forwardU t z.val|≤1/(18*t) ∧ |gaussianA t z.val|≤1/Real.sqrt (2*t) ∧
      |gaussianUD t z.val|≤1/(6*t):=by
  have hv:=GaussNativeEnergy.volume_pos z
  have hL:=heatLog_pos t ht z
  have hw:0<GaussNativeEnergy.volume z.val+18*t:=by positivity
  have h1:=SourceClockPhiHeatClockPrice.clock_U_price _ t hv ht
  have h2:=SourceClockPhiHeatClockPrice.clock_A_price _ t hv ht
  have h3:=SourceClockPhiHeatClockPrice.clock_aA_price _ t hv ht
  dsimp only [forwardU,gaussianUD,forwardA,gaussianA]
  rw [abs_of_nonneg (inv_nonneg.mpr hw.le)]
  rw [abs_of_nonneg (by positivity:0≤3/Real.sqrt ((GaussNativeEnergy.volume z.val+18*t)*heatLog t z.val))]
  rw [abs_of_nonneg (by positivity:0≤(Real.sqrt (GaussNativeEnergy.volume z.val+18*t))⁻¹*
    (3/Real.sqrt ((GaussNativeEnergy.volume z.val+18*t)*heatLog t z.val)))]
  rw [heatLog_volume t ht z]
  simpa only [one_div] using And.intro h1 (And.intro h2 h3)
private theorem heat_D(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    combinedGenerator (sourceHeatCore t ht ξ f)=sourceHeatCore t ht ξ (combinedGenerator f):=by
  have hJ:=LinearMap.congr_fun (SourceClockPhiForwardGeneratorTransport.actual_forward_generator_commute t ht.le).eq
    (profileCore (heatProfile t ht ξ) 1 f)
  have hN:=LinearMap.congr_fun (D_profile (heatProfile t ht ξ) 1).eq f
  simp only [Module.End.mul_apply] at hJ hN
  change combinedGenerator (sourceForwardCore t ht.le (profileCore (heatProfile t ht ξ) 1 f))=_
  rw [hJ,hN]
  rfl
private theorem heat_U(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    inverseVolumeAction (sourceHeatCore t ht ξ f)=sourceHeatCore t ht ξ (forwardUAction t ht.le f):=by
  have hJ:=LinearMap.congr_fun (actual_forward_U_return t ht.le) (profileCore (heatProfile t ht ξ) 1 f)
  have hN:=LinearMap.congr_fun (profile_multiplier (heatProfile t ht ξ) 1
    (forwardU t) (forwardU_smooth t ht.le) (fun _ _=>rfl)).eq f
  simp only [Module.End.mul_apply] at hJ hN
  change inverseVolumeAction (sourceForwardCore t ht.le (profileCore (heatProfile t ht ξ) 1 f))=_
  change profileCore (heatProfile t ht ξ) 1 (forwardUAction t ht.le f)=
    forwardUAction t ht.le (profileCore (heatProfile t ht ξ) 1 f) at hN
  rw [hJ,←hN]
  rfl
theorem heat_A(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    combinedConjugate (sourceHeatCore t ht ξ f)=
      sourceHeatCore t ht ξ (forwardAAction t ht.le (combinedGenerator f)):=by
  have hJ:=LinearMap.congr_fun (actual_forward_A_return t ht.le) (profileCore (heatProfile t ht ξ) 1 f)
  have hD:=LinearMap.congr_fun (D_profile (heatProfile t ht ξ) 1).eq f
  have hN:=LinearMap.congr_fun (profile_multiplier (heatProfile t ht ξ) 1
    (forwardA t) (forwardA_smooth t ht.le) (fun _ _=>rfl)).eq (combinedGenerator f)
  simp only [Module.End.mul_apply] at hJ hD hN
  change combinedConjugate (sourceForwardCore t ht.le (profileCore (heatProfile t ht ξ) 1 f))=_
  change profileCore (heatProfile t ht ξ) 1 (forwardAAction t ht.le (combinedGenerator f))=
    forwardAAction t ht.le (profileCore (heatProfile t ht ξ) 1 (combinedGenerator f)) at hN
  rw [hJ,hD,←hN]
  rfl
theorem heat_UD(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    (inverseVolumeAction*combinedGenerator) (sourceHeatCore t ht ξ f)=
      sourceHeatCore t ht ξ (forwardUAction t ht.le (combinedGenerator f)):=by
  change inverseVolumeAction (combinedGenerator (sourceHeatCore t ht ξ f))=_
  rw [heat_D,heat_U]
private theorem raw_graph(t:ℝ)(ht:0<t)(L R:End)
    (hr:∀ξ f,L (sourceHeatCore t ht ξ f)=sourceHeatCore t ht ξ (R f))(f:QuantumTest):
    (heatOperator t ht (embed f),heatMeanCore t ht (R f))∈SymmetricGraphClosure.closedGraph (realize L):=by
  have hi:Integrable (fun ξ=>embed (L (sourceHeatCore t ht ξ f))) gaussian:=by
    simp only [hr]
    exact sourceHeat_integrable t ht (R f)
  have h:=integral_core_graph L (fun ξ=>sourceHeatCore t ht ξ f) (sourceHeat_integrable t ht f) hi
  simp only [hr] at h
  rw [heatOperator_core]
  exact h

def heatUReader(t:ℝ)(ht:0<t):H→L[ℂ]H:=
  ((heatMeanCore t ht).comp (forwardUAction t ht.le)).extendOfNorm embed
def heatAReader(t:ℝ)(ht:0<t):H→L[ℂ]H:=
  ((weightedHeatMeanCore t ht).comp (gaussianAAction t ht)).extendOfNorm embed
def heatUDReader(t:ℝ)(ht:0<t):H→L[ℂ]H:=
  ((weightedHeatMeanCore t ht).comp (gaussianUDAction t ht)).extendOfNorm embed
private theorem U_reader_core_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖heatMeanCore t ht (forwardUAction t ht.le f)‖≤(1/(18*t))*‖embed f‖:=
  (heatMeanCore_bound t ht _).trans (multiplier_bound _ _ _ (by positivity)
    (fun z=>(coefficient_prices t ht z).1) f)
private theorem A_reader_core_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖weightedHeatMeanCore t ht (gaussianAAction t ht f)‖≤(1/Real.sqrt (2*t))*‖embed f‖:=
  (weightedHeatMeanCore_bound t ht _).trans (multiplier_bound _ _ _ (by positivity)
    (fun z=>(coefficient_prices t ht z).2.1) f)
private theorem UD_reader_core_bound(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖weightedHeatMeanCore t ht (gaussianUDAction t ht f)‖≤(1/(6*t))*‖embed f‖:=
  (weightedHeatMeanCore_bound t ht _).trans (multiplier_bound _ _ _ (by positivity)
    (fun z=>(coefficient_prices t ht z).2.2) f)
private theorem U_reader_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatUReader t ht (embed f)=heatMeanCore t ht (forwardUAction t ht.le f):=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense ⟨_,U_reader_core_bound t ht⟩ f
private theorem A_reader_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatAReader t ht (embed f)=weightedHeatMeanCore t ht (gaussianAAction t ht f):=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense ⟨_,A_reader_core_bound t ht⟩ f
private theorem UD_reader_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatUDReader t ht (embed f)=weightedHeatMeanCore t ht (gaussianUDAction t ht f):=
  LinearMap.extendOfNorm_eq SourceCoframeScaleTransport.embed_dense ⟨_,UD_reader_core_bound t ht⟩ f
private theorem reader_bounds(t:ℝ)(ht:0<t):
    ‖heatUReader t ht‖≤1/(18*t) ∧ ‖heatAReader t ht‖≤1/Real.sqrt (2*t) ∧
      ‖heatUDReader t ht‖≤1/(6*t):=by
  exact ⟨LinearMap.opNorm_extendOfNorm_le SourceCoframeScaleTransport.embed_dense (by positivity) (U_reader_core_bound t ht),
    LinearMap.opNorm_extendOfNorm_le SourceCoframeScaleTransport.embed_dense (by positivity) (A_reader_core_bound t ht),
    LinearMap.opNorm_extendOfNorm_le SourceCoframeScaleTransport.embed_dense (by positivity) (UD_reader_core_bound t ht)⟩

private theorem width_multiplier(t:ℝ)(ht:0<t)(b d:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hi:∀s z,b (combinedMap s z)=b z)
    (hp:∀z:physicalChart,Real.sqrt (heatVariance t z.val)*b z.val=d z.val):
    profileGenerator (widthProfile t ht)*multiply b hb=multiply d hd*combinedGenerator:=by
  have hD:Commute combinedGenerator (multiply b hb):=by
    rw [←unit_generator]
    exact generator_multiplier unitProfile b hb hi
  apply LinearMap.ext;intro f
  have hc:=LinearMap.congr_fun hD.eq f
  simp only [Module.End.mul_apply] at hc
  apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · rw [Module.End.mul_apply,profile_generator_value _ _ ⟨z,hz⟩,hc]
    change (Real.sqrt (heatVariance t z):ℂ) • ((b z:ℂ) • combinedGenerator f z)=
      (d z:ℂ) • combinedGenerator f z
    rw [smul_smul,←Complex.ofReal_mul,hp ⟨z,hz⟩]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem width_A(t:ℝ)(ht:0<t):
    profileGenerator (widthProfile t ht)*gaussianAAction t ht=forwardAAction t ht.le*combinedGenerator:=by
  apply width_multiplier t ht _ _ _ _ (fun _ _=>rfl)
  intro z
  unfold heatVariance gaussianA forwardA
  rw [heatLog_volume t ht z,mul_comm]
  simpa only [one_div] using SourceClockPhiHeatCoefficientProduct.clock_A_product
    (GaussNativeEnergy.volume z.val) t (GaussNativeEnergy.volume_pos z) ht
private theorem width_UD(t:ℝ)(ht:0<t):
    profileGenerator (widthProfile t ht)*gaussianUDAction t ht=forwardUAction t ht.le*combinedGenerator:=by
  apply width_multiplier t ht _ _ _ _ (fun _ _=>rfl)
  intro z
  dsimp only [heatVariance,gaussianUD,forwardA,gaussianA,forwardU]
  rw [heatLog_volume t ht z,mul_comm]
  simpa only [one_div] using SourceClockPhiHeatCoefficientProduct.clock_UD_product
    (GaussNativeEnergy.volume z.val) t (GaussNativeEnergy.volume_pos z) ht
private theorem core_native_graphs(t:ℝ)(ht:0<t)(f:QuantumTest):
    (heatOperator t ht (embed f),heatMeanCore t ht (forwardUAction t ht.le f))∈
      SymmetricGraphClosure.closedGraph (realize inverseVolumeAction) ∧
    (heatOperator t ht (embed f),weightedHeatMeanCore t ht (gaussianAAction t ht f))∈
      SymmetricGraphClosure.closedGraph (realize combinedConjugate) ∧
    (heatOperator t ht (embed f),weightedHeatMeanCore t ht (gaussianUDAction t ht f))∈
      SymmetricGraphClosure.closedGraph (realize (inverseVolumeAction*combinedGenerator)):=by
  refine ⟨raw_graph t ht _ _ (heat_U t ht) f,?_,?_⟩
  · have h:=raw_graph t ht _ (forwardAAction t ht.le*combinedGenerator) (heat_A t ht) f
    rw [←width_A,Module.End.mul_apply,gaussian_state_derivative] at h
    exact h
  · have h:=raw_graph t ht _ (forwardUAction t ht.le*combinedGenerator) (heat_UD t ht) f
    rw [←width_UD,Module.End.mul_apply,gaussian_state_derivative] at h
    exact h
private theorem all_native_graphs(t:ℝ)(ht:0<t)(x:H):
    (heatOperator t ht x,heatUReader t ht x)∈SymmetricGraphClosure.closedGraph (realize inverseVolumeAction) ∧
    (heatOperator t ht x,heatAReader t ht x)∈SymmetricGraphClosure.closedGraph (realize combinedConjugate) ∧
    (heatOperator t ht x,heatUDReader t ht x)∈SymmetricGraphClosure.closedGraph (realize (inverseVolumeAction*combinedGenerator)):=by
  have hU:=SourceClockPhiHeatClosedGraphExtension.actual_closed_graph_dense_extension
    inverseVolumeAction (heatOperator t ht) ((heatMeanCore t ht).comp (forwardUAction t ht.le))
    (1/(18*t)) (U_reader_core_bound t ht) (fun f=>(core_native_graphs t ht f).1) x
  have hA:=SourceClockPhiHeatClosedGraphExtension.actual_closed_graph_dense_extension
    combinedConjugate (heatOperator t ht) ((weightedHeatMeanCore t ht).comp (gaussianAAction t ht))
    (1/Real.sqrt (2*t)) (A_reader_core_bound t ht) (fun f=>(core_native_graphs t ht f).2.1) x
  have hD:=SourceClockPhiHeatClosedGraphExtension.actual_closed_graph_dense_extension
    (inverseVolumeAction*combinedGenerator) (heatOperator t ht)
    ((weightedHeatMeanCore t ht).comp (gaussianUDAction t ht))
    (1/(6*t)) (UD_reader_core_bound t ht) (fun f=>(core_native_graphs t ht f).2.2) x
  exact ⟨hU.1,hA.1,hD.1⟩
/-- The Gaussian source puts every original Hilbert input in all three native closed graphs. -/
theorem actual_heat_native_smoothing(t:ℝ)(ht:0<t):
    ‖heatOperator t ht‖≤1 ∧ ‖heatUReader t ht‖≤1/(18*t) ∧
    ‖heatAReader t ht‖≤1/Real.sqrt (2*t) ∧ ‖heatUDReader t ht‖≤1/(6*t) ∧
    ∀x:H,
      ((heatOperator t ht x,heatUReader t ht x)∈SymmetricGraphClosure.closedGraph (realize inverseVolumeAction) ∧
       ∀y:H,(heatOperator t ht x,y)∈SymmetricGraphClosure.closedGraph (realize inverseVolumeAction)→y=heatUReader t ht x) ∧
      ((heatOperator t ht x,heatAReader t ht x)∈SymmetricGraphClosure.closedGraph (realize combinedConjugate) ∧
       ∀y:H,(heatOperator t ht x,y)∈SymmetricGraphClosure.closedGraph (realize combinedConjugate)→y=heatAReader t ht x) ∧
      ((heatOperator t ht x,heatUDReader t ht x)∈SymmetricGraphClosure.closedGraph (realize (inverseVolumeAction*combinedGenerator)) ∧
       ∀y:H,(heatOperator t ht x,y)∈SymmetricGraphClosure.closedGraph (realize (inverseVolumeAction*combinedGenerator))→y=heatUDReader t ht x):=by
  refine ⟨heatOperator_norm t ht,(reader_bounds t ht).1,(reader_bounds t ht).2.1,(reader_bounds t ht).2.2,?_⟩
  intro x
  obtain ⟨hU,hA,hD⟩:=all_native_graphs t ht x
  exact ⟨⟨hU,fun _ hy=>SourceClockPhiHeatNativeClosedGraph.actual_U_closed_graph_singlevalued hy hU⟩,
    ⟨hA,fun _ hy=>SourceClockPhiHeatNativeClosedGraph.actual_A_closed_graph_singlevalued hy hA⟩,
    ⟨hD,fun _ hy=>SourceClockPhiHeatNativeClosedGraph.actual_UD_closed_graph_singlevalued hy hD⟩⟩

def heatNativeEnergy(t:ℝ)(ht:0<t)(x:H):ℝ:=‖heatOperator t ht x‖^2+
  (18*t)^2*‖heatUReader t ht x‖^2+2*t*‖heatAReader t ht x‖^2+
  (6*t)^2*‖heatUDReader t ht x‖^2
private theorem scaled_reader_bound(T:H→L[ℂ]H)(c:ℝ)(hc:0<c)(hb:‖T‖≤1/c)(x:H):
    c^2*‖T x‖^2≤‖x‖^2:=by
  have hn:‖T x‖≤(1/c)*‖x‖:=(T.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have h:c*‖T x‖≤‖x‖:=by
    calc _≤c*((1/c)*‖x‖):=mul_le_mul_of_nonneg_left hn hc.le
         _=‖x‖:=by field_simp [hc.ne']
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity:0≤c*‖T x‖) h 2
private theorem heat_native_energy_bound(t:ℝ)(ht:0<t)(x:H):heatNativeEnergy t ht x≤4*‖x‖^2:=by
  have hu:=scaled_reader_bound (heatUReader t ht) (18*t) (by positivity) (reader_bounds t ht).1 x
  have ha:=scaled_reader_bound (heatAReader t ht) (Real.sqrt (2*t)) (by positivity) (reader_bounds t ht).2.1 x
  rw [Real.sq_sqrt (by positivity:0≤2*t)] at ha
  have hd:=scaled_reader_bound (heatUDReader t ht) (6*t) (by positivity) (reader_bounds t ht).2.2 x
  have h0:‖heatOperator t ht x‖≤‖x‖:=by
    simpa only [one_mul] using ((heatOperator t ht).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (heatOperator_norm t ht) (norm_nonneg x))
  have hs:=pow_le_pow_left₀ (norm_nonneg _) h0 2
  dsimp only [heatNativeEnergy]
  linarith

open GaussDiagonalHistory GaussUnitaryHistory SourceLocalizedInverseFormPayment
open SourceClockRadiusAffineCutoff SourceClockPhiRadiusSourceCurrent
open SourceClockPhiRadiusNormalizedFluxBudget
private theorem heat_frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    (actualFrequency advanced μ w).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'
/-- One source cutoff pays the complete weighted native energy for every positive heat time. -/
theorem actual_heat_native_common_tail(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ᶠ F in (sourceFilter : Filter Index),
      ∀ advanced : Bool, ∀ t : ℝ, ∀ ht : 0 < t,
        (∫⁻ w : ℝ,ENNReal.ofReal (heatNativeEnergy t ht
          (embed (phiInverseAction (phiResponseCore m ell F (actualFrequency advanced μ w)
            (heat_frequency_nonreal advanced μ hμ w) g)))))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_normalized_response_common_tail μ hμ g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced t ht
  let f:ℝ→H:=fun w=>embed (phiInverseAction (phiResponseCore m ell F (actualFrequency advanced μ w)
    (heat_frequency_nonreal advanced μ hμ w) g))
  have hB:(∫⁻ w : ℝ,ENNReal.ofReal (‖f w‖^2))≤ENNReal.ofReal (ε/4):=hF advanced
  calc
    _≤∫⁻ w : ℝ,ENNReal.ofReal 4*ENNReal.ofReal (‖f w‖^2):=by
      apply lintegral_mono;intro w
      change ENNReal.ofReal (heatNativeEnergy t ht (f w)) ≤ ENNReal.ofReal 4*ENNReal.ofReal (‖f w‖^2)
      rw [←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤4)]
      exact ENNReal.ofReal_le_ofReal (heat_native_energy_bound t ht (f w))
    _=ENNReal.ofReal 4*(∫⁻ w : ℝ,ENNReal.ofReal (‖f w‖^2)):=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _≤ENNReal.ofReal 4*ENNReal.ofReal (ε/4):=mul_le_mul le_rfl hB zero_le zero_le
    _=ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤4)]
      congr 1
      ring

abbrev clockProfileAction (c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z) (α:ℝ):End:=
  profileCore ⟨c,hc,hi⟩ α

theorem clockProfileAction_pair (c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z) (α:ℝ)(f g:QuantumTest):
    sourcePair (clockProfileAction c hc hi α f) (clockProfileAction c hc hi α g)=sourcePair f g:=
  profileCore_pair ⟨c,hc,hi⟩ α f g

theorem clockProfileAction_D (c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z) (α:ℝ):
    Commute combinedGenerator (clockProfileAction c hc hi α):=
  D_profile ⟨c,hc,hi⟩ α

theorem clockProfileAction_continuous (c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u:ℝ,∀z:SourceCoordinateSlice,c (combinedMap u z)=c z) (f:QuantumTest):
    Continuous (fun α:ℝ=>embed (clockProfileAction c hc hi α f)):=
  profile_core_continuous ⟨c,hc,hi⟩ f

theorem actual_heat_operator_core(t:ℝ)(ht:0<t)(f:QuantumTest):
    heatOperator t ht (embed f)=heatMeanCore t ht f:=
  heatOperator_core t ht f

end LowEnergy.ClockPhiConservativeHeatSource
