import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiMatchedDiffusionSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiMatchedNoiseCore
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceGaugeRadialCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceScalarInverseBulk Set Function
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest

def combinedMap(t:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  SourceGaugeScaleTransport.scaleEquiv (-t) (SourceScalarAffineScaleTransport.scaleEquiv t z)
theorem combinedMap_apply(t:ℝ)(z:SourceCoordinateSlice):combinedMap t z=
    (z.1,Real.exp t • (z.2.1+vacuumSlice)-vacuumSlice,Real.exp (-t) • z.2.2):=rfl
private theorem combinedMap_zero(z:SourceCoordinateSlice):combinedMap 0 z=z:=by
  simp only [combinedMap_apply,Real.exp_zero,neg_zero,one_smul,add_sub_cancel_right]
private theorem combinedMap_add(t s:ℝ)(z:SourceCoordinateSlice):
    combinedMap t (combinedMap s z)=combinedMap (t+s) z:=by
  simp only [combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add]
  congr 2
  congr 1
  ring
private theorem combinedMap_chart(t:ℝ)(z:SourceCoordinateSlice):
    combinedMap t z∈physicalChart ↔ z∈physicalChart:=by
  have hg:=SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-t)) (Real.exp_pos (-t))
    (SourceScalarAffineScaleTransport.scaleEquiv t z)
  have hp:=SourceScalarAffineScaleTransport.scale_chart_iff t z
  exact hg.trans hp
private theorem combinedMap_smooth:ContDiff ℝ ∞
    (fun p:ℝ×SourceCoordinateSlice=>combinedMap p.1 p.2):=by
  simp only [combinedMap_apply]
  fun_prop

def parameter(r s:ℝ)(z:SourceCoordinateSlice):ℝ:=
  r*inverseRootVolume z+s*reciprocalVolume z
def localMap(r s:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (parameter r s z) z
private theorem parameter_invariant(r s t:ℝ)(z:SourceCoordinateSlice):
    parameter r s (combinedMap t z)=parameter r s z:=rfl
private theorem localMap_zero(z:SourceCoordinateSlice):localMap 0 0 z=z:=by
  simp only [localMap,parameter,zero_mul,add_zero,combinedMap_zero]
private theorem localMap_add(r s r' s':ℝ)(z:SourceCoordinateSlice):
    localMap r s (localMap r' s' z)=localMap (r+r') (s+s') z:=by
  simp only [localMap,parameter_invariant,combinedMap_add]
  congr 1
  unfold parameter
  ring
private theorem localMap_inverse(r s:ℝ)(z:SourceCoordinateSlice):
    localMap (-r) (-s) (localMap r s z)=z:=by
  rw [localMap_add,neg_add_cancel,neg_add_cancel,localMap_zero]
private theorem localMap_chart(r s:ℝ)(z:SourceCoordinateSlice):
    localMap r s z∈physicalChart ↔ z∈physicalChart:=combinedMap_chart _ _
theorem parameter_smooth(r s:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (parameter r s) z.val:=by
  exact (contDiffAt_const.mul (inverse_root_volume_smooth z)).add
    (contDiffAt_const.mul (reciprocal_volume_smooth z))
theorem localMap_smooth(r s:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (localMap r s) z.val:=by
  have hp:ContDiffAt ℝ ∞ (parameter r s) z.val:=parameter_smooth r s z
  have hi:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>x) z.val:=contDiffAt_id
  have hk:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(parameter r s x,x)) z.val:=hp.prodMk hi
  have hc:ContDiffAt ℝ ∞ (fun p:ℝ×SourceCoordinateSlice=>combinedMap p.1 p.2)
      (parameter r s z.val,z.val):=combinedMap_smooth.contDiffAt
  have h:=ContDiffAt.comp (f:=fun x:SourceCoordinateSlice=>(parameter r s x,x)) z.val hc hk
  change ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>combinedMap (parameter r s x) x) z.val
  exact h

def noiseValue(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):FockFiber:=
  (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z)
private def noiseSupport(r s:ℝ)(f:QuantumTest):Set SourceCoordinateSlice:=
  localMap (-r) (-s) '' tsupport f
private theorem noiseSupport_compact(r s:ℝ)(f:QuantumTest):IsCompact (noiseSupport r s f):=by
  apply f.hasCompactSupport.image_of_continuousOn
  intro z hz
  exact (localMap_smooth (-r) (-s) ⟨z,f.tsupport_subset hz⟩).continuousAt.continuousWithinAt
private theorem noiseSupport_chart(r s:ℝ)(f:QuantumTest):noiseSupport r s f⊆physicalChart:=by
  rintro z ⟨x,hx,rfl⟩
  exact (localMap_chart (-r) (-s) x).mpr (f.tsupport_subset hx)
private theorem noise_support(r s:ℝ)(f:QuantumTest):tsupport (noiseValue r s f)⊆noiseSupport r s f:=by
  apply closure_minimal _ (noiseSupport_compact r s f).isClosed
  intro z hz
  have hv:f (localMap r s z)≠0:=by
    intro hf
    exact hz (by simp only [noiseValue,hf,smul_zero])
  exact ⟨localMap r s z,subset_tsupport f hv,localMap_inverse r s z⟩
private theorem noise_zero(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)
    (hz:z∉noiseSupport r s f):noiseValue r s f z=0:=
  image_eq_zero_of_notMem_tsupport (fun h=>hz (noise_support r s f h))
private theorem noise_smooth(r s:ℝ)(f:QuantumTest):ContDiff ℝ ∞ (noiseValue r s f):=by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz:z∈noiseSupport r s f
  · have hp:=parameter_smooth r s ⟨z,noiseSupport_chart r s f hz⟩
    have hm:=localMap_smooth r s ⟨z,noiseSupport_chart r s f hz⟩
    have he:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>(Real.exp ((25/2:ℝ)*parameter r s x):ℂ)) z:=by
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp z ((contDiffAt_const.mul hp).exp)
    exact he.smul (f.contDiff.contDiffAt.comp z hm)
  · apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [(noiseSupport_compact r s f).isClosed.isOpen_compl.mem_nhds hz] with x hx
    exact noise_zero r s f x hx

def noiseCore(r s:ℝ):End where
  toFun f:=
    { toFun:=noiseValue r s f
      contDiff':=noise_smooth r s f
      hasCompactSupport':=(noiseSupport_compact r s f).of_isClosed_subset isClosed_closure (noise_support r s f)
      tsupport_subset':=(noise_support r s f).trans (noiseSupport_chart r s f) }
  map_add' f g:=by
    apply DFunLike.ext
    intro z
    change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • (f (localMap r s z)+g (localMap r s z))=_
    exact smul_add _ _ _
  map_smul' c f:=by
    apply DFunLike.ext
    intro z
    change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • (c • f (localMap r s z))=_
    exact smul_comm _ _ _
theorem noiseCore_zero(f:QuantumTest):noiseCore 0 0 f=f:=by
  apply DFunLike.ext
  intro z
  change noiseValue 0 0 f z=f z
  simp only [noiseValue,parameter,zero_mul,add_zero,mul_zero,Real.exp_zero,
    Complex.ofReal_one,one_smul,localMap_zero]

theorem noiseCore_add(r s r' s':ℝ)(f:QuantumTest):
    noiseCore r s (noiseCore r' s' f)=noiseCore (r+r') (s+s') f:=by
  apply DFunLike.ext
  intro z
  have hp:parameter r' s' (localMap r s z)=parameter r' s' z:=parameter_invariant _ _ _ _
  have hm:localMap r' s' (localMap r s z)=localMap (r+r') (s+s') z:=by
    rw [localMap_add,add_comm r' r,add_comm s' s]
  have ha:parameter r s z+parameter r' s' z=parameter (r+r') (s+s') z:=by
    unfold parameter;ring
  change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
    ((Real.exp ((25/2:ℝ)*parameter r' s' (localMap r s z)):ℂ) • f (localMap r' s' (localMap r s z)))=_
  rw [hp,hm,smul_smul,←Complex.ofReal_mul,←Real.exp_add,←mul_add,ha]
  rfl
theorem noiseCore_inverse(r s:ℝ)(f:QuantumTest):
    noiseCore (-r) (-s) (noiseCore r s f)=f:=by
  rw [noiseCore_add,neg_add_cancel,neg_add_cancel,noiseCore_zero]
theorem noiseCore_root(r s:ℝ):Commute (noiseCore r s) inverseRootAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
    ((inverseRootVolume (localMap r s z):ℂ) • f (localMap r s z))=
      (inverseRootVolume z:ℂ) • ((Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z))
  have hi:inverseRootVolume (localMap r s z)=inverseRootVolume z:=rfl
  rw [hi]
  exact smul_comm _ _ _
theorem noiseCore_weight(r s:ℝ):Commute (noiseCore r s) inverseVolumeAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
    ((reciprocalVolume (localMap r s z):ℂ) • f (localMap r s z))=
      (reciprocalVolume z:ℂ) • ((Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z))
  have hi:reciprocalVolume (localMap r s z)=reciprocalVolume z:=rfl
  rw [hi]
  exact smul_comm _ _ _

private abbrev ParameterPoint:=(ℝ×ℝ)×SourceCoordinateSlice
private def jointParameter(p:ParameterPoint):ℝ:=parameter p.1.1 p.1.2 p.2
private def jointMap(p:ParameterPoint):SourceCoordinateSlice:=localMap p.1.1 p.1.2 p.2
private def jointInverse(p:ParameterPoint):SourceCoordinateSlice:=localMap (-p.1.1) (-p.1.2) p.2
private theorem jointParameter_smooth(p:ParameterPoint)(hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ jointParameter p:=by
  have ha:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>inverseRootVolume x.2) p:=
    ContDiffAt.comp (f:=fun x:ParameterPoint=>x.2) p (inverse_root_volume_smooth ⟨p.2,hp⟩) contDiffAt_snd
  have hu:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>reciprocalVolume x.2) p:=
    ContDiffAt.comp (f:=fun x:ParameterPoint=>x.2) p (reciprocal_volume_smooth ⟨p.2,hp⟩) contDiffAt_snd
  exact ((contDiffAt_fst.fst).mul ha).add ((contDiffAt_fst.snd).mul hu)
private theorem jointMap_smooth(p:ParameterPoint)(hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ jointMap p:=by
  have hj:=jointParameter_smooth p hp
  have hs:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>x.2) p:=contDiffAt_snd
  have hk:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>(jointParameter x,x.2)) p:=hj.prodMk hs
  have hc:ContDiffAt ℝ ∞ (fun x:ℝ×SourceCoordinateSlice=>combinedMap x.1 x.2)
      (jointParameter p,p.2):=combinedMap_smooth.contDiffAt
  have h:=ContDiffAt.comp (f:=fun x:ParameterPoint=>(jointParameter x,x.2)) p hc hk
  change ContDiffAt ℝ ∞ (fun x:ParameterPoint=>combinedMap (jointParameter x) x.2) p
  exact h
private theorem jointInverse_smooth(p:ParameterPoint)(hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ jointInverse p:=by
  have hn:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>((-x.1.1,-x.1.2),x.2)) p:=by fun_prop
  have hc:=jointMap_smooth ((-p.1.1,-p.1.2),p.2) hp
  have h:=ContDiffAt.comp (f:=fun x:ParameterPoint=>((-x.1.1,-x.1.2),x.2)) p hc hn
  change ContDiffAt ℝ ∞ (fun x:ParameterPoint=>jointMap ((-x.1.1,-x.1.2),x.2)) p
  exact h
private def commonSupport(R S:ℝ)(f:QuantumTest):Set SourceCoordinateSlice:=
  jointInverse '' ((Icc (-R) R ×ˢ Icc (-S) S) ×ˢ tsupport f)
private theorem commonSupport_compact(R S:ℝ)(f:QuantumTest):IsCompact (commonSupport R S f):=by
  apply ((isCompact_Icc.prod isCompact_Icc).prod f.hasCompactSupport).image_of_continuousOn
  intro p hp
  exact (jointInverse_smooth p (f.tsupport_subset hp.2)).continuousAt.continuousWithinAt
private theorem commonSupport_chart(R S:ℝ)(f:QuantumTest):commonSupport R S f⊆physicalChart:=by
  rintro z ⟨p,hp,rfl⟩
  exact (localMap_chart (-p.1.1) (-p.1.2) p.2).mpr (f.tsupport_subset hp.2)
private theorem noise_common_support(r s R S:ℝ)(f:QuantumTest)
    (hr:r∈Icc (-R) R)(hs:s∈Icc (-S) S):tsupport (noiseCore r s f)⊆commonSupport R S f:=by
  intro z hz
  have h:=noise_support r s f hz
  rcases h with ⟨x,hx,rfl⟩
  exact ⟨((r,s),x),⟨⟨hr,hs⟩,hx⟩,rfl⟩
private theorem noise_joint_smooth(f:QuantumTest)(p:ParameterPoint)(hp:p.2∈physicalChart):
    ContDiffAt ℝ ∞ (fun x:ParameterPoint=>noiseValue x.1.1 x.1.2 f x.2) p:=by
  have hj:=jointParameter_smooth p hp
  have hc:ContDiffAt ℝ ∞ (fun x:ParameterPoint=>(Real.exp ((25/2:ℝ)*jointParameter x):ℂ)) p:=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p ((contDiffAt_const.mul hj).exp)
  have hf:=f.contDiff.contDiffAt.comp p (jointMap_smooth p hp)
  exact hc.smul hf

open SourceGaugeRadialPair SourceClockPhiCombinedScalePressure
private abbrev D:End:=combinedGenerator
def noiseGenerator(r s:ℝ):End:=
  (r:ℂ) • combinedConjugate+(s:ℂ) • (inverseVolumeAction*D)
theorem combined_generator_point(f:QuantumTest)(z:SourceCoordinateSlice):
    D f z=fderiv ℝ f z (phiEuler z-gaugeEuler z)+(25/2:ℂ) • f z:=by
  change (phiEulerAction f z+(61/2:ℂ) • f z)-
    (gaugeEulerAction f z+(18:ℂ) • f z)=_
  rw [phi_euler_apply,gauge_euler_apply,map_sub]
  module
private theorem noiseGenerator_point(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    noiseGenerator r s f z=(parameter r s z:ℂ) • D f z:=by
  change (r:ℂ) • ((inverseRootVolume z:ℂ) • D f z)+
    (s:ℂ) • ((reciprocalVolume z:ℂ) • D f z)=_
  simp only [parameter,Complex.ofReal_add,Complex.ofReal_mul,smul_smul,add_smul]
private theorem combinedMap_zero_jet(z:SourceCoordinateSlice):
    HasDerivAt (fun t:ℝ=>combinedMap t z) (phiEuler z-gaugeEuler z) 0:=by
  have he:HasDerivAt Real.exp (1:ℝ) 0:=by simpa using Real.hasDerivAt_exp (0:ℝ)
  have hn:HasDerivAt (fun t:ℝ=>Real.exp (-t)) (-1:ℝ) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).neg.exp)
  have h:HasDerivAt (fun t:ℝ=>(z.1,Real.exp t • (z.2.1+vacuumSlice)-vacuumSlice,
      Real.exp (-t) • z.2.2))
      ((0:Coframe),(1:ℝ) • (z.2.1+vacuumSlice),(-1:ℝ) • z.2.2) 0:=
    (hasDerivAt_const (0:ℝ) z.1).prodMk
      (((he.smul_const (z.2.1+vacuumSlice)).sub_const vacuumSlice).prodMk (hn.smul_const z.2.2))
  have hd:((0:Coframe),(1:ℝ) • (z.2.1+vacuumSlice),(-1:ℝ) • z.2.2)=phiEuler z-gaugeEuler z:=by
    simp [phiEuler,gaugeEuler,add_comm]
  exact (h.congr_deriv hd).congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _=>rfl))
private theorem phi_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    phiEulerAction f z word=fderiv ℝ (component word f) z (phiEuler z):=by
  have h:=congrArg (fun g:GaussDensityCore.ScalarTest=>g z)
    (GaussCoframeCore.component_derivative (phiEuler z) f word)
  change GaussCoframeCore.derivative (phiEuler z) f z word=
    GaussDensityCore.derivative (phiEuler z) (component word f) z at h
  simp only [GaussCoframeCore.derivative_apply,GaussDensityCore.derivative_apply] at h
  exact (congrArg (fun v:FockFiber=>v word) (phi_euler_apply f z)).trans h
private theorem combined_generator_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    D f z word=fderiv ℝ (component word f) z (phiEuler z-gaugeEuler z)+(25/2:ℂ)*f z word:=by
  change (phiEulerAction f z word+(61/2:ℂ)*f z word)-
    (gaugeEulerAction f z word+(18:ℂ)*f z word)=_
  rw [phi_component,gauge_euler_component,map_sub]
  ring
private theorem noiseGenerator_component(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    noiseGenerator r s f z word=(parameter r s z:ℂ)*(D f z word):=by
  exact congrArg (fun v:FockFiber=>v word) (noiseGenerator_point r s f z)
theorem noise_linear_zero_jet(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    HasDerivAt (fun t:ℝ=>noiseCore (t*r) (t*s) f z word) (noiseGenerator r s f z word) 0:=by
  let c:=parameter r s z
  have ht:HasDerivAt (fun t:ℝ=>t*c) c 0:=by
    simpa using (hasDerivAt_id (0:ℝ)).mul_const c
  have hx:HasDerivAt (fun t:ℝ=>combinedMap (t*c) z)
      (c • (phiEuler z-gaugeEuler z)) 0:=by
    simpa only [Function.comp_def,id_eq] using
      (combinedMap_zero_jet z).scomp_of_eq 0 ht (by simp)
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    0 hx (by simp only [zero_mul,combinedMap_zero])
  have he:HasDerivAt (fun t:ℝ=>(Real.exp ((25/2:ℝ)*(t*c)):ℂ)) ((25/2:ℂ)*(c:ℂ)) 0:=by
    have hr:=(((hasDerivAt_id (0:ℝ)).mul_const c).const_mul (25/2:ℝ)).exp
    have hc:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) hr
    simpa only [id_eq,zero_mul,mul_zero,Real.exp_zero,one_mul,Complex.ofRealCLM_apply,
      Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one,Function.comp_def] using hc
  have h:=he.mul hf
  simp only [Function.comp_def,zero_mul,mul_zero,Real.exp_zero,Complex.ofReal_one,one_mul,
    combinedMap_zero,map_smul,component_apply,Complex.real_smul] at h
  have hd:((25/2:ℂ)*(c:ℂ))*f z word+(c:ℂ)*fderiv ℝ (component word f) z (phiEuler z-gaugeEuler z)=
      noiseGenerator r s f z word:=by
    rw [noiseGenerator_component,combined_generator_component]
    change ((25/2:ℂ)*(c:ℂ))*f z word+(c:ℂ)*fderiv ℝ (component word f) z (phiEuler z-gaugeEuler z)=
      (c:ℂ)*(fderiv ℝ (component word f) z (phiEuler z-gaugeEuler z)+(25/2:ℂ)*f z word)
    ring
  have hp(t:ℝ):parameter (t*r) (t*s) z=t*c:=by dsimp only [c,parameter];ring
  have hm(t:ℝ):localMap (t*r) (t*s) z=combinedMap (t*c) z:=by rw [localMap,hp]
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t=>by
    change (Real.exp ((25/2:ℝ)*parameter (t*r) (t*s) z):ℂ)*f (localMap (t*r) (t*s) z) word=_
    rw [hp,hm]
    rfl)

theorem noise_linear_jet(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation)(t:ℝ):
    HasDerivAt (fun u:ℝ=>noiseCore (u*r) (u*s) f z word)
      (noiseGenerator r s (noiseCore (t*r) (t*s) f) z word) t:=by
  have h0:=noise_linear_zero_jet r s (noiseCore (t*r) (t*s) f) z word
  have h:HasDerivAt (fun u:ℝ=>noiseCore ((u-t)*r) ((u-t)*s) (noiseCore (t*r) (t*s) f) z word)
      (noiseGenerator r s (noiseCore (t*r) (t*s) f) z word) t:=by
    simpa only [Function.comp_def,one_smul,id_eq] using!
      h0.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u=>by
    dsimp only
    rw [noiseCore_add]
    have hr:(u-t)*r+t*r=u*r:=by ring
    have hs:(u-t)*s+t*s=u*s:=by ring
    rw [hr,hs])
theorem noiseGenerator_flow(r s t:ℝ)(f:QuantumTest):
    noiseGenerator r s (noiseCore (t*r) (t*s) f)=noiseCore (t*r) (t*s) (noiseGenerator r s f):=by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  have h1:=noise_linear_zero_jet r s (noiseCore (t*r) (t*s) f) z word
  have h2:HasDerivAt (fun u:ℝ=>noiseCore (t*r) (t*s) (noiseCore (u*r) (u*s) f) z word)
      (noiseCore (t*r) (t*s) (noiseGenerator r s f) z word) 0:=
    (noise_linear_zero_jet r s f (localMap (t*r) (t*s) z) word).const_mul
      (Real.exp ((25/2:ℝ)*parameter (t*r) (t*s) z):ℂ)
  have he:(fun u:ℝ=>noiseCore (u*r) (u*s) (noiseCore (t*r) (t*s) f) z word)=
      fun u:ℝ=>noiseCore (t*r) (t*s) (noiseCore (u*r) (u*s) f) z word:=by
    funext u
    rw [noiseCore_add,noiseCore_add,add_comm (u*r) (t*r),add_comm (u*s) (t*s)]
  rw [he] at h1
  exact h1.unique h2

open SourceScalarPairedTransport SourceScalarGaugeScale GaussLiveMomentum
private abbrev a:End:=inverseRootAction
private abbrev U:End:=inverseVolumeAction
private abbrev A:End:=combinedConjugate
private abbrev Phi:End:=SourceScalarAffineScaleTransport.generator
private abbrev Gauge:End:=SourceGaugeScaleTransport.generator
private theorem pair_add_l (f g h:QuantumTest) : sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]

private theorem pair_add_r (f g h:QuantumTest) : sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]

private theorem pair_sub_l (f g h:QuantumTest) : sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]

private theorem pair_sub_r (f g h:QuantumTest) : sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]

private theorem pair_smul_l (c:ℂ)(f g:QuantumTest) : sourcePair (c • f) g=(starRingEnd ℂ c)*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_left]

private theorem pair_smul_r (c:ℂ)(f g:QuantumTest) : sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private theorem self_pair (f:QuantumTest) : sourcePair f f=(‖embed f‖^2:ℂ) := by
  simpa only [sourcePair,Complex.ofReal_pow] using!
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (embed f)

private theorem flow_pair_generator (flow:ℝ → End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g) :=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq

private theorem phi_pair (f g:QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g

private theorem gauge_pair (f g:QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g

private theorem combined_pair (f g:QuantumTest) :
    sourcePair f (combinedGenerator g)= -sourcePair (combinedGenerator f) g := by
  simp only [combinedGenerator,LinearMap.sub_apply,pair_sub_l,pair_sub_r,phi_pair,gauge_pair]
  ring

private theorem weight_pair (f g:QuantumTest) : sourcePair f (U g)=sourcePair (U f) g :=
  multiply_pair _ _ f g

private theorem real_commute (c d:SourceCoordinateSlice → ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)

private theorem weight_combined : Commute U D := by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change U*(Phi-Gauge)=(Phi-Gauge)*U
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem weighted_pair (f g:QuantumTest):sourcePair f (U (D g))= -sourcePair (U (D f)) g := by
  rw [weight_pair,combined_pair]
  have hc:=LinearMap.congr_fun weight_combined.eq f
  change U (D f)=D (U f) at hc
  rw [←hc]
private def phiScale (r : ℝ) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (z.1,r • (vacuumSlice+z.2.1)-vacuumSlice,z.2.2)
private theorem phi_scale_one (z : SourceCoordinateSlice) : phiScale 1 z=z := by
  simp [phiScale]
private theorem phi_scale_derivative (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => phiScale r z) (phiEuler z) 1 := by
  simpa only [phiScale,phiEuler,id_eq,one_smul] using!
    (hasDerivAt_const (1 : ℝ) z.1).prodMk
      ((((hasDerivAt_id (1 : ℝ)).smul_const (vacuumSlice+z.2.1)).sub_const vacuumSlice).prodMk
        (hasDerivAt_const (1 : ℝ) z.2.2))


private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 1) (hz : γ 1=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 1 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem euler_multiplier (E : End) (e : SourceCoordinateSlice → SourceCoordinateSlice)
    (flow : ℝ → SourceCoordinateSlice → SourceCoordinateSlice)
    (hE : ∀ f z,E f z=fderiv ℝ f z (e z))
    (hg : ∀ z,HasDerivAt (fun r => flow r z) (e z) 1) (h1 : ∀ z,flow 1 z=z)
    (A : End) (B : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (law : ∀ f z,A f z=B z (f z)) (hinv : ∀ r z,B (flow r z)=B z) : E*A-A*E=0 := by
  apply sub_eq_zero.mpr
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change E (A f) z=A (E f) z
  rw [hE,law,hE]
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((B z).restrictScalars ℝ) f (A f) (fun r => flow r z) z (e z)
    (hg z) (h1 z) ((f.contDiff.differentiable (by simp)) z) (((A f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [law,hinv]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars'] using! h

private theorem root_commute:Commute a D := by
  have hp:phiEulerAction*a-a*phiEulerAction=0:=
    euler_multiplier phiEulerAction phiEuler phiScale phi_euler_apply phi_scale_derivative phi_scale_one a
      (fun z=>(inverseRootVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _=>rfl) (fun _ _=>rfl)
  have hg:gaugeEulerAction*a-a*gaugeEulerAction=0:=
    euler_multiplier gaugeEulerAction gaugeEuler gaugeScale gauge_euler_apply (fun z=>gauge_scale_derivative z 1) gauge_scale_one a
      (fun z=>(inverseRootVolume z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) (fun _ _=>rfl) (fun _ _=>rfl)
  change a*(Phi-Gauge)=(Phi-Gauge)*a
  unfold Phi Gauge SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem root_pair(f g:QuantumTest):sourcePair f (a g)=sourcePair (a f) g:=multiply_pair _ _ f g
private theorem conjugate_pair(f g:QuantumTest):sourcePair f (A g)= -sourcePair (A f) g:=by
  change sourcePair f (a (D g))= -sourcePair (a (D f)) g
  rw [root_pair,combined_pair]
  have h:=LinearMap.congr_fun root_commute.eq f
  change a (D f)=D (a f) at h
  rw [←h]
theorem noiseGenerator_pair(r s:ℝ)(f g:QuantumTest):
    sourcePair f (noiseGenerator r s g)= -sourcePair (noiseGenerator r s f) g:=by
  simp only [noiseGenerator,LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,
    pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,conjugate_pair,weighted_pair,Complex.conj_ofReal]
  ring

theorem noise_joint_contDiff(f:QuantumTest):
    ContDiff ℝ ∞ (fun x:ParameterPoint=>noiseCore x.1.1 x.1.2 f x.2):=by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp:p.2∈physicalChart
  · exact noise_joint_smooth f p hp
  · let R:ℝ:=|p.1.1|+1
    let S:ℝ:=|p.1.2|+1
    have hr:p.1.1∈Ioo (-R) R:=by
      have h1:=le_abs_self p.1.1
      have h2:=neg_abs_le p.1.1
      dsimp only [R]
      constructor <;> linarith
    have hs:p.1.2∈Ioo (-S) S:=by
      have h1:=le_abs_self p.1.2
      have h2:=neg_abs_le p.1.2
      dsimp only [S]
      constructor <;> linarith
    have hz:p.2∉commonSupport R S f:=fun h=>hp (commonSupport_chart R S f h)
    have hrN:{x:ParameterPoint|x.1.1∈Ioo (-R) R}∈nhds p:=
      (isOpen_Ioo.preimage (continuous_fst.fst)).mem_nhds hr
    have hsN:{x:ParameterPoint|x.1.2∈Ioo (-S) S}∈nhds p:=
      (isOpen_Ioo.preimage (continuous_fst.snd)).mem_nhds hs
    have hzN:{x:ParameterPoint|x.2∉commonSupport R S f}∈nhds p:=
      ((commonSupport_compact R S f).isClosed.isOpen_compl.preimage continuous_snd).mem_nhds hz
    apply (contDiffAt_const (c:=(0:FockFiber))).congr_of_eventuallyEq
    filter_upwards [hrN,hsN,hzN] with x hx hy hz
    exact image_eq_zero_of_notMem_tsupport (fun h=>hz
      (noise_common_support x.1.1 x.1.2 R S f ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩ h))
private theorem component_noise_continuous(r s:ℝ)(f:QuantumTest)(word:Occupation):
    Continuous (fun p:ℝ×SourceCoordinateSlice=>noiseCore (p.1*r) (p.1*s) f p.2 word):=by
  have h:Continuous (fun p:ℝ×SourceCoordinateSlice=>((p.1*r,p.1*s),p.2)):=by fun_prop
  have he:Continuous (fun v:FockFiber=>v word):=
    (PiLp.proj 2 (fun _:Occupation=>ℂ) word:FockFiber→L[ℂ]ℂ).continuous
  exact he.comp ((noise_joint_contDiff f).continuous.comp h)

open MeasureTheory Filter
private theorem density_continuous(N:ℕ):Continuous (GaussDensityCore.complexDensity N):=by
  have hg:Continuous (fun z:SourceCoordinateSlice=>(z.2.2:SourceQuantumConfigurationHilbert.Gauge)):=by fun_prop
  have hv:Continuous (fun z:SourceCoordinateSlice=>z.1 0*z.1 2*z.1 5):=by fun_prop
  exact Complex.continuous_ofReal.comp ((GaussHistoryHilbert.jacobian_continuous.comp hg).mul (hv.pow _))
private def pairKernel(r s:ℝ)(f g:QuantumTest)(t:ℝ)(z:SourceCoordinateSlice):ℂ:=
  densityPair (noiseCore (t*r) (t*s) f) (noiseCore (t*r) (t*s) g) z
private theorem pairKernel_continuous(r s:ℝ)(f g:QuantumTest):
    Continuous (fun p:ℝ×SourceCoordinateSlice=>pairKernel r s f g p.1 p.2):=by
  have he:(fun p:ℝ×SourceCoordinateSlice=>pairKernel r s f g p.1 p.2)=
      fun p=>∑word:Occupation,GaussDensityCore.complexDensity word.card p.2*
        star (noiseCore (p.1*r) (p.1*s) f p.2 word)*noiseCore (p.1*r) (p.1*s) g p.2 word:=by
    funext p
    exact densityPair_sum _ _ _
  rw [he]
  apply continuous_finsetSum
  intro word _
  exact (((density_continuous word.card).comp continuous_snd).mul
    (component_noise_continuous r s f word).star).mul (component_noise_continuous r s g word)
private theorem pairKernel_derivative(r s:ℝ)(f g:QuantumTest)(z:SourceCoordinateSlice)(t:ℝ):
    HasDerivAt (fun u:ℝ=>pairKernel r s f g u z)
      (pairKernel r s (noiseGenerator r s f) g t z+pairKernel r s f (noiseGenerator r s g) t z) t:=by
  have hw(word:Occupation):HasDerivAt
      (fun u:ℝ=>GaussDensityCore.complexDensity word.card z*
        star (noiseCore (u*r) (u*s) f z word)*noiseCore (u*r) (u*s) g z word)
      (GaussDensityCore.complexDensity word.card z*
        star (noiseCore (t*r) (t*s) (noiseGenerator r s f) z word)*noiseCore (t*r) (t*s) g z word+
       GaussDensityCore.complexDensity word.card z*
        star (noiseCore (t*r) (t*s) f z word)*noiseCore (t*r) (t*s) (noiseGenerator r s g) z word) t:=by
    have hf:=noise_linear_jet r s f z word t
    have hg:=noise_linear_jet r s g z word t
    rw [noiseGenerator_flow] at hf hg
    have h:=((hf.star).const_mul (GaussDensityCore.complexDensity word.card z)).mul hg
    exact h.congr_deriv (by ring)
  have h:=HasDerivAt.sum (u:=(Finset.univ:Finset Occupation)) (fun word _=>hw word)
  have hd:(∑word:Occupation,
      (GaussDensityCore.complexDensity word.card z*
        star (noiseCore (t*r) (t*s) (noiseGenerator r s f) z word)*noiseCore (t*r) (t*s) g z word+
       GaussDensityCore.complexDensity word.card z*
        star (noiseCore (t*r) (t*s) f z word)*noiseCore (t*r) (t*s) (noiseGenerator r s g) z word))=
      pairKernel r s (noiseGenerator r s f) g t z+pairKernel r s f (noiseGenerator r s g) t z:=by
    rw [Finset.sum_add_distrib]
    simp only [pairKernel,densityPair_sum]
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u=>by
    dsimp only
    simp only [Finset.sum_apply]
    exact densityPair_sum _ _ _)
private theorem pairKernel_zero(r s:ℝ)(f g:QuantumTest)(t:ℝ)(z:SourceCoordinateSlice)
    (hz:z∉tsupport (noiseCore (t*r) (t*s) f)):pairKernel r s f g t z=0:=by
  unfold pairKernel densityPair
  rw [image_eq_zero_of_notMem_tsupport hz,map_zero,inner_zero_left]
private theorem pair_flow_derivative(r s:ℝ)(f g:QuantumTest)(t:ℝ):
    HasDerivAt (fun u:ℝ=>sourcePair (noiseCore (u*r) (u*s) f) (noiseCore (u*r) (u*s) g)) 0 t:=by
  let R:ℝ:=(|t|+1)*|r|
  let S:ℝ:=(|t|+1)*|s|
  let K:Set SourceCoordinateSlice:=commonSupport R S f∪commonSupport R S (noiseGenerator r s f)
  have hK:IsCompact K:=(commonSupport_compact R S f).union (commonSupport_compact R S (noiseGenerator r s f))
  have hpar(u:ℝ)(hu:u∈Icc (t-1) (t+1)):(u*r∈Icc (-R) R)∧(u*s∈Icc (-S) S):=by
    have h1:=le_abs_self t
    have h2:=neg_abs_le t
    have hb:|u|≤ |t|+1:=by apply abs_le.mpr;constructor <;> linarith only [hu.1,hu.2,h1,h2]
    constructor
    · exact abs_le.mp (by simpa only [R,abs_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg r))
    · exact abs_le.mp (by simpa only [S,abs_mul] using mul_le_mul_of_nonneg_right hb (abs_nonneg s))
  let F:=pairKernel r s f g
  let F':=fun u z=>pairKernel r s (noiseGenerator r s f) g u z+pairKernel r s f (noiseGenerator r s g) u z
  have hcont:Continuous (fun p:ℝ×SourceCoordinateSlice=>F' p.1 p.2):=
    (pairKernel_continuous r s (noiseGenerator r s f) g).add (pairKernel_continuous r s f (noiseGenerator r s g))
  obtain ⟨C,hC⟩:=(isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hcont.continuousOn:ContinuousOn (fun p:ℝ×SourceCoordinateSlice=>F' p.1 p.2)
      (Icc (t-1) (t+1)×ˢK))
  let bound:SourceCoordinateSlice→ℝ:=K.indicator (fun _=>C)
  have hbound:Integrable bound GaussHistoryHilbert.configurationMeasure:=
    (integrableOn_const (μ:=GaussHistoryHilbert.configurationMeasure) (C:=C) hK.measure_ne_top).integrable_indicator hK.isClosed.measurableSet
  have hd:=hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := GaussHistoryHilbert.configurationMeasure) (F := F) (F' := F') (bound := bound)
    (Ioo_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (Filter.Eventually.of_forall (fun u=>(densityPair_integrable (noiseCore (u*r) (u*s) f) (noiseCore (u*r) (u*s) g)).aestronglyMeasurable))
    (densityPair_integrable (noiseCore (t*r) (t*s) f) (noiseCore (t*r) (t*s) g))
    ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z=>by
      intro u hu
      by_cases hz:z∈K
      · change ‖F' u z‖≤ K.indicator (fun _=>C) z
        rw [Set.indicator_of_mem hz]
        exact hC (u,z) ⟨⟨hu.1.le,hu.2.le⟩,hz⟩
      · have hp:=hpar u ⟨hu.1.le,hu.2.le⟩
        have hf:z∉tsupport (noiseCore (u*r) (u*s) f):=fun h=>hz (Or.inl (noise_common_support _ _ _ _ _ hp.1 hp.2 h))
        have hgf:z∉tsupport (noiseCore (u*r) (u*s) (noiseGenerator r s f)):=fun h=>hz (Or.inr (noise_common_support _ _ _ _ _ hp.1 hp.2 h))
        change ‖pairKernel r s (noiseGenerator r s f) g u z+pairKernel r s f (noiseGenerator r s g) u z‖≤K.indicator (fun _=>C) z
        rw [pairKernel_zero r s _ _ u z hgf,pairKernel_zero r s _ _ u z hf,
          Set.indicator_of_notMem hz,add_zero,norm_zero]))
    hbound (Filter.Eventually.of_forall (fun z u _=>pairKernel_derivative r s f g z u))
  have he:(fun u=>∫z,F u z ∂GaussHistoryHilbert.configurationMeasure)=
      fun u=>sourcePair (noiseCore (u*r) (u*s) f) (noiseCore (u*r) (u*s) g):=by
    funext u
    exact (sourcePair_integral _ _).symm
  rw [he] at hd
  have hv:(∫z,F' t z ∂GaussHistoryHilbert.configurationMeasure)=0:=by
    change (∫z,densityPair (noiseCore (t*r) (t*s) (noiseGenerator r s f)) (noiseCore (t*r) (t*s) g) z+
      densityPair (noiseCore (t*r) (t*s) f) (noiseCore (t*r) (t*s) (noiseGenerator r s g)) z ∂GaussHistoryHilbert.configurationMeasure)=0
    rw [integral_add (densityPair_integrable _ _) (densityPair_integrable _ _),
      ←sourcePair_integral,←sourcePair_integral,←noiseGenerator_flow,←noiseGenerator_flow,noiseGenerator_pair]
    ring
  rw [hv] at hd
  exact hd.2
theorem noiseCore_pair(r s:ℝ)(f g:QuantumTest):
    sourcePair (noiseCore r s f) (noiseCore r s g)=sourcePair f g:=by
  have h:=is_const_of_deriv_eq_zero
    (fun t=>(pair_flow_derivative r s f g t).differentiableAt)
    (fun t=>(pair_flow_derivative r s f g t).deriv) (1:ℝ) 0
  simpa only [one_mul,zero_mul,noiseCore_zero] using! h

open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
private theorem map_scalar_field(t:ℝ)(z:SourceCoordinateSlice):
    vacuum+((combinedMap t z).2.1:Scalar)=Real.exp t • (vacuum+(z.2.1:Scalar)):=by
  change vacuum+(Real.exp t • ((z.2.1:Scalar)+vacuum)-vacuum)=_
  module
private theorem action_scale(r s:ℝ)(phi:Scalar)(b:SourceQuantumScalarChart.NativeLie):
    action (r • phi) (s • b)=(r*s) • action phi b:=by
  change scalarP286ActionBilinear (s • b) (r • phi)=(r*s) • scalarP286ActionBilinear b phi
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
private theorem gauge_scale(r s:ℝ)(b:SourceQuantumScalarChart.NativeLie)(v:SourceQuantumConfigurationHilbert.Gauge):
    nativeGauge (s • b) (r • v)=(r*s) • nativeGauge b v:=by
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
private theorem inverse_scalar_finite(t:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    inverseL (combinedMap t z.val) v=
      (Real.exp (-t) • (inverseL z.val v).1,(inverseL z.val v).2.1,
        Real.exp (-2*t) • (inverseL z.val v).2.2):=by
  let z':physicalChart:=⟨combinedMap t z.val,(combinedMap_chart t z.val).mpr z.property⟩
  let u:=inverseL z.val v
  let u':Split:=(Real.exp (-t) • u.1,u.2.1,Real.exp (-2*t) • u.2.2)
  have hs:=congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1:Scalar)) u.1+(u.2.1:Scalar)=v.1 at hs
  have hg:=congrArg Prod.snd (inverse_right z v)
  change nativeGauge u.1 (z.val.2.2:SourceQuantumConfigurationHilbert.Gauge)+
    (u.2.2:SourceQuantumConfigurationHilbert.Gauge)=v.2 at hg
  have hcancel:Real.exp t*Real.exp (-t)=1:=by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hsq:Real.exp (-t)*Real.exp (-t)=Real.exp (-2*t):=by rw [←Real.exp_add];congr 1;ring
  have hp:splitMap z'.val u'=v:=by
    apply Prod.ext
    · change action (vacuum+((combinedMap t z.val).2.1:Scalar)) (Real.exp (-t) • u.1)+(u.2.1:Scalar)=v.1
      rw [map_scalar_field,action_scale,hcancel,one_smul]
      exact hs
    · change nativeGauge (Real.exp (-t) • u.1) (Real.exp (-t) • (z.val.2.2:SourceQuantumConfigurationHilbert.Gauge))+
        Real.exp (-2*t) • (u.2.2:SourceQuantumConfigurationHilbert.Gauge)=v.2
      rw [gauge_scale,hsq,←smul_add,hg,hv,smul_zero]
  exact (congrArg (inverseL z'.val) hp).symm.trans (inverse_left z' u')
private theorem inverse_gauge_finite(t:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    inverseL (combinedMap t z.val) v=
      (Real.exp t • (inverseL z.val v).1,Real.exp (2*t) • (inverseL z.val v).2.1,
        (inverseL z.val v).2.2):=by
  let z':physicalChart:=⟨combinedMap t z.val,(combinedMap_chart t z.val).mpr z.property⟩
  let u:=inverseL z.val v
  let u':Split:=(Real.exp t • u.1,Real.exp (2*t) • u.2.1,u.2.2)
  have hs:=congrArg Prod.fst (inverse_right z v)
  change action (vacuum+(z.val.2.1:Scalar)) u.1+(u.2.1:Scalar)=v.1 at hs
  have hg:=congrArg Prod.snd (inverse_right z v)
  change nativeGauge u.1 (z.val.2.2:SourceQuantumConfigurationHilbert.Gauge)+
    (u.2.2:SourceQuantumConfigurationHilbert.Gauge)=v.2 at hg
  have hcancel:Real.exp (-t)*Real.exp t=1:=by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hsq:Real.exp t*Real.exp t=Real.exp (2*t):=by rw [←Real.exp_add];congr 1;ring
  have hp:splitMap z'.val u'=v:=by
    apply Prod.ext
    · change action (vacuum+((combinedMap t z.val).2.1:Scalar)) (Real.exp t • u.1)+
        Real.exp (2*t) • (u.2.1:Scalar)=v.1
      rw [map_scalar_field,action_scale,hsq,←smul_add,hs,hv,smul_zero]
    · change nativeGauge (Real.exp t • u.1) (Real.exp (-t) • (z.val.2.2:SourceQuantumConfigurationHilbert.Gauge))+
        (u.2.2:SourceQuantumConfigurationHilbert.Gauge)=v.2
      rw [gauge_scale,hcancel,one_smul]
      exact hg
  exact (congrArg (inverseL z'.val) hp).symm.trans (inverse_left z' u')

private theorem parameter_native_line(r s t:ℝ)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    parameter r s (z+t • (0,v))=parameter r s z:=by
  have hp:(z+t • (0,v)).1=z.1:=by
    change z.1+t • (0:Coframe)=z.1
    simp only [smul_zero,add_zero]
  simp only [parameter,inverseRootVolume,reciprocalVolume,GaussNativeEnergy.volume,hp]
private def scaledNative(c:ℝ)(v:GaussLiveMomentum.Slice):SourceCoordinateSlice:=
  (0,Real.exp c • v.1,Real.exp (-c) • v.2)
private theorem localMap_native_line(r s t:ℝ)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    localMap r s (z+t • (0,v))=localMap r s z+t • scaledNative (parameter r s z) v:=by
  unfold localMap
  rw [parameter_native_line]
  simp only [combinedMap_apply,scaledNative]
  apply Prod.ext
  · simp
  apply Prod.ext
  · change Real.exp (parameter r s z) • ((z.2.1+t • v.1)+vacuumSlice)-vacuumSlice=
      (Real.exp (parameter r s z) • (z.2.1+vacuumSlice)-vacuumSlice)+t • (Real.exp (parameter r s z) • v.1)
    module
  · change Real.exp (-(parameter r s z)) • (z.2.2+t • v.2)=
      Real.exp (-(parameter r s z)) • z.2.2+t • (Real.exp (-(parameter r s z)) • v.2)
    module
private theorem noise_native_line(r s t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    noiseCore r s f (z+t • (0,v))=
      (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
        f (localMap r s z+t • scaledNative (parameter r s z) v):=by
  change noiseValue r s f (z+t • (0,v))=_
  simp only [noiseValue,parameter_native_line,localMap_native_line]
private theorem noise_native_fderiv(r s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    fderiv ℝ (noiseCore r s f) z (0,v)=
      (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
        fderiv ℝ f (localMap r s z) (scaledNative (parameter r s z) v):=by
  have hz:HasDerivAt (fun t:ℝ=>z+t • (0,v)) (0,v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,v)).const_add z
  have hx:HasDerivAt (fun t:ℝ=>localMap r s z+t • scaledNative (parameter r s z) v)
      (scaledNative (parameter r s z) v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (scaledNative (parameter r s z) v)).const_add (localMap r s z)
  have hleft:=(((noiseCore r s f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    (0:ℝ) hz (by simp)
  have hright:=(((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=localMap r s z)).comp_hasDerivAt_of_eq
    (0:ℝ) hx (by simp)).const_smul (Real.exp ((25/2:ℝ)*parameter r s z):ℂ)
  have he:(fun t:ℝ=>noiseCore r s f (z+t • (0,v)))=
      (fun t:ℝ=>(Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
        f (localMap r s z+t • scaledNative (parameter r s z) v)):=funext (noise_native_line r s · f z v)
  dsimp only [Function.comp_def] at hleft hright
  rw [he] at hleft
  exact hleft.unique hright

private theorem scaled_scalar_direction(r s:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    scaledNative (parameter r s z.val) (inverseL z.val v).2=
      Real.exp (parameter r s z.val) • direction v (localMap r s z.val):=by
  let c:=parameter r s z.val
  have he:Real.exp c*Real.exp (-2*c)=Real.exp (-c):=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp c • (inverseL z.val v).2.1,Real.exp (-c) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp c • (0,(inverseL (combinedMap c z.val) v).2)
  rw [inverse_scalar_finite c z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem scalar_native_inverse(r s:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    (inverseL z.val v).1=Real.exp (parameter r s z.val) • (inverseL (localMap r s z.val) v).1:=by
  let c:=parameter r s z.val
  change _=Real.exp c • (inverseL (combinedMap c z.val) v).1
  rw [inverse_scalar_finite c z v hv]
  simp only [smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
private theorem scaled_gauge_direction(r s:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    scaledNative (parameter r s z.val) (inverseL z.val v).2=
      Real.exp (-(parameter r s z.val)) • direction v (localMap r s z.val):=by
  let c:=parameter r s z.val
  have he:Real.exp (-c)*Real.exp (2*c)=Real.exp c:=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp c • (inverseL z.val v).2.1,Real.exp (-c) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp (-c) • (0,(inverseL (combinedMap c z.val) v).2)
  rw [inverse_gauge_finite c z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem gauge_native_inverse(r s:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    (inverseL z.val v).1=Real.exp (-(parameter r s z.val)) • (inverseL (localMap r s z.val) v).1:=by
  let c:=parameter r s z.val
  change _=Real.exp (-c) • (inverseL (combinedMap c z.val) v).1
  rw [inverse_gauge_finite c z v hv]
  simp only [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]
private theorem native_intertwine_at(r s k:ℝ)(z:physicalChart)(v:Ambient)
    (hd:scaledNative (parameter r s z.val) (inverseL z.val v).2=k • direction v (localMap r s z.val))
    (hb:(inverseL z.val v).1=k • (inverseL (localMap r s z.val) v).1)(f:QuantumTest):
    covariantMomentum v (noiseCore r s f) z.val=(k:ℂ) • (noiseCore r s (covariantMomentum v f) z.val):=by
  rw [covariantMomentum_apply,noise_native_fderiv,hd,map_smul,hb]
  change (-Complex.I) • ((Real.exp ((25/2:ℝ)*parameter r s z.val):ℂ) •
    (k • fderiv ℝ f (localMap r s z.val) (direction v (localMap r s z.val)))+
    GaussNativeMatter.nativeFock (k • (inverseL (localMap r s z.val) v).1)
      ((Real.exp ((25/2:ℝ)*parameter r s z.val):ℂ) • f (localMap r s z.val)))=
    (k:ℂ) • ((Real.exp ((25/2:ℝ)*parameter r s z.val):ℂ) •
      ((-Complex.I) • (fderiv ℝ f (localMap r s z.val) (direction v (localMap r s z.val))+
       GaussNativeMatter.nativeFock (inverseL (localMap r s z.val) v).1 (f (localMap r s z.val)))))
  simp only [map_smul,smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  module
def noiseWeight(r s k:ℝ):End:=multiply (fun z=>Real.exp (k*parameter r s z))
  (fun z=>(contDiffAt_const.mul (parameter_smooth r s z)).exp)
private theorem scalar_native_intertwine(r s:ℝ)(v:Ambient)(hv:v.2=0):
    covariantMomentum v*noiseCore r s=noiseWeight r s 1*noiseCore r s*covariantMomentum v:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · simpa only [Module.End.mul_apply,noiseWeight,multiply_apply,one_mul] using
      native_intertwine_at r s (Real.exp (parameter r s z)) ⟨z,hz⟩ v
        (scaled_scalar_direction r s ⟨z,hz⟩ v hv) (scalar_native_inverse r s ⟨z,hz⟩ v hv) f
  · exact (image_eq_zero_of_notMem_tsupport (fun h=>hz ((covariantMomentum v (noiseCore r s f)).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h=>hz ((noiseWeight r s 1 (noiseCore r s (covariantMomentum v f))).tsupport_subset h))).symm
private theorem gauge_native_intertwine(r s:ℝ)(v:Ambient)(hv:v.1=0):
    covariantMomentum v*noiseCore r s=noiseWeight r s (-1)*noiseCore r s*covariantMomentum v:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · simpa only [Module.End.mul_apply,noiseWeight,multiply_apply,neg_one_mul] using
      native_intertwine_at r s (Real.exp (-(parameter r s z))) ⟨z,hz⟩ v
        (scaled_gauge_direction r s ⟨z,hz⟩ v hv) (gauge_native_inverse r s ⟨z,hz⟩ v hv) f
  · exact (image_eq_zero_of_notMem_tsupport (fun h=>hz ((covariantMomentum v (noiseCore r s f)).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h=>hz ((noiseWeight r s (-1) (noiseCore r s (covariantMomentum v f))).tsupport_subset h))).symm

private theorem noiseWeight_native_derivative(r s k:ℝ)(z:physicalChart)(v:Ambient):
    fderiv ℝ (fun x:SourceCoordinateSlice=>Real.exp (k*parameter r s x)) z.val (direction v z.val)=0:=by
  have ht:HasDerivAt (fun t:ℝ=>z.val+t • direction v z.val) (direction v z.val) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (direction v z.val)).const_add z.val
  have hs:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>Real.exp (k*parameter r s x)) z.val:=
    (contDiffAt_const.mul (parameter_smooth r s z)).exp
  have hc:=(hs.differentiableAt (by simp)).hasFDerivAt
  have hd:=hc.comp_hasDerivAt_of_eq (0:ℝ) ht (by simp)
  have he:(fun t:ℝ=>Real.exp (k*parameter r s (z.val+t • direction v z.val)))=
      (fun _:ℝ=>Real.exp (k*parameter r s z.val)):=by
    funext t
    rw [show direction v z.val=(0,(inverseL z.val v).2) from rfl,parameter_native_line]
  change HasDerivAt (fun t:ℝ=>Real.exp (k*parameter r s (z.val+t • direction v z.val))) _ 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const _ _)
private theorem noiseWeight_native(r s k:ℝ)(v:Ambient):
    Commute (covariantMomentum v) (noiseWeight r s k):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · let c:SourceCoordinateSlice→ℝ:=fun x=>Real.exp (k*parameter r s x)
    have hs:ContDiffAt ℝ ∞ c z:=(contDiffAt_const.mul (parameter_smooth r s ⟨z,hz⟩)).exp
    have he:(noiseWeight r s k f : SourceCoordinateSlice→FockFiber)=(fun x=>c x • f x):=by
      funext x
      exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (c x) (f x)).symm
    have hd:directional v (noiseWeight r s k f) z=c z • directional v f z:=by
      rw [directional_apply,he,fderiv_fun_smul (hs.differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
      change c z • fderiv ℝ f z (direction v z)+fderiv ℝ c z (direction v z) • f z=_
      rw [noiseWeight_native_derivative r s k ⟨z,hz⟩ v,zero_smul,add_zero]
      rfl
    change (-Complex.I) • (directional v (noiseWeight r s k f) z+
      connection v z ((c z:ℂ) • f z))=
      (c z:ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))
    rw [hd,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    module
  · exact (image_eq_zero_of_notMem_tsupport (fun h=>hz ((covariantMomentum v (noiseWeight r s k f)).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h=>hz ((noiseWeight r s k (covariantMomentum v f)).tsupport_subset h))).symm
theorem noiseWeight_pair(r s k:ℝ)(f g:QuantumTest):
    sourcePair f (noiseWeight r s k g)=sourcePair (noiseWeight r s k f) g:=multiply_pair _ _ f g
theorem noiseWeight_flow(r s k r' s':ℝ):Commute (noiseCore r' s') (noiseWeight r s k):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp ((25/2:ℝ)*parameter r' s' z):ℂ) •
      ((Real.exp (k*parameter r s (localMap r' s' z)):ℂ) • f (localMap r' s' z))=
    (Real.exp (k*parameter r s z):ℂ) •
      ((Real.exp ((25/2:ℝ)*parameter r' s' z):ℂ) • f (localMap r' s' z))
  have hi:parameter r s (localMap r' s' z)=parameter r s z:=parameter_invariant _ _ _ _
  rw [hi];exact smul_comm _ _ _
theorem noise_pair_right(r s:ℝ)(f g:QuantumTest):
    sourcePair f (noiseCore r s g)=sourcePair (noiseCore (-r) (-s) f) g:=by
  have h:=noiseCore_pair r s (noiseCore (-r) (-s) f) g
  rw [noiseCore_add,add_neg_cancel,add_neg_cancel,noiseCore_zero] at h
  exact h
theorem noise_pair_left(r s:ℝ)(f g:QuantumTest):
    sourcePair (noiseCore r s f) g=sourcePair f (noiseCore (-r) (-s) g):=by
  have h:=noiseCore_pair r s f (noiseCore (-r) (-s) g)
  rw [noiseCore_add,add_neg_cancel,add_neg_cancel,noiseCore_zero] at h
  exact h
theorem noise_inverse_end(r s:ℝ):noiseCore (-r) (-s)*noiseCore r s=(1:End):=by
  apply LinearMap.ext;intro f;exact noiseCore_inverse r s f
private theorem native_adjoint_intertwine(r s k:ℝ)(v:Ambient)
    (hp:covariantMomentum v*noiseCore r s=noiseWeight r s k*noiseCore r s*covariantMomentum v):
    GaussMomentumAdjoint.adjoint v*noiseCore r s=
      noiseWeight r s k*noiseCore r s*GaussMomentumAdjoint.adjoint v:=by
  let N:=noiseCore r s
  let Ni:=noiseCore (-r) (-s)
  let M:=noiseWeight r s k
  let P:=covariantMomentum v
  have hN:Ni*N=1:=noise_inverse_end r s
  have hNi:N*Ni=1:=by simpa only [neg_neg] using noise_inverse_end (-r) (-s)
  have hm:Ni*M=M*Ni:=(noiseWeight_flow r s k (-r) (-s)).eq
  have hM:N*M=M*N:=(noiseWeight_flow r s k r s).eq
  have hP:P*M=M*P:=(noiseWeight_native r s k v).eq
  have hn:Ni*P=M*P*Ni:=by
    calc
      Ni*P=Ni*P*(N*Ni):=by rw [hNi,mul_one]
      _=Ni*(P*N)*Ni:=by noncomm_ring
      _=Ni*(M*N*P)*Ni:=by rw [hp]
      _=M*(Ni*N)*P*Ni:=by simp only [←mul_assoc,hm]
      _=M*P*Ni:=by rw [hN,mul_one]
  apply LinearMap.ext;intro g;apply SourceCoframeVolume.pair_ext;intro f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (N g))=
    sourcePair f (M (N (GaussMomentumAdjoint.adjoint v g)))
  calc
    _=sourcePair (P f) (N g):=adjoint_pair _ _ _
    _=sourcePair (Ni (P f)) g:=noise_pair_right _ _ _ _
    _=sourcePair (M (P (Ni f))) g:=congrArg (fun q=>sourcePair q g) (LinearMap.congr_fun hn f)
    _=sourcePair (P (M (Ni f))) g:=congrArg (fun q=>sourcePair q g) (LinearMap.congr_fun hP (Ni f)).symm
    _=sourcePair (M (Ni f)) (GaussMomentumAdjoint.adjoint v g):=(adjoint_pair _ _ _).symm
    _=sourcePair (Ni f) (M (GaussMomentumAdjoint.adjoint v g)):=(noiseWeight_pair _ _ _ _ _).symm
    _=sourcePair f (N (M (GaussMomentumAdjoint.adjoint v g))):=(noise_pair_right _ _ _ _).symm
    _=sourcePair f (M (N (GaussMomentumAdjoint.adjoint v g))):=
      congrArg (sourcePair f) (LinearMap.congr_fun hM (GaussMomentumAdjoint.adjoint v g))
private theorem scalar_adjoint_intertwine(r s:ℝ)(v:Ambient)(hv:v.2=0):
    GaussMomentumAdjoint.adjoint v*noiseCore r s=
      noiseWeight r s 1*noiseCore r s*GaussMomentumAdjoint.adjoint v:=
  native_adjoint_intertwine r s 1 v (scalar_native_intertwine r s v hv)
private theorem gauge_adjoint_intertwine(r s:ℝ)(v:Ambient)(hv:v.1=0):
    GaussMomentumAdjoint.adjoint v*noiseCore r s=
      noiseWeight r s (-1)*noiseCore r s*GaussMomentumAdjoint.adjoint v:=
  native_adjoint_intertwine r s (-1) v (gauge_native_intertwine r s v hv)

private theorem noiseWeight_adjoint(r s k:ℝ)(v:Ambient):
    Commute (GaussMomentumAdjoint.adjoint v) (noiseWeight r s k):=by
  apply LinearMap.ext;intro g;apply SourceCoframeVolume.pair_ext;intro f
  have hc:=LinearMap.congr_fun (noiseWeight_native r s k v).eq f
  change covariantMomentum v (noiseWeight r s k f)=noiseWeight r s k (covariantMomentum v f) at hc
  change sourcePair f (GaussMomentumAdjoint.adjoint v (noiseWeight r s k g))=
    sourcePair f (noiseWeight r s k (GaussMomentumAdjoint.adjoint v g))
  rw [adjoint_pair,noiseWeight_pair,←hc,←adjoint_pair,←noiseWeight_pair]
private theorem noiseWeight_mul(r s k l:ℝ):noiseWeight r s k*noiseWeight r s l=noiseWeight r s (k+l):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp (k*parameter r s z):ℂ) • ((Real.exp (l*parameter r s z):ℂ) • f z)=
    (Real.exp ((k+l)*parameter r s z):ℂ) • f z
  rw [smul_smul,←Complex.ofReal_mul,←Real.exp_add,←add_mul]
theorem noise_real_multiplier(r s:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)(hci:∀ z, c (localMap r s z)=c z):
    Commute (noiseCore r s) (multiply c hc):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • ((c (localMap r s z):ℂ) • f (localMap r s z))=
    (c z:ℂ) • ((Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z))
  rw [hci];exact smul_comm _ _ _
theorem noiseWeight_multiplier(r s k:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val):
    Commute (noiseWeight r s k) (multiply c hc):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (Real.exp (k*parameter r s z):ℂ) (c z:ℂ) (f z)
private theorem noise_sandwich(r s k:ℝ)(v w:Ambient)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)(hci:∀ z, c (localMap r s z)=c z)
    (hv:GaussMomentumAdjoint.adjoint v*noiseCore r s=noiseWeight r s k*noiseCore r s*GaussMomentumAdjoint.adjoint v)
    (hw:covariantMomentum w*noiseCore r s=noiseWeight r s k*noiseCore r s*covariantMomentum w):
    sandwich v w c hc*noiseCore r s=noiseWeight r s (k+k)*noiseCore r s*sandwich v w c hc:=by
  let P:=GaussMomentumAdjoint.adjoint v
  let W:=multiply c hc
  let Q:=covariantMomentum w
  let N:=noiseCore r s
  let M:=noiseWeight r s k
  have hPM:P*M=M*P:=(noiseWeight_adjoint r s k v).eq
  have hWM:W*M=M*W:=(noiseWeight_multiplier r s k c hc).symm.eq
  have hWN:W*N=N*W:=(noise_real_multiplier r s c hc hci).symm.eq
  have hMM:M*M=noiseWeight r s (k+k):=noiseWeight_mul r s k k
  change (P*W*Q)*N=noiseWeight r s (k+k)*N*(P*W*Q)
  calc
    (P*W*Q)*N=P*W*(Q*N):=by noncomm_ring
    _=P*W*(M*N*Q):=by rw [hw]
    _=P*(W*M)*N*Q:=by noncomm_ring
    _=(M*P)*(W*N)*Q:=by rw [hWM];simp only [←mul_assoc,hPM]
    _=M*(P*N)*W*Q:=by rw [hWN];noncomm_ring
    _=(M*M)*N*(P*W*Q):=by rw [hv];noncomm_ring
    _=noiseWeight r s (k+k)*N*(P*W*Q):=by rw [hMM]
private theorem scalar_kinetic_intertwine(r s:ℝ):
    scalarKinetic*noiseCore r s=noiseWeight r s 2*noiseCore r s*scalarKinetic:=by
  have h(i:ScalarIndex):sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth*noiseCore r s=
      noiseWeight r s 2*noiseCore r s*sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth:=by
    simpa only [one_add_one_eq_two] using noise_sandwich r s 1 (scalarDirection i) (scalarDirection i)
      scalarWeight scalarWeight_smooth (fun _=>rfl)
      (scalar_adjoint_intertwine r s _ rfl) (scalar_native_intertwine r s _ rfl)
  simp only [scalarKinetic,smul_mul_assoc,Finset.sum_mul,h,mul_smul_comm,Finset.mul_sum,Finset.smul_sum]
private theorem gauge_kinetic_intertwine(r s:ℝ):
    gaugeKinetic*noiseCore r s=noiseWeight r s (-2)*noiseCore r s*gaugeKinetic:=by
  have h(a:LieIndex)(i j:Fin 3):sandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)*noiseCore r s=
      noiseWeight r s (-2)*noiseCore r s*sandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j):=by
    simpa only [show (-1:ℝ)+(-1)=-2 by norm_num] using
      noise_sandwich r s (-1) (gaugeDirection i a) (gaugeDirection j a)
        (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j) (fun _=>rfl)
        (gauge_adjoint_intertwine r s _ rfl) (gauge_native_intertwine r s _ rfl)
  simp only [gaugeKinetic,smul_mul_assoc,Finset.sum_mul,h,mul_smul_comm,Finset.mul_sum,Finset.smul_sum]
private theorem noise_conjugate_of_intertwine(r s k:ℝ)(T:End)
    (h:T*noiseCore r s=noiseWeight r s k*noiseCore r s*T):
    noiseCore (-r) (-s)*T*noiseCore r s=noiseWeight r s k*T:=by
  have hm:noiseCore (-r) (-s)*noiseWeight r s k=noiseWeight r s k*noiseCore (-r) (-s):=
    (noiseWeight_flow r s k (-r) (-s)).eq
  calc
    _=noiseCore (-r) (-s)*(T*noiseCore r s):=by noncomm_ring
    _=noiseCore (-r) (-s)*(noiseWeight r s k*noiseCore r s*T):=by rw [h]
    _=noiseWeight r s k*(noiseCore (-r) (-s)*noiseCore r s)*T:=by simp only [←mul_assoc,hm]
    _=noiseWeight r s k*T:=by rw [noise_inverse_end,mul_one]
theorem scalar_kinetic_finite(r s:ℝ):
    noiseCore (-r) (-s)*scalarKinetic*noiseCore r s=noiseWeight r s 2*scalarKinetic:=
  noise_conjugate_of_intertwine r s 2 scalarKinetic (scalar_kinetic_intertwine r s)
theorem gauge_kinetic_finite(r s:ℝ):
    noiseCore (-r) (-s)*gaugeKinetic*noiseCore r s=noiseWeight r s (-2)*gaugeKinetic:=
  noise_conjugate_of_intertwine r s (-2) gaugeKinetic (gauge_kinetic_intertwine r s)

end LowEnergy.ClockPhiMatchedNoiseCore
