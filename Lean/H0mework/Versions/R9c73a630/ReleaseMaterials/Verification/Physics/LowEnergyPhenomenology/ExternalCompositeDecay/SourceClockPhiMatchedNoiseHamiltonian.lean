import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiMatchedNoiseHamiltonian
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge GaussLiveMomentum
open SourceGaugeRadialCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare
open SourceScalarInverseBulk SourceCoframeVolume ClockPhiMatchedNoiseCore Set Function
open scoped ContDiff Topology Distributions InnerProductSpace
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev D:End:=SourceClockPhiCombinedScalePressure.combinedGenerator

def parameterGradient(r s:ℝ)(i:Fin 6)(z:SourceCoordinateSlice):ℝ:=
  (-(r/2)*inverseRootVolume z*reciprocalVolume z-s*reciprocalVolume z^2)*SourceCoframeVolume.volumeGradient z i
private theorem parameterGradient_smooth(r s:ℝ)(i:Fin 6)(z:physicalChart):
    ContDiffAt ℝ ∞ (parameterGradient r s i) z.val:=by
  apply ContDiffAt.mul
  · exact ((contDiffAt_const.mul (inverse_root_volume_smooth z)).mul (reciprocal_volume_smooth z)).sub
      (contDiffAt_const.mul ((reciprocal_volume_smooth z).pow 2))
  · fin_cases i <;> dsimp [SourceCoframeVolume.volumeGradient] <;> fun_prop
def parameterGradientAction(r s:ℝ)(i:Fin 6):End:=
  multiply (parameterGradient r s i) (parameterGradient_smooth r s i)
private theorem parameter_coordinate_derivative(r s:ℝ)(z:physicalChart)(i:Fin 6):
    fderiv ℝ (parameter r s) z.val (GaussCoframeCore.coframeDirection i)=parameterGradient r s i z.val:=by
  have hv := (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z.val)
  have hroot := (hasDerivAt_inv (Real.sqrt_pos.mpr (volume_pos z)).ne').comp_hasFDerivAt z.val
    (hv.sqrt (volume_pos z).ne')
  have hu := (hasDerivAt_inv (volume_pos z).ne').comp_hasFDerivAt z.val hv
  have hr:HasFDerivAt inverseRootVolume _ z.val:=hroot
  have hi:HasFDerivAt reciprocalVolume _ z.val:=hu
  have hd := (hr.const_mul r).add (hi.const_mul s)
  change HasFDerivAt (parameter r s) _ z.val at hd
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,SourceCoframeVolume.volume_coordinate_derivative]
  unfold parameterGradient inverseRootVolume reciprocalVolume
  have hpos:Real.sqrt (GaussNativeEnergy.volume z.val)≠0:=(Real.sqrt_pos.mpr (volume_pos z)).ne'
  have hsquare:Real.sqrt (GaussNativeEnergy.volume z.val)^2=GaussNativeEnergy.volume z.val:=Real.sq_sqrt (volume_pos z).le
  rw [←hsquare]
  simp only [Real.sqrt_sq_eq_abs,abs_of_pos (Real.sqrt_pos.mpr (volume_pos z))]
  field_simp [hpos]
  ring
private theorem parameterGradient_invariant(r s r' s':ℝ)(i:Fin 6)(z:SourceCoordinateSlice):
    parameterGradient r s i (localMap r' s' z)=parameterGradient r s i z:=rfl
private theorem parameter_coframe_jet(r s:ℝ)(z:physicalChart)(i:Fin 6):
    HasDerivAt (fun t:ℝ=>parameter r s (z.val+t • GaussCoframeCore.coframeDirection i))
      (parameterGradient r s i z.val) 0:=by
  have ht:HasDerivAt (fun t:ℝ=>z.val+t • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i)).const_add z.val
  have h:=((parameter_smooth r s z).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℝ) ht (by simp)
  simpa only [Function.comp_def,parameter_coordinate_derivative] using h

private theorem localMap_coframe_jet(r s:ℝ)(z:physicalChart)(i:Fin 6):
    HasDerivAt (fun t:ℝ=>localMap r s (z.val+t • GaussCoframeCore.coframeDirection i))
      (GaussCoframeCore.coframeDirection i+parameterGradient r s i z.val •
        (phiEuler (localMap r s z.val)-gaugeEuler (localMap r s z.val))) 0:=by
  let c:=parameter r s z.val
  let dc:=parameterGradient r s i z.val
  have hc:=parameter_coframe_jet r s z i
  have he:=hc.exp
  have hn:=hc.neg.exp
  have hco:HasDerivAt (fun t:ℝ=>z.val.1+t • (GaussCoframeCore.coframeDirection i).1)
      (GaussCoframeCore.coframeDirection i).1 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i).1).const_add z.val.1
  have h:=hco.prodMk (((he.smul_const (z.val.2.1+vacuumSlice)).sub_const vacuumSlice).prodMk
    (hn.smul_const z.val.2.2))
  have hp:parameter r s (z.val+(0:ℝ) • GaussCoframeCore.coframeDirection i)=c:=by simp [c]
  simp only [Pi.neg_apply,hp] at h
  have hd:((GaussCoframeCore.coframeDirection i).1,
      (Real.exp c*dc) • (z.val.2.1+vacuumSlice),(Real.exp (-c)*(-dc)) • z.val.2.2)=
      GaussCoframeCore.coframeDirection i+dc •
        (phiEuler (localMap r s z.val)-gaugeEuler (localMap r s z.val)):=by
    simp only [localMap,combinedMap_apply,phiEuler,gaugeEuler,GaussCoframeCore.coframeDirection]
    apply Prod.ext
    · simp
    apply Prod.ext
    · change (Real.exp c*dc) • (z.val.2.1+vacuumSlice)=
        0+dc • (vacuumSlice+(Real.exp c • (z.val.2.1+vacuumSlice)-vacuumSlice)-0)
      module
    · change (Real.exp (-c)*(-dc)) • z.val.2.2=0+dc • (0-Real.exp (-c) • z.val.2.2)
      module
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun t=>by
    simp only [localMap,combinedMap_apply,GaussCoframeCore.coframeDirection,
      Prod.fst_add,Prod.snd_add,Prod.smul_mk,smul_zero,add_zero])
private theorem component_fderiv(f:QuantumTest)(z v:SourceCoordinateSlice)(word:Occupation):
    fderiv ℝ f z v word=fderiv ℝ (component word f) z v:=by
  have h:=congrArg (fun g:GaussDensityCore.ScalarTest=>g z) (GaussCoframeCore.component_derivative v f word)
  change GaussCoframeCore.derivative v f z word=GaussDensityCore.derivative v (component word f) z at h
  simpa only [GaussCoframeCore.derivative_apply,GaussDensityCore.derivative_apply] using h
private theorem combined_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    D f z word=fderiv ℝ (component word f) z (phiEuler z-gaugeEuler z)+(25/2:ℂ)*f z word:=by
  have h:=congrArg (fun v:FockFiber=>v word) (combined_generator_point f z)
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,component_fderiv] using h
private theorem coframe_noise_derivative(r s:ℝ)(f:QuantumTest)(z:physicalChart)(i:Fin 6):
    GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (noiseCore r s f) z.val=
      noiseCore r s (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f+
        parameterGradientAction r s i (D f)) z.val:=by
  apply PiLp.ext;intro word
  have hc:=parameter_coframe_jet r s z i
  have hx:=localMap_coframe_jet r s z i
  have hz:HasDerivAt (fun t:ℝ=>z.val+t • GaussCoframeCore.coframeDirection i)
      (GaussCoframeCore.coframeDirection i) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (GaussCoframeCore.coframeDirection i)).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=localMap r s z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (noiseCore r s f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hz (by simp)
  have he0:= (hc.const_mul (25/2:ℝ)).exp
  have he:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) he0
  have hh:=he.mul hf
  have heq:(fun t:ℝ=>(Real.exp ((25/2:ℝ)*parameter r s (z.val+t • GaussCoframeCore.coframeDirection i)):ℂ)*
      f (localMap r s (z.val+t • GaussCoframeCore.coframeDirection i)) word)=
      (fun t:ℝ=>noiseCore r s f (z.val+t • GaussCoframeCore.coframeDirection i) word):=by
    funext t;rfl
  have hcomp(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  dsimp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at hh hl
  simp only [hcomp] at hh hl
  change HasDerivAt (fun t:ℝ=>(Real.exp ((25/2:ℝ)*parameter r s (z.val+t • GaussCoframeCore.coframeDirection i)):ℂ)*
    f (localMap r s (z.val+t • GaussCoframeCore.coframeDirection i)) word) _ 0 at hh
  rw [heq] at hh
  have h:=hl.unique hh
  rw [GaussCoframeCore.derivative_apply,component_fderiv]
  change fderiv ℝ (component word (noiseCore r s f)) z.val (GaussCoframeCore.coframeDirection i)=_
  rw [h]
  change _=(Real.exp ((25/2:ℝ)*parameter r s z.val):ℂ)*
    (GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f (localMap r s z.val) word+
      (parameterGradient r s i (localMap r s z.val):ℂ)*D f (localMap r s z.val) word)
  rw [parameterGradient_invariant,GaussCoframeCore.derivative_apply,component_fderiv,combined_component]
  simp only [zero_smul,add_zero,map_add,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring_nf
  abel

private theorem flow_pair_generator(flow:ℝ→End)(G:End)
    (hzero:∀ f,flow 0 f=f)(hpair:∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀ f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest):sourcePair f (G g)= -sourcePair (G f) g:=by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=fun _=>inner ℂ (embed f) (embed g):=
    funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq
private theorem D_pair(f g:QuantumTest):sourcePair f (D g)= -sourcePair (D f) g:=by
  have hp:=flow_pair_generator SourceScalarAffineScaleTransport.coreFlow SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
  have hg:=flow_pair_generator SourceGaugeScaleTransport.coreFlow SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
  change sourcePair f (SourceScalarAffineScaleTransport.generator g-SourceGaugeScaleTransport.generator g)=
    -sourcePair (SourceScalarAffineScaleTransport.generator f-SourceGaugeScaleTransport.generator f) g
  simp only [sourcePair,map_sub,inner_sub_left,inner_sub_right] at hp hg ⊢
  linear_combination hp-hg
private theorem coframe_function_D(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀ x y : SourceCoordinateSlice,x.1=y.1→c x=c y):
    Commute D (multiply c hc):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · let e:=phiEuler z-gaugeEuler z
    have ht:HasDerivAt (fun t:ℝ=>z+t • e) e 0:=by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const e).const_add z
    have hd:=((hc ⟨z,hz⟩).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) ht (by simp)
    have he:(fun t:ℝ=>c (z+t • e))=(fun _:ℝ=>c z):=by
      funext t;apply hfirst
      change z.1+t • ((0:Coframe)-0)=z.1
      simp
    dsimp only [Function.comp_def] at hd
    rw [he] at hd
    have hdc:fderiv ℝ c z e=0:=hd.unique (hasDerivAt_const _ _)
    have hm:(multiply c hc f:SourceCoordinateSlice→FockFiber)=(fun x=>c x • f x):=by
      funext x;exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) (c x) (f x)).symm
    change D (multiply c hc f) z=multiply c hc (D f) z
    rw [combined_generator_point (multiply c hc f) z]
    change fderiv ℝ (multiply c hc f) z (phiEuler z-gaugeEuler z)+(25/2:ℂ) • ((c z:ℂ) • f z)=
      (c z:ℂ) • D f z
    rw [combined_generator_point f z,hm,
      fderiv_fun_smul ((hc ⟨z,hz⟩).differentiableAt (by simp))
        (f.contDiff.differentiable (by simp)).differentiableAt]
    change c z • fderiv ℝ f z e+fderiv ℝ c z e • f z+(25/2:ℂ) • (c z • f z)=_
    rw [hdc,zero_smul,add_zero]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
    module
  · exact (image_eq_zero_of_notMem_tsupport (fun h=>hz ((D (multiply c hc f)).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h=>hz ((multiply c hc (D f)).tsupport_subset h))).symm
private theorem gradient_D(r s:ℝ)(i:Fin 6):Commute D (parameterGradientAction r s i):=by
  apply coframe_function_D
  intro x y h
  simp only [parameterGradient,inverseRootVolume,reciprocalVolume,GaussNativeEnergy.volume,
    SourceCoframeVolume.volumeGradient,h]
def coframeCorrection(r s:ℝ)(i:Fin 6):End:=(-Complex.I) • (parameterGradientAction r s i*D)
private theorem coframeCorrection_pair(r s:ℝ)(i:Fin 6):GaussCoframeForm.Paired (coframeCorrection r s i) (coframeCorrection r s i):=by
  intro f g
  have hc:=LinearMap.congr_fun (gradient_D r s i).eq f
  change D (parameterGradientAction r s i f)=parameterGradientAction r s i (D f) at hc
  change sourcePair f ((-Complex.I) • (parameterGradientAction r s i (D g)))=
    sourcePair ((-Complex.I) • (parameterGradientAction r s i (D f))) g
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,map_neg,Complex.conj_I,neg_neg]
  change (-Complex.I)*sourcePair f (parameterGradientAction r s i (D g))=
    Complex.I*sourcePair (parameterGradientAction r s i (D f)) g
  rw [show sourcePair f (parameterGradientAction r s i (D g))=sourcePair (parameterGradientAction r s i f) (D g)
    from multiply_pair _ _ _ _,D_pair,hc]
  ring
private theorem coframe_momentum_intertwine(r s:ℝ)(i:Fin 6):
    GaussCoframeCore.momentum i*noiseCore r s=noiseCore r s*(GaussCoframeCore.momentum i+coframeCorrection r s i):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · have h:=coframe_noise_derivative r s f ⟨z,hz⟩ i
    change (-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) (noiseCore r s f) z=
      noiseCore r s ((-Complex.I) • GaussCoframeCore.derivative (GaussCoframeCore.coframeDirection i) f+
        (-Complex.I) • parameterGradientAction r s i (D f)) z
    rw [h,←smul_add,map_smul]
    rfl
  · exact (image_eq_zero_of_notMem_tsupport (fun h=>hz ((GaussCoframeCore.momentum i (noiseCore r s f)).tsupport_subset h))).trans
      (image_eq_zero_of_notMem_tsupport (fun h=>hz ((noiseCore r s ((GaussCoframeCore.momentum i+coframeCorrection r s i) f)).tsupport_subset h))).symm

private def noiseConjugation(r s:ℝ):End →ₐ[ℂ] End where
  toFun T:=noiseCore (-r) (-s)*T*noiseCore r s
  map_zero':=by simp
  map_add' T R:=by simp only [mul_add,add_mul]
  map_one':=by simpa using noise_inverse_end r s
  map_mul' T R:=by
    have hi:noiseCore r s*noiseCore (-r) (-s)=1:=by simpa only [neg_neg] using noise_inverse_end (-r) (-s)
    change noiseCore (-r) (-s)*(T*R)*noiseCore r s=
      (noiseCore (-r) (-s)*T*noiseCore r s)*(noiseCore (-r) (-s)*R*noiseCore r s)
    calc
      _=noiseCore (-r) (-s)*T*(noiseCore r s*noiseCore (-r) (-s))*R*noiseCore r s:=by rw [hi];noncomm_ring
      _=_:=by noncomm_ring
  commutes' c:=by
    change noiseCore (-r) (-s)*(c • (1:End))*noiseCore r s=c • (1:End)
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,noise_inverse_end]
private theorem conjugation_add(r s:ℝ)(T R:End):noiseConjugation r s (T+R)=noiseConjugation r s T+noiseConjugation r s R:=by
  change noiseCore (-r) (-s)*(T+R)*noiseCore r s=_
  simp only [mul_add,add_mul];rfl
private theorem conjugation_smul(r s:ℝ)(c:ℂ)(T:End):noiseConjugation r s (c • T)=c • noiseConjugation r s T:=by
  change noiseCore (-r) (-s)*(c • T)*noiseCore r s=_
  rw [mul_smul_comm,smul_mul_assoc];rfl
private theorem conjugation_mul(r s:ℝ)(T R:End):noiseConjugation r s (T*R)=noiseConjugation r s T*noiseConjugation r s R:=
  (noiseConjugation r s).map_mul T R
private theorem conjugation_sum{ι:Type*}[Fintype ι](r s:ℝ)(T:ι→End):
    noiseConjugation r s (∑i,T i)=∑i,noiseConjugation r s (T i):=by
  change noiseCore (-r) (-s)*(∑i,T i)*noiseCore r s=_
  simp only [Finset.mul_sum,Finset.sum_mul];rfl
private theorem conjugation_apply(r s:ℝ)(T:End)(f:QuantumTest):
    noiseConjugation r s T f=noiseCore (-r) (-s) (T (noiseCore r s f)):=rfl
private theorem conjugation_pair(r s:ℝ)(T R:End)(hp:GaussCoframeForm.Paired T R):
    GaussCoframeForm.Paired (noiseConjugation r s T) (noiseConjugation r s R):=by
  intro f g
  rw [conjugation_apply,conjugation_apply,noise_pair_right,neg_neg,neg_neg,hp,noise_pair_left,neg_neg,neg_neg]
private theorem conjugation_fixed(r s:ℝ)(T:End)(hc:Commute T (noiseCore r s)):
    noiseConjugation r s T=T:=by
  change noiseCore (-r) (-s)*T*noiseCore r s=T
  calc
    _=noiseCore (-r) (-s)*(T*noiseCore r s):=by noncomm_ring
    _=(noiseCore (-r) (-s)*noiseCore r s)*T:=by rw [hc.eq];noncomm_ring
    _=T:=by rw [noise_inverse_end,one_mul]
private theorem conjugation_momentum(r s:ℝ)(i:Fin 6):
    noiseConjugation r s (GaussCoframeCore.momentum i)=GaussCoframeCore.momentum i+coframeCorrection r s i:=by
  have h:=congrArg (fun T:End=>noiseCore (-r) (-s)*T) (coframe_momentum_intertwine r s i)
  change noiseCore (-r) (-s)*GaussCoframeCore.momentum i*noiseCore r s=_
  simpa only [←mul_assoc,noise_inverse_end r s,one_mul] using h
private theorem conjugation_adjoint(r s:ℝ)(i:Fin 6):
    noiseConjugation r s (GaussCoframeCore.adjoint i)=GaussCoframeCore.adjoint i+coframeCorrection r s i:=by
  apply LinearMap.ext;intro g;apply SourceCoframeVolume.pair_ext;intro f
  have h:=conjugation_pair r s (GaussCoframeCore.adjoint i) (GaussCoframeCore.momentum i)
    (GaussCoframeKinetic.adjoint_pair i) f g
  rw [conjugation_momentum] at h
  change sourcePair f (noiseConjugation r s (GaussCoframeCore.adjoint i) g)=
    sourcePair f (GaussCoframeCore.adjoint i g+coframeCorrection r s i g)
  rw [h]
  have hp:=GaussCoframeKinetic.adjoint_pair i f g
  have hq:=coframeCorrection_pair r s i f g
  simpa only [LinearMap.add_apply,sourcePair,map_add,inner_add_left,inner_add_right] using congrArg₂ (·+·) hp.symm hq.symm
private theorem conjugation_real(r s:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)(hi:∀ z,c (localMap r s z)=c z):
    noiseConjugation r s (multiply c hc)=multiply c hc:=
  conjugation_fixed r s _ (noise_real_multiplier r s c hc hi).symm
private theorem constant_fiber_commute(r s:ℝ)(T:End)(B:FockFiber →L[ℂ] FockFiber)
    (hT:∀ f z,T f z=B (f z)):Commute T (noiseCore r s):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change T (noiseCore r s f) z=noiseCore r s (T f) z
  rw [hT]
  change B ((Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z))=
    (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • T f (localMap r s z)
  rw [map_smul,hT]
private theorem conjugation_spin(r s:ℝ)(j:Fin 7):
    noiseConjugation r s (GaussCoframeSpin.current j)=GaussCoframeSpin.current j:=
  conjugation_fixed r s _ (constant_fiber_commute r s _ (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full j)) (fun _ _=>rfl))
private theorem conjugation_number(r s:ℝ):
    noiseConjugation r s GaussCoframeForm.number=GaussCoframeForm.number:=by
  apply conjugation_fixed
  apply constant_fiber_commute r s _ fiberNumber
  intro f z;apply PiLp.ext;intro word
  rw [GaussCoframeForm.number_apply,fiberNumber_apply]
def finiteCoframeTerm(r s:ℝ)(i j:Fin 6):End:=
  (GaussCoframeCore.adjoint i+coframeCorrection r s i)*
    multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*
    (GaussCoframeCore.momentum j+coframeCorrection r s j)
private theorem conjugation_coframe_term(r s:ℝ)(i j:Fin 6):
    noiseConjugation r s (GaussCoframeKinetic.term i j)=finiteCoframeTerm r s i j:=by
  change noiseConjugation r s (GaussCoframeCore.adjoint i*
    multiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)*GaussCoframeCore.momentum j)=_
  rw [conjugation_mul r s,conjugation_mul r s,conjugation_adjoint,conjugation_momentum,conjugation_real r s _ _ (fun _=>rfl)]
  rfl
def finiteMixed(r s:ℝ)(i:Fin 6)(j:Fin 7)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val):End:=
  (1/2:ℂ) • (GaussCoframeSpin.current j*multiply c hc*(GaussCoframeCore.momentum i+coframeCorrection r s i)+
    (GaussCoframeCore.adjoint i+coframeCorrection r s i)*multiply c hc*GaussCoframeSpin.current j)
private theorem conjugation_mixed(r s:ℝ)(i:Fin 6)(j:Fin 7)(c:SourceCoordinateSlice→ℝ)
    (hc:∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)(hi:∀ z,c (localMap r s z)=c z):
    noiseConjugation r s (GaussCoframeForm.mixed i j c hc)=finiteMixed r s i j c hc:=by
  change noiseConjugation r s ((1/2:ℂ) • (GaussCoframeSpin.current j*multiply c hc*GaussCoframeCore.momentum i+
    GaussCoframeCore.adjoint i*multiply c hc*GaussCoframeSpin.current j))=_
  rw [conjugation_smul r s,conjugation_add r s,conjugation_mul r s,conjugation_mul r s,conjugation_mul r s,conjugation_mul r s,conjugation_spin,conjugation_adjoint,conjugation_momentum,
    conjugation_real r s c hc hi]
  rfl

def finiteCoframeCurrent(r s:ℝ):End:=
  finiteMixed r s 1 5 (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0)+
  finiteMixed r s 3 3 (GaussCoframeForm.currentCoefficient 1) (GaussCoframeForm.currentCoefficient_smooth 1)+
  finiteMixed r s 3 4 (fun z=> -GaussCoframeForm.currentCoefficient 0 z)
    (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg)+
  finiteMixed r s 4 3 (GaussCoframeForm.currentCoefficient 2) (GaussCoframeForm.currentCoefficient_smooth 2)
def finiteCoframeAction(r s:ℝ):End:=
  (∑ i:Fin 6,∑ j:Fin 6,finiteCoframeTerm r s i j)+finiteCoframeCurrent r s+
    (∑ j:Fin 7,GaussCoframeForm.spinSquare j)+GaussCoframeForm.numberShift+
    multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth
private theorem conjugation_coframe_current(r s:ℝ):
    noiseConjugation r s GaussCoframeForm.currentAction=finiteCoframeCurrent r s:=by
  unfold GaussCoframeForm.currentAction
  rw [conjugation_add r s,conjugation_add r s,conjugation_add r s,
    conjugation_mixed r s 1 5 (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0) (fun _=>rfl),
    conjugation_mixed r s 3 3 (GaussCoframeForm.currentCoefficient 1) (GaussCoframeForm.currentCoefficient_smooth 1) (fun _=>rfl),
    conjugation_mixed r s 3 4 (fun z=> -GaussCoframeForm.currentCoefficient 0 z) (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg) (fun _=>rfl),
    conjugation_mixed r s 4 3 (GaussCoframeForm.currentCoefficient 2) (GaussCoframeForm.currentCoefficient_smooth 2) (fun _=>rfl)]
  rfl
private theorem conjugation_spin_square(r s:ℝ)(j:Fin 7):
    noiseConjugation r s (GaussCoframeForm.spinSquare j)=GaussCoframeForm.spinSquare j:=by
  change noiseConjugation r s ((GaussCoframeForm.spinWeight j:ℂ) •
    (GaussCoframeSpin.current j*multiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth*
      GaussCoframeSpin.current j))=_
  rw [conjugation_smul r s,conjugation_mul r s,conjugation_mul r s,conjugation_spin,
    conjugation_real r s _ _ (fun _=>rfl)]
  rfl
private theorem conjugation_number_shift(r s:ℝ):
    noiseConjugation r s GaussCoframeForm.numberShift=GaussCoframeForm.numberShift:=by
  change noiseConjugation r s ((1/2:ℂ) • (GaussCoframeForm.number*
    multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
    multiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth*GaussCoframeForm.number))=_
  rw [conjugation_smul r s,conjugation_add r s,conjugation_mul r s,conjugation_mul r s,conjugation_number,
    conjugation_real r s _ _ (fun _=>rfl)]
  rfl
private theorem conjugation_coframe(r s:ℝ):
    noiseConjugation r s GaussCoframeForm.coframeAction=finiteCoframeAction r s:=by
  simp only [GaussCoframeForm.coframeAction,GaussCoframeKinetic.kinetic,conjugation_add r s,conjugation_sum r s,
    conjugation_coframe_term,conjugation_coframe_current,conjugation_spin_square,
    conjugation_number_shift,conjugation_real r s GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth (fun _=>rfl),finiteCoframeAction]
private theorem conjugation_scalar_kinetic(r s:ℝ):
    noiseConjugation r s scalarKinetic=noiseWeight r s 2*scalarKinetic:=scalar_kinetic_finite r s
private theorem conjugation_gauge_kinetic(r s:ℝ):
    noiseConjugation r s gaugeKinetic=noiseWeight r s (-2)*gaugeKinetic:=gauge_kinetic_finite r s

private theorem conjugation_local(r s d:ℝ)(T:End)(B:SourceCoordinateSlice→FockFiber →L[ℂ] FockFiber)
    (hT:∀ f z,T f z=B z (f z))
    (hB:∀ t z,B (combinedMap t z)=(Real.exp (d*t):ℂ) • B z):
    noiseConjugation r s T=noiseWeight r s (-d)*T:=by
  have hp:T*noiseCore r s=noiseCore r s*(noiseWeight r s (-d)*T):=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change T (noiseCore r s f) z=noiseCore r s (noiseWeight r s (-d) (T f)) z
    rw [hT]
    change B z ((Real.exp ((25/2:ℝ)*parameter r s z):ℂ) • f (localMap r s z))=
      (Real.exp ((25/2:ℝ)*parameter r s z):ℂ) •
        ((Real.exp ((-d)*parameter r s (localMap r s z)):ℂ) • T f (localMap r s z))
    have hi:parameter r s (localMap r s z)=parameter r s z:=rfl
    have hb:B (localMap r s z)=(Real.exp (d*parameter r s z):ℂ) • B z:=hB (parameter r s z) z
    rw [map_smul,hi,hT,hb]
    simp only [smul_apply,smul_smul]
    have he:(Real.exp ((-d)*parameter r s z):ℂ)*(Real.exp (d*parameter r s z):ℂ)=1:=by
      rw [←Complex.ofReal_mul,←Real.exp_add]
      simp only [neg_mul,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
    rw [he,mul_one]
  change noiseCore (-r) (-s)*T*noiseCore r s=noiseWeight r s (-d)*T
  have h:=congrArg (fun R:End=>noiseCore (-r) (-s)*R) hp
  simpa only [←mul_assoc,noise_inverse_end r s,one_mul] using h
private theorem conjugation_real_degree(r s d:ℝ)(T:End)(c:SourceCoordinateSlice→ℝ)
    (hT:∀ f z,T f z=(c z:ℂ) • f z)
    (hc:∀ t z,c (combinedMap t z)=Real.exp (d*t)*c z):
    noiseConjugation r s T=noiseWeight r s (-d)*T:=by
  apply conjugation_local r s d T (fun z=>(c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) hT
  intro t z
  rw [hc,Complex.ofReal_mul,smul_smul]
private theorem scalar_field_finite(t:ℝ)(z:SourceCoordinateSlice):
    scalarField (combinedMap t z)=Real.exp t • scalarField z:=by
  change vacuum+(Real.exp t • ((z.2.1:Scalar)+vacuum)-vacuum)=Real.exp t • (vacuum+(z.2.1:Scalar))
  module
private theorem connection_field_finite(t:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    connectionField (combinedMap t z) i=Real.exp (-t) • connectionField z i:=
  map_smul (SourceCartanCubic.gaugeCoordinate i) (Real.exp (-t)) _
open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
private theorem action_biscalar(r s:ℝ)(phi:Scalar)(b:NativeLie):
    action (r • phi) (s • b)=(r*s) • action phi b:=by
  change scalarP286ActionBilinear (s • b) (r • phi)=(r*s) • scalarP286ActionBilinear b phi
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
private theorem gradient_finite(t:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    scalarGradient (combinedMap t z) i=scalarGradient z i:=by
  change action (scalarField (combinedMap t z)) (connectionField (combinedMap t z) i)=_
  rw [connection_field_finite,scalar_field_finite,action_biscalar]
  rw [←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  rfl
private theorem bracket_scale(t:ℝ)(a b:NativeLie):
    (SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket
      (t • a) (t • b):NativeLie)=t^2 •
      SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket a b:=by
  erw [SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_left,
    SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_right,smul_smul]
  rw [pow_two]
private theorem magnetic_finite(t:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    magneticField (combinedMap t z) i=Real.exp (-2*t) • magneticField z i:=by
  have he:Real.exp (-t)^2=Real.exp (-2*t):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [magneticField,SourceQuantumGaugeCenterMagnetic.magneticOfConnection,
    connection_field_finite,bracket_scale,he]
  fin_cases i <;> rfl
private def centeredValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖scalarField z‖^2
private def vacuumLinearValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*inner ℝ vacuum (scalarField z)
private def vacuumConstantValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖vacuum‖^2
private def spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*GaussNativeEnergy.volume z/2 * ∑ i:Fin 3,∑ j:Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem conjugation_center(r s:ℝ):noiseConjugation r s centeredAction=noiseWeight r s (-2)*centeredAction:=by
  apply conjugation_real_degree r s 2 centeredAction centeredValue (fun _ _=>rfl)
  intro t z
  have he:Real.exp t^2=Real.exp (2*t):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [centeredValue,scalar_field_finite,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,he]
  change sourceTime 0*GaussNativeEnergy.volume z*(Real.exp (2*t)*‖scalarField z‖^2)=_
  ring
private theorem conjugation_vacuum_linear(r s:ℝ):
    noiseConjugation r s vacuumLinearAction=noiseWeight r s (-1)*vacuumLinearAction:=by
  apply conjugation_real_degree r s 1 vacuumLinearAction vacuumLinearValue (fun _ _=>rfl)
  intro t z
  simp only [vacuumLinearValue,scalar_field_finite,real_inner_smul_right,one_mul]
  change sourceTime 0*GaussNativeEnergy.volume z*(Real.exp t*inner ℝ vacuum (scalarField z))=_
  ring
private theorem conjugation_vacuum_constant(r s:ℝ):
    noiseConjugation r s vacuumConstantAction=vacuumConstantAction:=by
  apply conjugation_fixed
  apply (noise_real_multiplier r s _ _ (fun _=>rfl)).symm
private theorem conjugation_spatial(r s:ℝ):noiseConjugation r s scalarSpatialAction=scalarSpatialAction:=by
  apply conjugation_fixed
  apply (noise_real_multiplier r s _ _ ?_).symm
  intro z
  change spatialValue (combinedMap (parameter r s z) z)=spatialValue z
  simp only [spatialValue,gradient_finite]
  rfl
private theorem magnetic_value_finite(t:ℝ)(z:SourceCoordinateSlice):
    magneticPotential (combinedMap t z)=Real.exp ((-4)*t)*magneticPotential z:=by
  have he:Real.exp (-2*t)^2=Real.exp ((-4)*t):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [magneticPotential,magnetic_finite,real_inner_smul_left,real_inner_smul_right]
  change GaussNativeEnergy.volume z/(2*sourceSigma*sourceTime 0)*
    (∑ i:Fin 3,∑ j:Fin 3,inverseSpatial z i j*(Real.exp (-2*t)*(Real.exp (-2*t)*inner ℝ (magneticField z i) (magneticField z j))))=_
  have hh(i j:Fin 3):inverseSpatial z i j*(Real.exp (-2*t)*(Real.exp (-2*t)*inner ℝ (magneticField z i) (magneticField z j)))=
      Real.exp ((-4)*t)*(inverseSpatial z i j*inner ℝ (magneticField z i) (magneticField z j)):=by
    rw [←he];ring
  simp only [hh,←Finset.mul_sum]
  ring
private theorem conjugation_magnetic(r s:ℝ):noiseConjugation r s magneticAction=noiseWeight r s 4*magneticAction:=by
  have h:=conjugation_real_degree r s (-4) magneticAction magneticPotential (fun _ _=>rfl) magnetic_value_finite
  simpa only [neg_neg] using h

private def matterTerm(i b:Fin 3):End:=
  GaussQuantumMultiplier.action (GaussMatterCore.localMatrix i b) (GaussMatterCore.local_smooth i b)
private def matterFiber(i b:Fin 3)(z:SourceCoordinateSlice):FockFiber →L[ℂ] FockFiber:=
  (GaussMatterCore.coefficient i b z:ℂ) • GaussMatterCore.quantumTerm b (connectionField z i)
private theorem matter_term_apply(i b:Fin 3)(f:QuantumTest)(z:SourceCoordinateSlice):
    matterTerm i b f z=matterFiber i b z (f z):=by
  exact congrArg (fun T:FockFiber →L[ℂ] FockFiber=>T (f z))
    (map_smul GaussQuantumMultiplier.quantizer (GaussMatterCore.coefficient i b z:ℂ)
      (GaussMatterCore.matrixTerm b (connectionField z i)))
private theorem conjugation_matter_term(r s:ℝ)(i b:Fin 3):
    noiseConjugation r s (matterTerm i b)=noiseWeight r s 1*matterTerm i b:=by
  have h:=conjugation_local r s (-1) (matterTerm i b) (matterFiber i b) (matter_term_apply i b) (by
    intro t z
    change (GaussMatterCore.coefficient i b z:ℂ) • GaussMatterCore.quantumTerm b (connectionField (combinedMap t z) i)=
      (Real.exp ((-1)*t):ℂ) • ((GaussMatterCore.coefficient i b z:ℂ) • GaussMatterCore.quantumTerm b (connectionField z i))
    rw [connection_field_finite,map_smul,neg_one_mul,smul_comm (GaussMatterCore.coefficient i b z:ℂ) (Real.exp (-t))]
    apply ContinuousLinearMap.ext
    intro f
    exact RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _)
  simpa only [neg_neg] using h
private theorem conjugation_matter(r s:ℝ):
    noiseConjugation r s GaussMatterCore.matterAction=noiseWeight r s 1*GaussMatterCore.matterAction:=by
  change noiseConjugation r s (∑ i:Fin 3,∑ b:Fin 3,matterTerm i b)=noiseWeight r s 1*(∑ i:Fin 3,∑ b:Fin 3,matterTerm i b)
  simp only [conjugation_sum r s,conjugation_matter_term,Finset.mul_sum]
private theorem potential_decompose(z:SourceCoordinateSlice):
    potential z=centeredValue z-2*vacuumLinearValue z+vacuumConstantValue z+spatialValue z+magneticPotential z:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hn:=norm_sub_sq_real (scalarField z) vacuum
  rw [hsub,real_inner_comm vacuum (scalarField z)] at hn
  unfold potential scalarPotential centeredValue vacuumLinearValue vacuumConstantValue spatialValue
  rw [real_inner_self_eq_norm_sq,hn]
  ring
private theorem potential_action_decompose:
    multiply potential potential_smooth=centeredAction-(2:ℂ) • vacuumLinearAction+
      vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (potential z:ℂ) • f z=(centeredValue z:ℂ) • f z-
    (2:ℂ) • ((vacuumLinearValue z:ℂ) • f z)+(vacuumConstantValue z:ℂ) • f z+
    (spatialValue z:ℂ) • f z+(magneticPotential z:ℂ) • f z
  rw [potential_decompose]
  push_cast
  simp only [add_smul,sub_smul,mul_smul]
private theorem complete_split:
    GaussDiagonalHistory.diagonalAction=scalarKinetic+gaugeKinetic+GaussCoframeForm.coframeAction+GaussMatterCore.matterAction+
      centeredAction-(2:ℂ) • vacuumLinearAction+vacuumConstantAction+scalarSpatialAction+magneticAction:=by
  unfold GaussDiagonalHistory.diagonalAction GaussNativeForm.nativeAction
  rw [potential_action_decompose]
  abel
def finiteHamiltonian(r s:ℝ):End:=
  noiseWeight r s 2*scalarKinetic+noiseWeight r s (-2)*gaugeKinetic+finiteCoframeAction r s+
    noiseWeight r s 1*GaussMatterCore.matterAction+noiseWeight r s (-2)*centeredAction-
    (2:ℂ) • (noiseWeight r s (-1)*vacuumLinearAction)+vacuumConstantAction+scalarSpatialAction+
    noiseWeight r s 4*magneticAction
theorem original_noise_hamiltonian_finite(r s:ℝ):
    noiseCore (-r) (-s)*GaussDiagonalHistory.diagonalAction*noiseCore r s=finiteHamiltonian r s:=by
  change noiseConjugation r s GaussDiagonalHistory.diagonalAction=_
  rw [complete_split]
  have hsub(T R:End):noiseConjugation r s (T-R)=noiseConjugation r s T-noiseConjugation r s R:=by
    change noiseCore (-r) (-s)*(T-R)*noiseCore r s=_
    simp only [mul_sub,sub_mul];rfl
  simp only [conjugation_add r s,hsub,conjugation_smul r s,conjugation_scalar_kinetic,
    conjugation_gauge_kinetic,conjugation_coframe,conjugation_matter,conjugation_center,
    conjugation_vacuum_linear,conjugation_vacuum_constant,conjugation_spatial,conjugation_magnetic,finiteHamiltonian]

end LowEnergy.ClockPhiMatchedNoiseHamiltonian
