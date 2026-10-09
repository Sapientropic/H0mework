import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileCoframeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseHamiltonian
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeScaleAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiProfileLocalNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceScalarVirialBulk SourceGaugeRadialCurrent SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceClockPhiCompleteHeatGainPayment
open SourceClockPhiProfileCoframeReturn ClockPhiConservativeHeatSource ClockPhiMatchedNoiseCore SourceKineticScale
open scoped Topology ContDiff InnerProductSpace RealInnerProductSpace Matrix
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev FiberOp:=FockFiber→L[ℂ]FockFiber
private theorem profileInvariant(c:SourceCoordinateSlice→ℝ)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (u:ℝ)(z:SourceCoordinateSlice):c (combinedMap u z)=c z:=hfirst _ _ rfl
private abbrev input(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):Op:=clockProfileAction c hc (profileInvariant c hfirst) 1
private abbrev heat(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):Op:=sourceForwardCore t ht.le*input c hc hfirst
private theorem input_point(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:SourceCoordinateSlice):
    input c hc hfirst f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul]
private def w(t:ℝ)(c:SourceCoordinateSlice→ℝ)(p q:ℝ)(z:SourceCoordinateSlice):ℝ:=
  (forwardRatio t z)^p*Real.exp (q*c z)
private theorem w_smooth(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(p q:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (w t c p q) z.val:=by
  have h:ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact (h.rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').mul ((contDiffAt_const.mul (hc z)).exp)
def actualProfileWeight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(p q:ℝ):Op:=multiply (w t c p q) (w_smooth t ht c hc p q)
private theorem w_invariant(t:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p q s:ℝ)(z:SourceCoordinateSlice):
    w t c p q (combinedMap s z)=w t c p q z:=by
  unfold w
  rw [profileInvariant c hfirst]
  rfl
private theorem complete_forward_point(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:physicalChart):
    profileCompleteCore t ht c hc (profileInvariant c hfirst) f (forwardPoint t z.val)=
      GaussFockWeights.weight (fun N=>(Real.rpow (forwardRatio t z.val) (-((N+3:ℝ)/2)):ℂ))
        ((Real.exp ((25/2:ℝ)*c z.val):ℂ) •
          ((gainProfile (Real.sqrt t) z.val:ℂ) • f (combinedMap (c z.val) z.val))):=by
  apply PiLp.ext
  intro word
  change heat t ht c hc hfirst (sourceGain (Real.sqrt t) f) (forwardPoint t z.val) word=_
  rw [Module.End.mul_apply,forwardCore_apply,input_point]
  have hg:gainProfile (Real.sqrt t) (combinedMap (c z.val) z.val)=gainProfile (Real.sqrt t) z.val:=rfl
  change (_:ℂ)*((Real.exp ((25/2:ℝ)*c z.val):ℂ)*
    ((gainProfile (Real.sqrt t) (combinedMap (c z.val) z.val):ℂ)*f _ word))=_
  rw [hg]
  rfl
private theorem local_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)(B:SourceCoordinateSlice→FiberOp)
    (hT:∀f z,T f z=B z (f z))
    (hNumber:∀z a,Commute (GaussFockWeights.weight a) (B z))
    (hForward:∀z:physicalChart,B (forwardPoint t z.val)=(((forwardRatio t z.val)^p:ℝ):ℂ) • B z.val)
    (hCombined:∀s z,B (combinedMap s z)=(Real.exp (d*s):ℂ) • B z):
    T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T):=by
  have hp(z:physicalChart)(f:QuantumTest):
      T (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (forwardPoint t z.val)=
        profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T f)) (forwardPoint t z.val):=by
    rw [hT,complete_forward_point t ht c hc hfirst,complete_forward_point t ht c hc hfirst,hForward]
    change (((forwardRatio t z.val)^p:ℝ):ℂ) • B z.val
      (GaussFockWeights.weight _ ((_ :ℂ) • ((_ :ℂ) • f _)))=
      GaussFockWeights.weight _ ((_ :ℂ) • ((_ :ℂ) • ((w t c p (-d) _:ℂ) • T f _)))
    rw [w_invariant t c hfirst,hT,hCombined]
    let a:ℕ→ℂ:=fun N=>(Real.rpow (forwardRatio t z.val) (-((N+3:ℝ)/2)):ℂ)
    have hN:GaussFockWeights.weight a (B z.val (f (combinedMap (c z.val) z.val)))=
      B z.val (GaussFockWeights.weight a (f (combinedMap (c z.val) z.val))):=
      congrArg (fun A:FiberOp=>A (f (combinedMap (c z.val) z.val))) (hNumber z.val a).eq
    simp only [smul_apply,map_smul,smul_smul]
    rw [←hN]
    congr 1
    have he:(Real.exp ((-d)*c z.val):ℂ)*(Real.exp (d*c z.val):ℂ)=1:=by
      rw [←Complex.ofReal_mul,←Real.exp_add]
      simp only [neg_mul,neg_add_cancel,Real.exp_zero,Complex.ofReal_one]
    rw [show (-d)*c z.val= -(c z.val*d) by ring,
      show d*c z.val=c z.val*d by ring] at he
    dsimp only [w]
    rw [Complex.ofReal_mul]
    linear_combination (norm:=ring) -(((forwardRatio t z.val)^p:ℝ):ℂ)*
      (Real.exp ((25/2:ℝ)*c z.val):ℂ)*(gainProfile (Real.sqrt t) z.val:ℂ)*he
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro x
  by_cases hx:x∈physicalChart
  · by_cases ha:18*t<GaussNativeEnergy.volume x
    · let z:physicalChart:=⟨backwardPoint t x,backward_chart t ht.le ⟨x,hx⟩ ha⟩
      have hz:forwardPoint t z.val=x:=forward_backward t ht.le x ha
      change T (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) x=profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T f)) x
      rw [←hz]
      exact hp z f
    · change T (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f)) x=
        heat t ht c hc hfirst (sourceGain (Real.sqrt t) (actualProfileWeight t ht c hc p (-d) (T f))) x
      rw [hT]
      change B x (forwardValue t _ x)=forwardValue t _ x
      simp only [forwardValue,if_neg ha,map_zero]
  · have h0(q:QuantumTest):q x=0:=image_eq_zero_of_notMem_tsupport (fun h=>hx (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem scalar_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)(a:SourceCoordinateSlice→ℝ)
    (hT:∀f z,T f z=(a z:ℂ) • f z)
    (hForward:∀z:physicalChart,a (forwardPoint t z.val)=(forwardRatio t z.val)^p*a z.val)
    (hCombined:∀s z,a (combinedMap s z)=Real.exp (d*s)*a z):
    T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T):=by
  apply local_transport t ht c hc hfirst p d T (fun z=>(a z:ℂ) • ContinuousLinearMap.id ℂ FockFiber) hT
  · intro z b
    change GaussFockWeights.weight b*((a z:ℂ) • (1:FiberOp))=((a z:ℂ) • (1:FiberOp))*GaussFockWeights.weight b
    simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  · intro z
    rw [hForward,Complex.ofReal_mul,smul_smul]
  · intro s z
    rw [hCombined,Complex.ofReal_mul,smul_smul]
private theorem heat_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (heat t ht c hc hfirst f) (heat t ht c hc hfirst g)=sourcePair f g:=by
  change sourcePair (sourceForwardCore t ht.le (input c hc hfirst f))
    (sourceForwardCore t ht.le (input c hc hfirst g))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair,clockProfileAction_pair]
private theorem gain_pair(e:ℝ)(f g:QuantumTest):sourcePair (sourceGain e f) g=sourcePair f (sourceGain e g):=by
  have hs(z:physicalChart):ContDiffAt ℝ ∞ (gainProfile e) z.val:=by
    have h:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact h.rpow_const_of_ne (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
  change sourcePair (multiply (gainProfile e) hs f) g=sourcePair f (multiply (gainProfile e) hs g)
  exact (multiply_pair _ _ f g).symm
private theorem gain_squared_weight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (p q:ℝ):
    sourceGain (Real.sqrt t)*(sourceGain (Real.sqrt t)*actualProfileWeight t ht c hc p q)=actualProfileWeight t ht c hc (p+1/3) q:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:(gainProfile (Real.sqrt t) z)^2=(forwardRatio t z)^(1/3:ℝ):=by
      unfold gainProfile
      rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
      congr 1
      norm_num
    have hh:gainProfile (Real.sqrt t) z*gainProfile (Real.sqrt t) z*w t c p q z=w t c (p+1/3) q z:=by
      unfold w
      rw [←pow_two,hg,←mul_assoc,←Real.rpow_add hr,add_comm (1/3:ℝ)]
    apply PiLp.ext
    intro word
    change (gainProfile (Real.sqrt t) z:ℂ)*((gainProfile (Real.sqrt t) z:ℂ)*((w t c p q z:ℂ)*f z word))=(w t c (p+1/3) q z:ℂ)*f z word
    have hc:=congrArg Complex.ofReal hh
    simp only [Complex.ofReal_mul] at hc
    rw [←mul_assoc,←mul_assoc,hc]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • ((_ :ℂ) • ((_ :ℂ) • f z))=(_ :ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero,smul_zero]
private theorem paired_return(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(p d:ℝ)(T:Op)
    (h:T*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc p (-d)*T))(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (T (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (p+1/3) (-d) (T g)):=by
  have hx:=LinearMap.congr_fun h g
  change T (profileCompleteCore t ht c hc (profileInvariant c hfirst) g)=profileCompleteCore t ht c hc (profileInvariant c hfirst) (actualProfileWeight t ht c hc p (-d) (T g)) at hx
  rw [hx]
  change sourcePair (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f))
    (heat t ht c hc hfirst (sourceGain (Real.sqrt t) (actualProfileWeight t ht c hc p (-d) (T g))))=_
  rw [heat_pair,gain_pair]
  exact congrArg (sourcePair f) (LinearMap.congr_fun (gain_squared_weight t ht c hc p (-d)) (T g))

private theorem scalar_field_finite(s:ℝ)(z:SourceCoordinateSlice):scalarField (combinedMap s z)=Real.exp s • scalarField z:=by
  change vacuum+(Real.exp s • ((z.2.1:Scalar)+vacuum)-vacuum)=Real.exp s • (vacuum+(z.2.1:Scalar))
  module
private theorem connection_field_finite(s:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):
    connectionField (combinedMap s z) i=Real.exp (-s) • connectionField z i:=
  map_smul (SourceCartanCubic.gaugeCoordinate i) (Real.exp (-s)) _
open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
private theorem action_biscalar(r s:ℝ)(phi:Scalar)(b:NativeLie):
    action (r • phi) (s • b)=(r*s) • action phi b:=by
  change scalarP286ActionBilinear (s • b) (r • phi)=(r*s) • scalarP286ActionBilinear b phi
  simp only [map_smul,LinearMap.smul_apply,smul_smul]
private theorem gradient_finite(s:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):scalarGradient (combinedMap s z) i=scalarGradient z i:=by
  change action (scalarField (combinedMap s z)) (connectionField (combinedMap s z) i)=_
  rw [connection_field_finite,scalar_field_finite,action_biscalar,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  rfl
private theorem bracket_scale(s:ℝ)(a b:NativeLie):
    (SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket (s • a) (s • b):NativeLie)=
      s^2 • SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket a b:=by
  erw [SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_left,
    SaturationMonoid.PhysicsCore.StageNineCoframeGravityGaugeRegularity.jointP286CoordinateLieBracket_smul_right,smul_smul]
  rw [pow_two]
private theorem magnetic_finite(s:ℝ)(z:SourceCoordinateSlice)(i:Fin 3):magneticField (combinedMap s z) i=Real.exp (-2*s) • magneticField z i:=by
  have he:Real.exp (-s)^2=Real.exp (-2*s):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [magneticField,SourceQuantumGaugeCenterMagnetic.magneticOfConnection,connection_field_finite,bracket_scale,he]
  fin_cases i <;> rfl
private abbrev centerValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖scalarField z‖^2
private abbrev vacLinValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*inner ℝ vacuum (scalarField z)
private abbrev vacConstValue(z:SourceCoordinateSlice):ℝ:=sourceTime 0*GaussNativeEnergy.volume z*‖vacuum‖^2
private abbrev spatialValue(z:SourceCoordinateSlice):ℝ:=
  -(sourceTime 0*GaussNativeEnergy.volume z/2*∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j))
private theorem center_forward(t:ℝ)(ht:0<t)(z:physicalChart):centerValue (forwardPoint t z.val)=(forwardRatio t z.val)^(1:ℝ)*centerValue z.val:=by
  unfold centerValue
  rw [forward_volume t ht.le z,Real.rpow_one]
  unfold forwardRatio
  change sourceTime 0*(GaussNativeEnergy.volume z.val+18*t)*‖scalarField z.val‖^2=_
  field_simp [(volume_pos z).ne']
private theorem center_combined(s:ℝ)(z:SourceCoordinateSlice):centerValue (combinedMap s z)=Real.exp (2*s)*centerValue z:=by
  have he:Real.exp s^2=Real.exp (2*s):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [centerValue,scalar_field_finite,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,he]
  change sourceTime 0*GaussNativeEnergy.volume z*(Real.exp (2*s)*‖scalarField z‖^2)=_
  ring
private theorem vacLin_forward(t:ℝ)(ht:0<t)(z:physicalChart):vacLinValue (forwardPoint t z.val)=(forwardRatio t z.val)^(1:ℝ)*vacLinValue z.val:=by
  unfold vacLinValue
  rw [forward_volume t ht.le z,Real.rpow_one]
  unfold forwardRatio
  change sourceTime 0*(GaussNativeEnergy.volume z.val+18*t)*inner ℝ vacuum (scalarField z.val)=_
  field_simp [(volume_pos z).ne']
private theorem vacLin_combined(s:ℝ)(z:SourceCoordinateSlice):vacLinValue (combinedMap s z)=Real.exp (1*s)*vacLinValue z:=by
  simp only [vacLinValue,scalar_field_finite,real_inner_smul_right,one_mul]
  change sourceTime 0*GaussNativeEnergy.volume z*(Real.exp s*inner ℝ vacuum (scalarField z))=_
  ring
private theorem vacConst_forward(t:ℝ)(ht:0<t)(z:physicalChart):vacConstValue (forwardPoint t z.val)=(forwardRatio t z.val)^(1:ℝ)*vacConstValue z.val:=by
  unfold vacConstValue
  rw [forward_volume t ht.le z,Real.rpow_one]
  unfold forwardRatio
  field_simp [(volume_pos z).ne']
private theorem spatial_scale(r:ℝ)(hr:r≠0)(z:SourceCoordinateSlice):spatialValue (scale r z)=r*spatialValue z:=by
  have hgrad(i:Fin 3):scalarGradient (scale r z) i=scalarGradient z i:=rfl
  simp only [spatialValue,volume_scale,inverse_spatial_scale,hgrad]
  have he(i j:Fin 3):r⁻¹^2*inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)=
      r⁻¹^2*(inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)):=by ring
  simp only [he,←Finset.mul_sum]
  field_simp [hr]
private theorem spatial_forward(t:ℝ)(ht:0<t)(z:physicalChart):spatialValue (forwardPoint t z.val)=(forwardRatio t z.val)^(1/3:ℝ)*spatialValue z.val:=
  spatial_scale _ (Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _).ne' z.val
private theorem spatial_combined(s:ℝ)(z:SourceCoordinateSlice):spatialValue (combinedMap s z)=Real.exp (0*s)*spatialValue z:=by
  simp only [spatialValue,gradient_finite,zero_mul,Real.exp_zero,one_mul]
  rfl
private theorem magnetic_scale(r:ℝ)(hr:r≠0)(z:SourceCoordinateSlice):magneticPotential (scale r z)=r*magneticPotential z:=by
  have hmag(i:Fin 3):magneticField (scale r z) i=magneticField z i:=rfl
  simp only [magneticPotential,volume_scale,inverse_spatial_scale,hmag]
  have he(i j:Fin 3):r⁻¹^2*inverseSpatial z i j*inner ℝ (magneticField z i) (magneticField z j)=
      r⁻¹^2*(inverseSpatial z i j*inner ℝ (magneticField z i) (magneticField z j)):=by ring
  simp only [he,←Finset.mul_sum]
  field_simp [hr]
private theorem magnetic_forward(t:ℝ)(ht:0<t)(z:physicalChart):magneticPotential (forwardPoint t z.val)=(forwardRatio t z.val)^(1/3:ℝ)*magneticPotential z.val:=
  magnetic_scale _ (Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _).ne' z.val
private theorem magnetic_combined(s:ℝ)(z:SourceCoordinateSlice):magneticPotential (combinedMap s z)=Real.exp ((-4)*s)*magneticPotential z:=by
  have he:Real.exp (-2*s)^2=Real.exp ((-4)*s):=by rw [pow_two,←Real.exp_add];congr 1;ring
  simp only [magneticPotential,magnetic_finite,real_inner_smul_left,real_inner_smul_right]
  change GaussNativeEnergy.volume z/(2*sourceSigma*sourceTime 0)*
    (∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*(Real.exp (-2*s)*(Real.exp (-2*s)*inner ℝ (magneticField z i) (magneticField z j))))=_
  have hh(i j:Fin 3):inverseSpatial z i j*(Real.exp (-2*s)*(Real.exp (-2*s)*inner ℝ (magneticField z i) (magneticField z j)))=
      Real.exp ((-4)*s)*(inverseSpatial z i j*inner ℝ (magneticField z i) (magneticField z j)):=by rw [←he];ring
  simp only [hh,←Finset.mul_sum]
  ring
private abbrev matterMatrix(z:SourceCoordinateSlice):Matrix Mode Mode ℂ:=∑i:Fin 3,∑b:Fin 3,GaussMatterCore.localMatrix i b z
private theorem matter_point(f:QuantumTest)(z:SourceCoordinateSlice):
    GaussMatterCore.matterAction f z=GaussQuantumMultiplier.quantized (matterMatrix z) (f z):=by
  change (∑i:Fin 3,∑b:Fin 3,GaussQuantumMultiplier.quantizer (GaussMatterCore.localMatrix i b z) (f z))=
    GaussQuantumMultiplier.quantizer (∑i:Fin 3,∑b:Fin 3,GaussMatterCore.localMatrix i b z) (f z)
  simp only [map_sum,sum_apply]
private theorem matter_matrix_forward(t:ℝ)(ht:0<t)(z:physicalChart):
    matterMatrix (forwardPoint t z.val)=(((forwardRatio t z.val)^(-1/3:ℝ):ℝ):ℂ) • matterMatrix z.val:=by
  have hi(i b:Fin 3):GaussMatterCore.localMatrix i b (forwardPoint t z.val)=
      (((forwardRatio t z.val)^(-1/3:ℝ):ℝ):ℂ) • GaussMatterCore.localMatrix i b z.val:=by
    unfold GaussMatterCore.localMatrix GaussMatterCore.coefficient forwardPoint
    rw [triad_inverse_scale,smul_smul,←Real.rpow_neg (forward_ratio_pos t ht.le z).le]
    change ((2*sourceTime 0*((forwardRatio t z.val)^(-(1/3:ℝ))*triadInverse z.val.1 i b):ℝ):ℂ) •
      GaussMatterCore.matrixTerm b (connectionField z.val i)=_
    congr 1
    push_cast
    ring
  simp only [matterMatrix,hi,←Finset.smul_sum]
private theorem matter_matrix_combined(s:ℝ)(z:SourceCoordinateSlice):matterMatrix (combinedMap s z)=(Real.exp ((-1)*s):ℂ) • matterMatrix z:=by
  have hi(i b:Fin 3):GaussMatterCore.localMatrix i b (combinedMap s z)=(Real.exp ((-1)*s):ℂ) • GaussMatterCore.localMatrix i b z:=by
    have hc:GaussMatterCore.coefficient i b (combinedMap s z)=GaussMatterCore.coefficient i b z:=rfl
    simp only [GaussMatterCore.localMatrix,connection_field_finite,hc,map_smul,neg_one_mul]
    apply Matrix.ext
    intro row col
    change (GaussMatterCore.coefficient i b z:ℂ)*((Real.exp (-s):ℂ)*GaussMatterCore.matrixTerm b (connectionField z i) row col)=
      (Real.exp (-s):ℂ)*((GaussMatterCore.coefficient i b z:ℂ)*GaussMatterCore.matrixTerm b (connectionField z i) row col)
    ring
  simp only [matterMatrix,hi,←Finset.smul_sum]
private theorem center_point(f:QuantumTest)(z:SourceCoordinateSlice):centeredAction f z=(centerValue z:ℂ) • f z:=rfl
private theorem vacLin_point(f:QuantumTest)(z:SourceCoordinateSlice):vacuumLinearAction f z=(vacLinValue z:ℂ) • f z:=rfl
private theorem vacConst_point(f:QuantumTest)(z:SourceCoordinateSlice):vacuumConstantAction f z=(vacConstValue z:ℂ) • f z:=rfl
private theorem spatial_point(f:QuantumTest)(z:SourceCoordinateSlice):scalarSpatialAction f z=(spatialValue z:ℂ) • f z:=rfl
private theorem magnetic_point(f:QuantumTest)(z:SourceCoordinateSlice):magneticAction f z=(magneticPotential z:ℂ) • f z:=rfl
attribute [local irreducible] GaussMatterCore.matterAction centeredAction vacuumLinearAction vacuumConstantAction scalarSpatialAction magneticAction
private theorem matter_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    GaussMatterCore.matterAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc (-1/3) (-(-1:ℝ))*GaussMatterCore.matterAction):=by
  apply local_transport t ht c hc hfirst (-1/3) (-1) GaussMatterCore.matterAction (fun z=>GaussQuantumMultiplier.quantized (matterMatrix z)) matter_point
  · intro z a
    exact GaussQuantumMultiplier.weight_commute a (matterMatrix z)
  · intro z
    have h:=congrArg GaussQuantumMultiplier.quantizer (matter_matrix_forward t ht z)
    simpa only [map_smul] using! h
  · intro s z
    have h:=congrArg GaussQuantumMultiplier.quantizer (matter_matrix_combined s z)
    simpa only [map_smul] using! h
private theorem center_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    centeredAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc 1 (-2)*centeredAction):=
  scalar_transport t ht c hc hfirst 1 2 centeredAction centerValue center_point (center_forward t ht) center_combined
private theorem vacLin_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    vacuumLinearAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc 1 (-1)*vacuumLinearAction):=
  scalar_transport t ht c hc hfirst 1 1 vacuumLinearAction vacLinValue vacLin_point (vacLin_forward t ht) vacLin_combined
private theorem vacConst_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    vacuumConstantAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc 1 (-(0:ℝ))*vacuumConstantAction):=by
  apply scalar_transport t ht c hc hfirst 1 0 vacuumConstantAction vacConstValue vacConst_point (vacConst_forward t ht)
  intro s z
  simp only [zero_mul,Real.exp_zero,one_mul]
  rfl
private theorem spatial_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    scalarSpatialAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc (1/3) (-(0:ℝ))*scalarSpatialAction):=
  scalar_transport t ht c hc hfirst (1/3) 0 scalarSpatialAction spatialValue spatial_point (spatial_forward t ht) spatial_combined
private theorem magnetic_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):
    magneticAction*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*(actualProfileWeight t ht c hc (1/3) (-(-4:ℝ))*magneticAction):=
  scalar_transport t ht c hc hfirst (1/3) (-4) magneticAction magneticPotential magnetic_point (magnetic_forward t ht) magnetic_combined

private def forwardAction(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Op:=
  multiply (fun x=>b (forwardPoint t x)) (fun z=>by
    simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))
private theorem input_forward_commute(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hbfirst:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y):
    Commute (input c hc hfirst) (forwardAction t ht b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change input c hc hfirst (forwardAction t ht b hb f) z word=(b (forwardPoint t z):ℂ)*input c hc hfirst f z word
  rw [input_point,input_point]
  change (_:ℂ)*((b (forwardPoint t (combinedMap (c z) z)):ℂ)*f _ word)=_
  have he:b (forwardPoint t (combinedMap (c z) z))=b (forwardPoint t z):=hbfirst _ _ rfl
  rw [he]
  simp only [PiLp.smul_apply,smul_eq_mul]
  ring
private theorem scalar_gain(t:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (sourceGain (Real.sqrt t)) (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (_:ℂ) • ((_ :ℂ) • f z)=(_ :ℂ) • ((_ :ℂ) • f z)
  exact smul_comm _ _ _
private theorem coframe_multiplier_transport(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hbfirst:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y):
    multiply b hb*profileCompleteCore t ht c hc (profileInvariant c hfirst)=profileCompleteCore t ht c hc (profileInvariant c hfirst)*forwardAction t ht b hb:=by
  have hJ:=SourceClockPhiForwardGeneratorTransport.actual_forward_multiplier_transport t ht.le b hb
  change multiply b hb*sourceForwardCore t ht.le=sourceForwardCore t ht.le*forwardAction t ht b hb at hJ
  have hN:=(input_forward_commute t ht c hc hfirst b hb hbfirst).eq
  have hG:sourceGain (Real.sqrt t)*forwardAction t ht b hb=forwardAction t ht b hb*sourceGain (Real.sqrt t):=by
    exact (scalar_gain t (fun x=>b (forwardPoint t x)) (fun z=>by
      simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))).eq
  change multiply b hb*(heat t ht c hc hfirst*sourceGain (Real.sqrt t))=_
  change multiply b hb*(sourceForwardCore t ht.le*input c hc hfirst*sourceGain (Real.sqrt t))=_
  calc
    _=(multiply b hb*sourceForwardCore t ht.le)*input c hc hfirst*sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*forwardAction t ht b hb)*input c hc hfirst*sourceGain (Real.sqrt t):=by rw [hJ]
    _=(sourceForwardCore t ht.le*(forwardAction t ht b hb*input c hc hfirst))*sourceGain (Real.sqrt t):=by noncomm_ring
    _=(sourceForwardCore t ht.le*(input c hc hfirst*forwardAction t ht b hb))*sourceGain (Real.sqrt t):=by rw [←hN]
    _=(sourceForwardCore t ht.le*input c hc hfirst)*(forwardAction t ht b hb*sourceGain (Real.sqrt t)):=by noncomm_ring
    _=(sourceForwardCore t ht.le*input c hc hfirst)*(sourceGain (Real.sqrt t)*forwardAction t ht b hb):=by rw [←hG]
    _=(sourceForwardCore t ht.le*input c hc hfirst*sourceGain (Real.sqrt t))*forwardAction t ht b hb:=by noncomm_ring
    _=_:=rfl
private theorem coframe_weight_smooth(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(gainProfile (Real.sqrt t) x)^2*b (forwardPoint t x)) z.val:=by
  have h:ContDiffAt ℝ ∞ (gainProfile (Real.sqrt t)) z.val:=by
    have hr:ContDiffAt ℝ ∞ (forwardRatio ((Real.sqrt t)^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact hr.rpow_const_of_ne (forward_ratio_pos _ (sq_nonneg _) z).ne'
  exact (h.pow 2).mul (by
    simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))

theorem actual_profile_coframe_multiplier_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hbfirst:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (multiply b hb (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (multiply (fun z=>(gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z))
        (coframe_weight_smooth t ht b hb) g):=by
  have h:=LinearMap.congr_fun (coframe_multiplier_transport t ht c hc hfirst b hb hbfirst) g
  change multiply b hb (profileCompleteCore t ht c hc (profileInvariant c hfirst) g)=profileCompleteCore t ht c hc (profileInvariant c hfirst) (forwardAction t ht b hb g) at h
  rw [h]
  change sourcePair (heat t ht c hc hfirst (sourceGain (Real.sqrt t) f))
    (heat t ht c hc hfirst (sourceGain (Real.sqrt t) (forwardAction t ht b hb g)))=_
  rw [heat_pair,gain_pair]
  apply congrArg (sourcePair f)
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (gainProfile (Real.sqrt t) z:ℂ)*((gainProfile (Real.sqrt t) z:ℂ)*((b (forwardPoint t z):ℂ)*g z word))=
    (((gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z):ℝ):ℂ)*g z word
  push_cast
  ring


theorem actual_profile_complete_matter_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (GaussMatterCore.matterAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (0) (1) (GaussMatterCore.matterAction g)):=by
  have h:=paired_return t ht c hc hfirst (-1/3) (-1) GaussMatterCore.matterAction (matter_transport t ht c hc hfirst) f g
  rw [show (-1/3:ℝ)+1/3=(0) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

theorem actual_profile_complete_centered_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (centeredAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (4/3) (-2) (centeredAction g)):=by
  have h:=paired_return t ht c hc hfirst (1) (2) centeredAction (center_transport t ht c hc hfirst) f g
  rw [show (1:ℝ)+1/3=(4/3) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

theorem actual_profile_complete_vacuum_linear_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (vacuumLinearAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (4/3) (-1) (vacuumLinearAction g)):=by
  have h:=paired_return t ht c hc hfirst (1) (1) vacuumLinearAction (vacLin_transport t ht c hc hfirst) f g
  rw [show (1:ℝ)+1/3=(4/3) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

theorem actual_profile_complete_vacuum_constant_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (vacuumConstantAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (4/3) (0) (vacuumConstantAction g)):=by
  have h:=paired_return t ht c hc hfirst (1) (0) vacuumConstantAction (vacConst_transport t ht c hc hfirst) f g
  rw [show (1:ℝ)+1/3=(4/3) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

theorem actual_profile_complete_signed_spatial_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (scalarSpatialAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (2/3) (0) (scalarSpatialAction g)):=by
  have h:=paired_return t ht c hc hfirst (1/3) (0) scalarSpatialAction (spatial_transport t ht c hc hfirst) f g
  rw [show (1/3:ℝ)+1/3=(2/3) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

theorem actual_profile_complete_magnetic_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f g:QuantumTest):
    sourcePair (profileCompleteCore t ht c hc (profileInvariant c hfirst) f) (magneticAction (profileCompleteCore t ht c hc (profileInvariant c hfirst) g))=
      sourcePair f (actualProfileWeight t ht c hc (2/3) (4) (magneticAction g)):=by
  have h:=paired_return t ht c hc hfirst (1/3) (-4) magneticAction (magnetic_transport t ht c hc hfirst) f g
  rw [show (1/3:ℝ)+1/3=(2/3) by norm_num] at h
  simpa only [neg_neg,neg_zero] using h

end LowEnergy.SourceClockPhiProfileLocalNativeReturn
