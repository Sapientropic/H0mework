import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoframeForwardCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedNoiseCore
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeScaleAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardGeneratorTransport
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatHamiltonianCoefficient
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatLocalNativeWork
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiHeatNativeHamiltonianWork
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussLiveMomentum GaussFockWeights SourceCoframeVolume SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceKineticScale
open ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource GaussNativeEnergy SourceScalarAffineScaleTransport
open SourceClockPhiCompleteHeatGainPayment SourceClockPhiHeatHamiltonianCoefficient
open scoped ContDiff Topology
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private def forwardAmplitude(t:ℝ)(z:SourceCoordinateSlice):FockFiber→L[ℂ]FockFiber:=
  weight (fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ))
private theorem forward_value_above(t:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)
    (hz:18*t<GaussNativeEnergy.volume z):
    forwardValue t f z=forwardAmplitude t z (f (backwardPoint t z)):=by
  apply PiLp.ext
  intro word
  rw [forwardValue,if_pos hz]
  rfl
private theorem native_volume(s:ℝ)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    GaussNativeEnergy.volume (z+s • (0,v))=GaussNativeEnergy.volume z:=by
  simp only [GaussNativeEnergy.volume,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
private theorem native_ratio(t s:ℝ)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    backwardRatio t (z+s • (0,v))=backwardRatio t z:=by
  unfold backwardRatio
  rw [native_volume]
private theorem backward_native_line(t s:ℝ)(z:SourceCoordinateSlice)(v:GaussLiveMomentum.Slice):
    backwardPoint t (z+s • (0,v))=backwardPoint t z+s • (0,v):=by
  unfold backwardPoint
  rw [native_ratio]
  simp only [SourceCoframeVolume.scale,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero,Prod.snd_add,Prod.smul_snd]
  apply Prod.ext <;> simp
private theorem forward_native_line(t:ℝ)(ht:0≤t)(f:QuantumTest)(z:SourceCoordinateSlice)
    (v:GaussLiveMomentum.Slice)(hz:18*t<GaussNativeEnergy.volume z)(s:ℝ):
    sourceForwardCore t ht f (z+s • (0,v))=
      forwardAmplitude t z (f (backwardPoint t z+s • (0,v))):=by
  change forwardValue t f (z+s • (0,v))=_
  rw [forward_value_above t f _ (by rw [native_volume];exact hz),backward_native_line]
  simp only [forwardAmplitude,native_ratio]
private theorem forward_native_fderiv(t:ℝ)(ht:0≤t)(f:QuantumTest)(z:SourceCoordinateSlice)
    (v:GaussLiveMomentum.Slice)(hz:18*t<GaussNativeEnergy.volume z):
    fderiv ℝ (sourceForwardCore t ht f) z (0,v)=
      forwardAmplitude t z (fderiv ℝ f (backwardPoint t z) (0,v)):=by
  have hline(x:SourceCoordinateSlice):HasDerivAt (fun s:ℝ=>x+s • (0,v)) (0,v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,v)).const_add x
  have hl:=(((sourceForwardCore t ht f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    0 (hline z) (by simp)
  have hv:=(((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=backwardPoint t z)).comp_hasDerivAt_of_eq
    0 (hline (backwardPoint t z)) (by simp))
  have hr:=((forwardAmplitude t z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hv
  have he:(fun s:ℝ=>sourceForwardCore t ht f (z+s • (0,v)))=
      fun s:ℝ=>forwardAmplitude t z (f (backwardPoint t z+s • (0,v))):=
    funext (forward_native_line t ht f z v hz)
  dsimp only [Function.comp_def] at hl hr
  rw [he] at hl
  exact hl.unique hr

theorem actual_forward_native_momentum(t:ℝ)(ht:0≤t)(v:Ambient):
    GaussCoreDifferential.covariantMomentum v*sourceForwardCore t ht=
      sourceForwardCore t ht*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreDifferential.covariantMomentum v (sourceForwardCore t ht f) z=
    sourceForwardCore t ht (GaussCoreDifferential.covariantMomentum v f) z
  by_cases hz:18*t<GaussNativeEnergy.volume z
  · rw [covariantMomentum_apply,forward_native_fderiv t ht f z (inverseL z v).2 hz]
    change _=forwardValue t (GaussCoreDifferential.covariantMomentum v f) z
    rw [forward_value_above t _ z hz,covariantMomentum_apply]
    have hinv:inverseL (backwardPoint t z)=inverseL z:=inverse_coframe_scale _ _
    rw [hinv]
    have hzero:sourceForwardCore t ht f z=forwardAmplitude t z (f (backwardPoint t z)):=
      forward_value_above t f z hz
    have hc:=congrArg (fun A:FockFiber→L[ℂ]FockFiber=>A (f (backwardPoint t z)))
      (native_weight_commute (fun N=>(Real.rpow (backwardRatio t z) ((N+3:ℝ)/2):ℂ)) (inverseL z v).1).eq
    change forwardAmplitude t z (GaussNativeMatter.nativeFock (inverseL z v).1 (f (backwardPoint t z)))=
      GaussNativeMatter.nativeFock (inverseL z v).1 (forwardAmplitude t z (f (backwardPoint t z))) at hc
    rw [hzero]
    rw [map_smul,map_add,hc]
  · have hline:∀s:ℝ,sourceForwardCore t ht f (z+s • (0,(inverseL z v).2))=0:=by
      intro s
      change forwardValue t f _=0
      rw [forwardValue,if_neg (by rw [native_volume];exact hz)]
    have hd:HasDerivAt (fun s:ℝ=>sourceForwardCore t ht f (z+s • (0,(inverseL z v).2)))
        (fderiv ℝ (sourceForwardCore t ht f) z (0,(inverseL z v).2)) 0:=by
      have hq:HasDerivAt (fun s:ℝ=>z+s • (0,(inverseL z v).2)) (0,(inverseL z v).2) 0:=by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,(inverseL z v).2)).const_add z
      exact (((sourceForwardCore t ht f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq 0 hq (by simp)
    have he:fderiv ℝ (sourceForwardCore t ht f) z (0,(inverseL z v).2)=0:=by
      rw [funext hline] at hd
      exact hd.unique (hasDerivAt_const (0:ℝ) (0:FockFiber))
    change GaussCoreDifferential.covariantMomentum v (sourceForwardCore t ht f) z=forwardValue t _ z
    rw [covariantMomentum_apply,he,show sourceForwardCore t ht f z=0 from by simpa only [zero_smul,add_zero] using hline 0]
    simp only [map_zero,add_zero,smul_zero,forwardValue,if_neg hz]
private theorem combinedMap_chart(t:ℝ)(z:SourceCoordinateSlice):
    combinedMap t z∈physicalChart ↔ z∈physicalChart:=by
  have hg:=SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-t)) (Real.exp_pos (-t))
    (SourceScalarAffineScaleTransport.scaleEquiv t z)
  have hp:=SourceScalarAffineScaleTransport.scale_chart_iff t z
  exact hg.trans hp

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
theorem inverse_scalar_finite(t:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
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
theorem inverse_gauge_finite(t:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
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



private def heatNoise(t:ℝ)(ht:0<t)(ξ:ℝ):Op:=
  (show {N:Op // sourceForwardCore t ht.le*N=sourceHeatCore t ht ξ} from ⟨_,rfl⟩).val
private def noiseParameter(t ξ:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatMean t z+Real.sqrt (heatVariance t z)*ξ
private theorem heatNoise_point(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    heatNoise t ht ξ f z=(Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
      f (combinedMap (noiseParameter t ξ z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*noiseParameter t ξ z)):ℂ) •
    f (combinedMap (1*noiseParameter t ξ z) z)=_
  simp only [one_mul]
private theorem noise_parameter_native(t ξ s:ℝ)(z:SourceCoordinateSlice)(v:Slice):
    noiseParameter t ξ (z+s • (0,v))=noiseParameter t ξ z:=by
  unfold noiseParameter heatMean heatVariance heatLog reciprocalVolume
  rw [native_volume]
private def profileNative(c:ℝ)(v:Slice):SourceCoordinateSlice:=
  (0,Real.exp c • v.1,Real.exp (-c) • v.2)
private theorem heatMap_native_line(t ξ s:ℝ)(z:SourceCoordinateSlice)(v:Slice):
    combinedMap (noiseParameter t ξ (z+s • (0,v))) (z+s • (0,v))=
      combinedMap (noiseParameter t ξ z) z+s • profileNative (noiseParameter t ξ z) v:=by
  rw [noise_parameter_native]
  simp only [combinedMap_apply,profileNative]
  apply Prod.ext
  · simp
  apply Prod.ext
  · change Real.exp (noiseParameter t ξ z) • ((z.2.1+s • v.1)+vacuumSlice)-vacuumSlice=
      (Real.exp (noiseParameter t ξ z) • (z.2.1+vacuumSlice)-vacuumSlice)+s • (Real.exp (noiseParameter t ξ z) • v.1)
    module
  · change Real.exp (-(noiseParameter t ξ z)) • (z.2.2+s • v.2)=
      Real.exp (-(noiseParameter t ξ z)) • z.2.2+s • (Real.exp (-(noiseParameter t ξ z)) • v.2)
    module
private theorem heatNoise_native_line(t:ℝ)(ht:0<t)(ξ s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(v:Slice):
    heatNoise t ht ξ f (z+s • (0,v))=
      (Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
        f (combinedMap (noiseParameter t ξ z) z+s • profileNative (noiseParameter t ξ z) v):=by
  rw [heatNoise_point,heatMap_native_line,noise_parameter_native]
private theorem heatNoise_native_derivative(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(v:Slice):
    fderiv ℝ (heatNoise t ht ξ f) z (0,v)=
      (Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
        fderiv ℝ f (combinedMap (noiseParameter t ξ z) z) (profileNative (noiseParameter t ξ z) v):=by
  have hz:HasDerivAt (fun s:ℝ=>z+s • (0,v)) (0,v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,v)).const_add z
  have hx:HasDerivAt (fun s:ℝ=>combinedMap (noiseParameter t ξ z) z+s • profileNative (noiseParameter t ξ z) v)
      (profileNative (noiseParameter t ξ z) v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (profileNative (noiseParameter t ξ z) v)).const_add (combinedMap (noiseParameter t ξ z) z)
  have hl:=(((heatNoise t ht ξ f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    (0:ℝ) hz (by simp)
  have hr:=(((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=combinedMap (noiseParameter t ξ z) z)).comp_hasDerivAt_of_eq
    (0:ℝ) hx (by simp)).const_smul (Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ)
  have he:(fun s:ℝ=>heatNoise t ht ξ f (z+s • (0,v)))=
      fun s:ℝ=>(Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
        f (combinedMap (noiseParameter t ξ z) z+s • profileNative (noiseParameter t ξ z) v):=
    funext (fun s=>heatNoise_native_line t ht ξ s f z v)
  dsimp only [Function.comp_def] at hl hr
  rw [he] at hl
  exact hl.unique hr
private theorem heat_native_intertwine(t:ℝ)(ht:0<t)(ξ k:ℝ)(z:physicalChart)(v:Ambient)
    (hd:profileNative (noiseParameter t ξ z.val) (inverseL z.val v).2=
      k • direction v (combinedMap (noiseParameter t ξ z.val) z.val))
    (hb:(inverseL z.val v).1=k • (inverseL (combinedMap (noiseParameter t ξ z.val) z.val) v).1)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (heatNoise t ht ξ f) z.val=
      (k:ℂ) • heatNoise t ht ξ (GaussCoreDifferential.covariantMomentum v f) z.val:=by
  rw [covariantMomentum_apply,heatNoise_native_derivative,hd,map_smul,hb]
  rw [heatNoise_point t ht ξ f z.val,heatNoise_point t ht ξ (GaussCoreDifferential.covariantMomentum v f) z.val,covariantMomentum_apply]
  unfold direction
  simp only [map_smul,smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  module


private theorem profile_scalar_direction(t ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    profileNative (noiseParameter t ξ z.val) (inverseL z.val v).2=
      Real.exp (noiseParameter t ξ z.val) • direction v (combinedMap (noiseParameter t ξ z.val) z.val):=by
  let c:=noiseParameter t ξ z.val
  have he:Real.exp c*Real.exp (-2*c)=Real.exp (-c):=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp c • (inverseL z.val v).2.1,Real.exp (-c) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp c • (0,(inverseL (combinedMap c z.val) v).2)
  rw [inverse_scalar_finite c z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem profile_scalar_inverse(t ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    (inverseL z.val v).1=Real.exp (noiseParameter t ξ z.val) •
      (inverseL (combinedMap (noiseParameter t ξ z.val) z.val) v).1:=by
  rw [inverse_scalar_finite _ z v hv]
  simp only [smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
private theorem profile_gauge_direction(t ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    profileNative (noiseParameter t ξ z.val) (inverseL z.val v).2=
      Real.exp (-(noiseParameter t ξ z.val)) • direction v (combinedMap (noiseParameter t ξ z.val) z.val):=by
  let c:=noiseParameter t ξ z.val
  have he:Real.exp (-c)*Real.exp (2*c)=Real.exp c:=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp c • (inverseL z.val v).2.1,Real.exp (-c) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp (-c) • (0,(inverseL (combinedMap c z.val) v).2)
  rw [inverse_gauge_finite c z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem profile_gauge_inverse(t ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    (inverseL z.val v).1=Real.exp (-(noiseParameter t ξ z.val)) •
      (inverseL (combinedMap (noiseParameter t ξ z.val) z.val) v).1:=by
  rw [inverse_gauge_finite _ z v hv]
  simp only [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]

private theorem actual_profile_scalar_momentum(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (heatNoise t ht ξ f) z.val=
      (Real.exp (noiseParameter t ξ z.val):ℂ) • heatNoise t ht ξ (GaussCoreDifferential.covariantMomentum v f) z.val:=
  heat_native_intertwine t ht ξ _ z v (profile_scalar_direction t ξ z v hv) (profile_scalar_inverse t ξ z v hv) f
private theorem actual_profile_gauge_momentum(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (heatNoise t ht ξ f) z.val=
      (Real.exp (-(noiseParameter t ξ z.val)):ℂ) • heatNoise t ht ξ (GaussCoreDifferential.covariantMomentum v f) z.val:=
  heat_native_intertwine t ht ξ _ z v (profile_gauge_direction t ξ z v hv) (profile_gauge_inverse t ξ z v hv) f


private theorem noise_parameter_smooth(t:ℝ)(ht:0<t)(ξ:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (noiseParameter t ξ) z.val:=by
  have hu:=reciprocal_volume_smooth z
  have hp:0<reciprocalVolume z.val:=by unfold reciprocalVolume;exact inv_pos.mpr (GaussNativeEnergy.volume_pos z)
  have hL:ContDiffAt ℝ ∞ (heatLog t) z.val:=
    (contDiffAt_const.add (contDiffAt_const.mul hu)).log (by change 1+18*t*reciprocalVolume z.val≠0;positivity)
  have hLp:0<heatLog t z.val:=by
    apply Real.log_pos
    change 1<1+18*t*reciprocalVolume z.val
    nlinarith
  have hw:ContDiffAt ℝ ∞ (fun x=>Real.sqrt (heatVariance t x)) z.val:=
    (hL.div_const 9).sqrt (by change heatLog t z.val/9≠0;positivity)
  exact ((hL.neg.div_const 6).add (hw.mul contDiffAt_const))
private def profileWeight(t:ℝ)(ht:0<t)(ξ q:ℝ):Op:=
  multiply (fun z=>Real.exp (q*noiseParameter t ξ z))
    (fun z=>(contDiffAt_const.mul (noise_parameter_smooth t ht ξ z)).exp)
private theorem profileWeight_invariant(t ξ q:ℝ)(z:SourceCoordinateSlice):
    noiseParameter t ξ (combinedMap q z)=noiseParameter t ξ z:=rfl
theorem native_multiplier_commute(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀z:SourceCoordinateSlice,∀w:Slice,∀s:ℝ,b (z+s • (0,w))=b z)
    (v:Ambient):
    GaussCoreDifferential.covariantMomentum v*multiply b hb=multiply b hb*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let w:Slice:=(inverseL z v).2
  have hz:HasDerivAt (fun s:ℝ=>z+s • (0,w)) (0,w) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,w)).const_add z
  have hl:=(((multiply b hb f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    (0:ℝ) hz (by simp)
  have hr:=(((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    (0:ℝ) hz (by simp)).const_smul (b z:ℂ)
  have he:(fun s:ℝ=>multiply b hb f (z+s • (0,w)))=
      fun s:ℝ=>(b z:ℂ) • f (z+s • (0,w)):=by
    funext s
    change (b (z+s • (0,w)):ℂ) • f (z+s • (0,w))=_
    rw [hi]
  dsimp only [Function.comp_def] at hl hr
  rw [he] at hl
  have hd:fderiv ℝ (multiply b hb f) z (0,w)=(b z:ℂ) • fderiv ℝ f z (0,w):=hl.unique hr
  change GaussCoreDifferential.covariantMomentum v (multiply b hb f) z=
    multiply b hb (GaussCoreDifferential.covariantMomentum v f) z
  rw [covariantMomentum_apply,hd]
  change _=(b z:ℂ) • GaussCoreDifferential.covariantMomentum v f z
  rw [covariantMomentum_apply]
  change (-Complex.I) • ((b z:ℂ) • fderiv ℝ f z (0,(inverseL z v).2)+
    GaussNativeMatter.nativeFock (inverseL z v).1 ((b z:ℂ) • f z))=_
  rw [map_smul]
  module
private theorem heatNoise_coframe_multiplier(t:ℝ)(ht:0<t)(ξ:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀z q,b (combinedMap q z)=b z):
    heatNoise t ht ξ*multiply b hb=multiply b hb*heatNoise t ht ξ:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change heatNoise t ht ξ (multiply b hb f) z=(b z:ℂ) • heatNoise t ht ξ f z
  rw [heatNoise_point,heatNoise_point]
  change _ • ((b (combinedMap (noiseParameter t ξ z) z):ℂ) • f _)=_
  rw [hi]
  exact smul_comm _ _ _
private theorem scalar_profile_return(t:ℝ)(ht:0<t)(ξ:ℝ)(v:Ambient)(hv:v.2=0):
    GaussCoreDifferential.covariantMomentum v*heatNoise t ht ξ=
      heatNoise t ht ξ*profileWeight t ht ξ 1*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreDifferential.covariantMomentum v (heatNoise t ht ξ f) z=
    heatNoise t ht ξ (profileWeight t ht ξ 1 (GaussCoreDifferential.covariantMomentum v f)) z
  by_cases hz:z∈physicalChart
  · rw [actual_profile_scalar_momentum t ht ξ ⟨z,hz⟩ v hv f,heatNoise_point,heatNoise_point]
    change (Real.exp (noiseParameter t ξ z):ℂ) •
      ((Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (noiseParameter t ξ z) z))=
      (Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
        ((Real.exp (1*noiseParameter t ξ (combinedMap (noiseParameter t ξ z) z)):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (noiseParameter t ξ z) z))
    rw [profileWeight_invariant,one_mul]
    exact smul_comm _ _ _
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem gauge_profile_return(t:ℝ)(ht:0<t)(ξ:ℝ)(v:Ambient)(hv:v.1=0):
    GaussCoreDifferential.covariantMomentum v*heatNoise t ht ξ=
      heatNoise t ht ξ*profileWeight t ht ξ (-1)*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreDifferential.covariantMomentum v (heatNoise t ht ξ f) z=
    heatNoise t ht ξ (profileWeight t ht ξ (-1) (GaussCoreDifferential.covariantMomentum v f)) z
  by_cases hz:z∈physicalChart
  · rw [actual_profile_gauge_momentum t ht ξ ⟨z,hz⟩ v hv f,heatNoise_point,heatNoise_point]
    change (Real.exp (-(noiseParameter t ξ z)):ℂ) •
      ((Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (noiseParameter t ξ z) z))=
      (Real.exp ((25/2:ℝ)*noiseParameter t ξ z):ℂ) •
        ((Real.exp (-1*noiseParameter t ξ (combinedMap (noiseParameter t ξ z) z)):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (noiseParameter t ξ z) z))
    rw [profileWeight_invariant,neg_one_mul]
    exact smul_comm _ _ _
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]


private theorem gain_native_commute(e:ℝ)(v:Ambient):
    GaussCoreDifferential.covariantMomentum v*SourceClockPhiActualCovarianceStep.sourceGain e=
      SourceClockPhiActualCovarianceStep.sourceGain e*GaussCoreDifferential.covariantMomentum v:=by
  have hb(z:physicalChart):ContDiffAt ℝ ∞ (SourceClockPhiActualCovarianceStep.gainProfile e) z.val:=by
    have hr:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact hr.rpow_const_of_ne (p:=(1/6:ℝ)) (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
  have hi(z:SourceCoordinateSlice)(w:Slice)(r:ℝ):
      SourceClockPhiActualCovarianceStep.gainProfile e (z+r • (0,w))=
        SourceClockPhiActualCovarianceStep.gainProfile e z:=by
    unfold SourceClockPhiActualCovarianceStep.gainProfile forwardRatio
    rw [native_volume]
  have h:=native_multiplier_commute (SourceClockPhiActualCovarianceStep.gainProfile e) hb hi v
  change _*SourceClockPhiActualCovarianceStep.sourceGain e=
    SourceClockPhiActualCovarianceStep.sourceGain e*_ at h
  exact h
private theorem gain_weight_commute(t:ℝ)(ht:0<t)(ξ q e:ℝ):
    profileWeight t ht ξ q*SourceClockPhiActualCovarianceStep.sourceGain e=
      SourceClockPhiActualCovarianceStep.sourceGain e*profileWeight t ht ξ q:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp (q*noiseParameter t ξ z):ℂ) •
    ((SourceClockPhiActualCovarianceStep.gainProfile e z:ℂ) • f z)=
      (SourceClockPhiActualCovarianceStep.gainProfile e z:ℂ) •
        ((Real.exp (q*noiseParameter t ξ z):ℂ) • f z)
  exact smul_comm _ _ _
private theorem heat_factor(t:ℝ)(ht:0<t)(ξ:ℝ):
    sourceForwardCore t ht.le*heatNoise t ht ξ=sourceHeatCore t ht ξ:=rfl
private theorem complete_factor(t:ℝ)(ht:0<t)(ξ:ℝ):
    completeHeatCore t ht ξ=sourceForwardCore t ht.le*heatNoise t ht ξ*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=rfl
private theorem complete_native_return(t:ℝ)(ht:0<t)(ξ q:ℝ)(v:Ambient)
    (hN:GaussCoreDifferential.covariantMomentum v*heatNoise t ht ξ=
      heatNoise t ht ξ*profileWeight t ht ξ q*GaussCoreDifferential.covariantMomentum v):
    GaussCoreDifferential.covariantMomentum v*completeHeatCore t ht ξ=
      completeHeatCore t ht ξ*profileWeight t ht ξ q*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  have hJ:=LinearMap.congr_fun (actual_forward_native_momentum t ht.le v)
    (heatNoise t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))
  have hn:=LinearMap.congr_fun hN (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  have hg:=LinearMap.congr_fun (gain_native_commute (Real.sqrt t) v) f
  have hw:=LinearMap.congr_fun (gain_weight_commute t ht ξ q (Real.sqrt t))
    (GaussCoreDifferential.covariantMomentum v f)
  simp only [Module.End.mul_apply] at hJ hn hg hw
  change GaussCoreDifferential.covariantMomentum v
    (sourceForwardCore t ht.le (heatNoise t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)))=
    sourceForwardCore t ht.le (heatNoise t ht ξ (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
      (profileWeight t ht ξ q (GaussCoreDifferential.covariantMomentum v f))))
  rw [hJ,hn,hg,hw]

theorem actual_complete_scalar_momentum(t:ℝ)(ht:0<t)(ξ:ℝ)(v:Ambient)(hv:v.2=0):
    GaussCoreDifferential.covariantMomentum v*completeHeatCore t ht ξ=
      completeHeatCore t ht ξ*profileWeight t ht ξ 1*GaussCoreDifferential.covariantMomentum v:=
  complete_native_return t ht ξ 1 v (scalar_profile_return t ht ξ v hv)
theorem actual_complete_gauge_momentum(t:ℝ)(ht:0<t)(ξ:ℝ)(v:Ambient)(hv:v.1=0):
    GaussCoreDifferential.covariantMomentum v*completeHeatCore t ht ξ=
      completeHeatCore t ht ξ*profileWeight t ht ξ (-1)*GaussCoreDifferential.covariantMomentum v:=
  complete_native_return t ht ξ (-1) v (gauge_profile_return t ht ξ v hv)

private theorem coframe_weight_smooth(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*b (forwardPoint t x)) z.val:=by
  have h:ContDiffAt ℝ ∞ (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t)) z.val:=by
    have hr:ContDiffAt ℝ ∞ (forwardRatio ((Real.sqrt t)^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact hr.rpow_const_of_ne (forward_ratio_pos _ (sq_nonneg _) z).ne'
  exact (h.pow 2).mul (by
    simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))


private theorem native_form_weight_smooth(t:ℝ)(ht:0<t)(ξ q:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*
      b (forwardPoint t x)*Real.exp ((2*q)*noiseParameter t ξ x)) z.val:=
  (coframe_weight_smooth t ht b hb z).mul
    ((contDiffAt_const.mul (noise_parameter_smooth t ht ξ z)).exp)
private def nativeFormWeight(t:ℝ)(ht:0<t)(ξ q:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Op:=
  multiply (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*
    b (forwardPoint t x)*Real.exp ((2*q)*noiseParameter t ξ x)) (native_form_weight_smooth t ht ξ q b hb)
private theorem native_weighted_pair(t:ℝ)(ht:0<t)(ξ q:ℝ)(v w:Ambient)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y)
    (hv:GaussCoreDifferential.covariantMomentum v*completeHeatCore t ht ξ=
      completeHeatCore t ht ξ*profileWeight t ht ξ q*GaussCoreDifferential.covariantMomentum v)
    (hw:GaussCoreDifferential.covariantMomentum w*completeHeatCore t ht ξ=
      completeHeatCore t ht ξ*profileWeight t ht ξ q*GaussCoreDifferential.covariantMomentum w)
    (f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (sandwich v w b hb (completeHeatCore t ht ξ g))=
      sourcePair (GaussCoreDifferential.covariantMomentum v f)
        (nativeFormWeight t ht ξ q b hb (GaussCoreDifferential.covariantMomentum w g)):=by
  have hvf:=LinearMap.congr_fun hv f
  have hwg:=LinearMap.congr_fun hw g
  simp only [Module.End.mul_apply] at hvf hwg
  change sourcePair (completeHeatCore t ht ξ f)
    (GaussMomentumAdjoint.adjoint v (multiply b hb (GaussCoreDifferential.covariantMomentum w (completeHeatCore t ht ξ g))))=_
  rw [GaussNativeForm.adjoint_pair,hvf,hwg,SourceClockPhiHeatLocalNativeWork.actual_complete_coframe_multiplier_pair t ht ξ b hb hfirst]
  dsimp only [profileWeight]
  rw [←multiply_pair]
  apply congrArg (sourcePair (GaussCoreDifferential.covariantMomentum v f))
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (Real.exp (q*noiseParameter t ξ z):ℂ)*
    ((((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z):ℝ):ℂ)*
      ((Real.exp (q*noiseParameter t ξ z):ℂ)*GaussCoreDifferential.covariantMomentum w g z word))=
    (((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z)*Real.exp ((2*q)*noiseParameter t ξ z):ℝ):ℂ)*
      GaussCoreDifferential.covariantMomentum w g z word
  have he:Real.exp (q*noiseParameter t ξ z)*Real.exp (q*noiseParameter t ξ z)=
      Real.exp ((2*q)*noiseParameter t ξ z):=by rw [←Real.exp_add];congr 1;ring
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  have hec : (Real.exp (q*noiseParameter t ξ z):ℂ)*(Real.exp (q*noiseParameter t ξ z):ℂ)=
      (Real.exp ((2*q)*noiseParameter t ξ z):ℂ) := by exact_mod_cast he
  rw [←hec]
  ring

private theorem actual_complete_scalar_kinetic_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))=
      (1/2:ℂ)*(∑a:ScalarIndex,sourcePair (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)
        (nativeFormWeight t ht ξ 1 scalarWeight scalarWeight_smooth
          (GaussCoreDifferential.covariantMomentum (scalarDirection a) g))):=by
  have h(a:ScalarIndex):=native_weighted_pair t ht ξ 1 (scalarDirection a) (scalarDirection a)
    scalarWeight scalarWeight_smooth (fun x y h=>by
      dsimp only [scalarWeight,volume]
      rw [h])
    (actual_complete_scalar_momentum t ht ξ _ rfl) (actual_complete_scalar_momentum t ht ξ _ rfl) f g
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  congr 1
  exact Finset.sum_congr rfl (fun a _=>h a)

private theorem actual_complete_gauge_kinetic_pair(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))=
      (1/2:ℂ)*(∑a:LieIndex,∑i:Fin 3,∑j:Fin 3,
        sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
          (nativeFormWeight t ht ξ (-1) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
            (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) g))):=by
  have h(a:LieIndex)(i j:Fin 3):=native_weighted_pair t ht ξ (-1) (gaugeDirection i a) (gaugeDirection j a)
    (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j) (fun x y h=>by
      dsimp only [gaugeWeight,volume,inverseSpatial]
      rw [h])
    (actual_complete_gauge_momentum t ht ξ _ rfl) (actual_complete_gauge_momentum t ht ξ _ rfl) f g
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _=>h a i j)


private theorem ratio_smooth(t:ℝ)(_ht:0<t)(z:physicalChart):
    ContDiffAt ℝ ∞ (forwardRatio t) z.val:=
  (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
private theorem radial_noise_smooth(t:ℝ)(ht:0<t)(ξ p q:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(forwardRatio t x)^p*Real.exp (q*noiseParameter t ξ x)) z.val:=
  ((ratio_smooth t ht z).rpow_const_of_ne (forward_ratio_pos t ht.le z).ne').mul
    ((contDiffAt_const.mul (noise_parameter_smooth t ht ξ z)).exp)
def radialNoiseWeight(t:ℝ)(ht:0<t)(ξ p q:ℝ):Op:=
  multiply (fun z=>(forwardRatio t z)^p*Real.exp (q*noiseParameter t ξ z))
    (radial_noise_smooth t ht ξ p q)
private theorem radial_noise_native(t:ℝ)(ht:0<t)(ξ p q:ℝ)(v:Ambient):
    GaussCoreDifferential.covariantMomentum v*radialNoiseWeight t ht ξ p q=
      radialNoiseWeight t ht ξ p q*GaussCoreDifferential.covariantMomentum v:=by
  exact native_multiplier_commute _ _ (fun z w s=>by
    have hr:forwardRatio t (z+s • (0,w))=forwardRatio t z:=by
      unfold forwardRatio
      rw [native_volume]
    rw [hr,noise_parameter_native]) v
private theorem radial_noise_adjoint_pair(t:ℝ)(ht:0<t)(ξ p q:ℝ)(v:Ambient)(f h:QuantumTest):
    sourcePair (GaussCoreDifferential.covariantMomentum v f) (radialNoiseWeight t ht ξ p q h)=
      sourcePair f (radialNoiseWeight t ht ξ p q (GaussMomentumAdjoint.adjoint v h)):=by
  have hc:=LinearMap.congr_fun (radial_noise_native t ht ξ p q v) f
  simp only [Module.End.mul_apply] at hc
  dsimp only [radialNoiseWeight] at hc ⊢
  rw [multiply_pair,←hc,←GaussNativeForm.adjoint_pair,←multiply_pair]
private theorem actual_gain_square(t:ℝ)(ht:0<t)(z:physicalChart):
    (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val)^2=(forwardRatio t z.val)^(1/3:ℝ):=by
  have hr:=forward_ratio_pos t ht.le z
  unfold SourceClockPhiActualCovarianceStep.gainProfile
  rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 1
  norm_num
private theorem scalar_forward_price(t:ℝ)(ht:0<t)(z:physicalChart):
    scalarWeight (forwardPoint t z.val)=(forwardRatio t z.val)^(-1:ℝ)*scalarWeight z.val:=by
  rw [forwardPoint,scalar_weight_scale,inv_pow,cube_root_cube _ (forward_ratio_pos t ht.le z).le]
  simp only [Real.rpow_neg_one]
private theorem gauge_forward_price(t:ℝ)(ht:0<t)(z:physicalChart)(i j:Fin 3):
    gaugeWeight (forwardPoint t z.val) i j=(forwardRatio t z.val)^(1/3:ℝ)*gaugeWeight z.val i j:=by
  exact gauge_weight_scale _ (Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _).ne' _ i j
private theorem native_form_weight_factor(t:ℝ)(ht:0<t)(ξ q β:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hForward:∀z:physicalChart,b (forwardPoint t z.val)=(forwardRatio t z.val)^β*b z.val):
    nativeFormWeight t ht ξ q b hb=radialNoiseWeight t ht ξ (β+1/3) (2*q)*multiply b hb:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:=actual_gain_square t ht ⟨z,hz⟩
    have hbz:=hForward ⟨z,hz⟩
    apply PiLp.ext
    intro word
    change (((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z)*
      Real.exp ((2*q)*noiseParameter t ξ z):ℝ):ℂ)*f z word=
      (((forwardRatio t z)^(β+1/3)*Real.exp ((2*q)*noiseParameter t ξ z):ℝ):ℂ)*((b z:ℂ)*f z word)
    rw [hg,hbz,Real.rpow_add hr]
    push_cast
    ring
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • f z=(_:ℂ) • ((_ :ℂ) • f z)
    rw [hf,smul_zero,smul_zero,smul_zero]
private theorem scalar_form_factor(t:ℝ)(ht:0<t)(ξ:ℝ):
    nativeFormWeight t ht ξ 1 scalarWeight scalarWeight_smooth=
      radialNoiseWeight t ht ξ (-2/3) 2*multiply scalarWeight scalarWeight_smooth:=by
  convert native_form_weight_factor t ht ξ 1 (-1) scalarWeight scalarWeight_smooth
    (scalar_forward_price t ht) using 1; norm_num
private theorem gauge_form_factor(t:ℝ)(ht:0<t)(ξ:ℝ)(i j:Fin 3):
    nativeFormWeight t ht ξ (-1) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)=
      radialNoiseWeight t ht ξ (2/3) (-2)*multiply (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j):=by
  convert native_form_weight_factor t ht ξ (-1) (1/3) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
    (fun z=>gauge_forward_price t ht z i j) using 1; norm_num

theorem actual_complete_scalar_source(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (scalarKinetic (completeHeatCore t ht ξ g))=
      sourcePair f (radialNoiseWeight t ht ξ (-2/3) 2 (scalarKinetic g)):=by
  rw [actual_complete_scalar_kinetic_pair]
  simp_rw [scalar_form_factor,Module.End.mul_apply,radial_noise_adjoint_pair]
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
    sourcePair,inner_smul_right,inner_sum,sandwich,LinearMap.comp_apply]

theorem actual_complete_gauge_source(t:ℝ)(ht:0<t)(ξ:ℝ)(f g:QuantumTest):
    sourcePair (completeHeatCore t ht ξ f) (gaugeKinetic (completeHeatCore t ht ξ g))=
      sourcePair f (radialNoiseWeight t ht ξ (2/3) (-2) (gaugeKinetic g)):=by
  rw [actual_complete_gauge_kinetic_pair]
  simp_rw [gauge_form_factor,Module.End.mul_apply,radial_noise_adjoint_pair]
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
    sourcePair,inner_smul_right,inner_sum,sandwich,LinearMap.comp_apply]

end LowEnergy.SourceClockPhiHeatNativeHamiltonianWork
