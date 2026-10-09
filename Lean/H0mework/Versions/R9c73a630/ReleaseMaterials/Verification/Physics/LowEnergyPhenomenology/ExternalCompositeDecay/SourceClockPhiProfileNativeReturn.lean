import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeHamiltonianWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileLocalNativeReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiProfileNativeReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussLiveMomentum GaussFockWeights SourceCoframeVolume SourcePhysicalKineticSquare
open SourceClockPhiCoframeForwardCore SourceKineticScale ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource
open SourceClockPhiHeatNativeHamiltonianWork SourceScalarAffineScaleTransport
open scoped ContDiff Topology
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private theorem c_invariant(c:SourceCoordinateSlice→ℝ)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(u:ℝ)(z:SourceCoordinateSlice):c (combinedMap u z)=c z:=hfirst _ _ rfl
def profile(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y):Op:=clockProfileAction c hc (c_invariant c hfirst) 1
private theorem profile_point(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:SourceCoordinateSlice):
    profile c hc hfirst f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul]
private theorem c_native(c:SourceCoordinateSlice→ℝ)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(s:ℝ)(z:SourceCoordinateSlice)(v:Slice):c (z+s • (0,v))=c z:=
  hfirst _ _ (by simp only [Prod.fst_add,Prod.smul_fst,smul_zero,add_zero])
private def profileNative(a:ℝ)(v:Slice):SourceCoordinateSlice:=(0,Real.exp a • v.1,Real.exp (-a) • v.2)
private theorem map_native_line(c:SourceCoordinateSlice→ℝ)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(s:ℝ)(z:SourceCoordinateSlice)(v:Slice):
    combinedMap (c (z+s • (0,v))) (z+s • (0,v))=
      combinedMap (c z) z+s • profileNative (c z) v:=by
  rw [c_native c hfirst]
  simp only [combinedMap_apply,profileNative]
  apply Prod.ext
  · simp
  apply Prod.ext
  · change Real.exp (c z) • ((z.2.1+s • v.1)+vacuumSlice)-vacuumSlice=
      (Real.exp (c z) • (z.2.1+vacuumSlice)-vacuumSlice)+s • (Real.exp (c z) • v.1)
    module
  · change Real.exp (-(c z)) • (z.2.2+s • v.2)=
      Real.exp (-(c z)) • z.2.2+s • (Real.exp (-(c z)) • v.2)
    module
private theorem profile_native_line(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(s:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice)(v:Slice):
    profile c hc hfirst f (z+s • (0,v))=(Real.exp ((25/2:ℝ)*c z):ℂ) •
      f (combinedMap (c z) z+s • profileNative (c z) v):=by
  rw [profile_point, map_native_line c hfirst,c_native c hfirst]
private theorem profile_native_derivative(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(f:QuantumTest)(z:SourceCoordinateSlice)(v:Slice):
    fderiv ℝ (profile c hc hfirst f) z (0,v)=(Real.exp ((25/2:ℝ)*c z):ℂ) •
      fderiv ℝ f (combinedMap (c z) z) (profileNative (c z) v):=by
  have hz:HasDerivAt (fun s:ℝ=>z+s • (0,v)) (0,v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (0,v)).const_add z
  have hx:HasDerivAt (fun s:ℝ=>combinedMap (c z) z+s • profileNative (c z) v)
      (profileNative (c z) v) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (profileNative (c z) v)).const_add (combinedMap (c z) z)
  have hl:=(((profile c hc hfirst f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=z)).comp_hasDerivAt_of_eq
    (0:ℝ) hz (by simp)
  have hr:=(((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x:=combinedMap (c z) z)).comp_hasDerivAt_of_eq
    (0:ℝ) hx (by simp)).const_smul (Real.exp ((25/2:ℝ)*c z):ℂ)
  have he:(fun s:ℝ=>profile c hc hfirst f (z+s • (0,v)))=
      fun s:ℝ=>(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z+s • profileNative (c z) v):=
    funext (fun s=>profile_native_line c hc hfirst s f z v)
  dsimp only [Function.comp_def] at hl hr
  rw [he] at hl
  exact hl.unique hr
private theorem native_intertwine(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(k:ℝ)(z:physicalChart)(v:Ambient)
    (hd:profileNative (c z.val) (inverseL z.val v).2=k • direction v (combinedMap (c z.val) z.val))
    (hb:(inverseL z.val v).1=k • (inverseL (combinedMap (c z.val) z.val) v).1)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (profile c hc hfirst f) z.val=
      (k:ℂ) • profile c hc hfirst (GaussCoreDifferential.covariantMomentum v f) z.val:=by
  rw [covariantMomentum_apply,profile_native_derivative,hd,map_smul,hb]
  rw [profile_point c hc hfirst f z.val,profile_point c hc hfirst (GaussCoreDifferential.covariantMomentum v f) z.val,covariantMomentum_apply]
  unfold direction
  simp only [map_smul,smul_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  module
private theorem profile_scalar_direction(c:SourceCoordinateSlice→ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    profileNative (c z.val) (inverseL z.val v).2=
      Real.exp (c z.val) • direction v (combinedMap (c z.val) z.val):=by
  let a:=c z.val
  have he:Real.exp a*Real.exp (-2*a)=Real.exp (-a):=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp a • (inverseL z.val v).2.1,Real.exp (-a) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp a • (0,(inverseL (combinedMap a z.val) v).2)
  rw [inverse_scalar_finite a z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem profile_scalar_inverse(c:SourceCoordinateSlice→ℝ)(z:physicalChart)(v:Ambient)(hv:v.2=0):
    (inverseL z.val v).1=Real.exp (c z.val) •
      (inverseL (combinedMap (c z.val) z.val) v).1:=by
  rw [inverse_scalar_finite _ z v hv]
  simp only [smul_smul,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
private theorem profile_gauge_direction(c:SourceCoordinateSlice→ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    profileNative (c z.val) (inverseL z.val v).2=
      Real.exp (-(c z.val)) • direction v (combinedMap (c z.val) z.val):=by
  let a:=c z.val
  have he:Real.exp (-a)*Real.exp (2*a)=Real.exp a:=by
    rw [←Real.exp_add];congr 1;ring
  change (0,Real.exp a • (inverseL z.val v).2.1,Real.exp (-a) • (inverseL z.val v).2.2)=_
  unfold direction
  change _=Real.exp (-a) • (0,(inverseL (combinedMap a z.val) v).2)
  rw [inverse_gauge_finite a z v hv]
  simp only [Prod.smul_mk,smul_zero,smul_smul,he]
private theorem profile_gauge_inverse(c:SourceCoordinateSlice→ℝ)(z:physicalChart)(v:Ambient)(hv:v.1=0):
    (inverseL z.val v).1=Real.exp (-(c z.val)) •
      (inverseL (combinedMap (c z.val) z.val) v).1:=by
  rw [inverse_gauge_finite _ z v hv]
  simp only [smul_smul,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_smul]

private theorem actual_profile_scalar_momentum(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(z:physicalChart)(v:Ambient)(hv:v.2=0)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (profile c hc hfirst f) z.val=
      (Real.exp (c z.val):ℂ) • profile c hc hfirst (GaussCoreDifferential.covariantMomentum v f) z.val:=
  native_intertwine c hc hfirst _ z v (profile_scalar_direction c z v hv) (profile_scalar_inverse c z v hv) f
private theorem actual_profile_gauge_momentum(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(z:physicalChart)(v:Ambient)(hv:v.1=0)(f:QuantumTest):
    GaussCoreDifferential.covariantMomentum v (profile c hc hfirst f) z.val=
      (Real.exp (-(c z.val)):ℂ) • profile c hc hfirst (GaussCoreDifferential.covariantMomentum v f) z.val:=
  native_intertwine c hc hfirst _ z v (profile_gauge_direction c z v hv) (profile_gauge_inverse c z v hv) f




private def exponentialWeight(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q:ℝ):Op:=multiply (fun z=>Real.exp (q*c z))
  (fun z=>(contDiffAt_const.mul (hc z)).exp)
private theorem profile_invariant(c:SourceCoordinateSlice→ℝ)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(z:SourceCoordinateSlice)(u:ℝ):c (combinedMap u z)=c z:=c_invariant c hfirst u z
private theorem scalar_profile_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(v:Ambient)(hv:v.2=0):
    GaussCoreDifferential.covariantMomentum v*profile c hc hfirst=
      profile c hc hfirst*exponentialWeight c hc 1*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreDifferential.covariantMomentum v (profile c hc hfirst f) z=
    profile c hc hfirst (exponentialWeight c hc 1 (GaussCoreDifferential.covariantMomentum v f)) z
  by_cases hz:z∈physicalChart
  · rw [actual_profile_scalar_momentum c hc hfirst ⟨z,hz⟩ v hv f,profile_point,profile_point]
    change (Real.exp (c z):ℂ) •
      ((Real.exp ((25/2:ℝ)*c z):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (c z) z))=
      (Real.exp ((25/2:ℝ)*c z):ℂ) •
        ((Real.exp (1*c (combinedMap (c z) z)):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (c z) z))
    rw [profile_invariant c hfirst,one_mul]
    exact smul_comm _ _ _
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]
private theorem gauge_profile_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(v:Ambient)(hv:v.1=0):
    GaussCoreDifferential.covariantMomentum v*profile c hc hfirst=
      profile c hc hfirst*exponentialWeight c hc (-1)*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreDifferential.covariantMomentum v (profile c hc hfirst f) z=
    profile c hc hfirst (exponentialWeight c hc (-1) (GaussCoreDifferential.covariantMomentum v f)) z
  by_cases hz:z∈physicalChart
  · rw [actual_profile_gauge_momentum c hc hfirst ⟨z,hz⟩ v hv f,profile_point,profile_point]
    change (Real.exp (-(c z)):ℂ) •
      ((Real.exp ((25/2:ℝ)*c z):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (c z) z))=
      (Real.exp ((25/2:ℝ)*c z):ℂ) •
        ((Real.exp (-1*c (combinedMap (c z) z)):ℂ) • GaussCoreDifferential.covariantMomentum v f (combinedMap (c z) z))
    rw [profile_invariant c hfirst,neg_one_mul]
    exact smul_comm _ _ _
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]



private theorem volume_native(s:ℝ)(z:SourceCoordinateSlice)(v:Slice):volume (z+s • (0,v))=volume z:=by
  simp only [volume,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
private theorem gain_native_commute(e:ℝ)(v:Ambient):
    GaussCoreDifferential.covariantMomentum v*SourceClockPhiActualCovarianceStep.sourceGain e=
      SourceClockPhiActualCovarianceStep.sourceGain e*GaussCoreDifferential.covariantMomentum v:=by
  have hb(z:physicalChart):ContDiffAt ℝ ∞ (SourceClockPhiActualCovarianceStep.gainProfile e) z.val:=by
    have hr:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact hr.rpow_const_of_ne (p:=(1/6:ℝ)) (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
  have hi(z:SourceCoordinateSlice)(w:Slice)(r:ℝ):
      SourceClockPhiActualCovarianceStep.gainProfile e (z+r • (0,w))=SourceClockPhiActualCovarianceStep.gainProfile e z:=by
    unfold SourceClockPhiActualCovarianceStep.gainProfile forwardRatio
    rw [volume_native]
  have h:=native_multiplier_commute (SourceClockPhiActualCovarianceStep.gainProfile e) hb hi v
  change _*SourceClockPhiActualCovarianceStep.sourceGain e=SourceClockPhiActualCovarianceStep.sourceGain e*_ at h
  exact h
private theorem gain_weight_commute(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q e:ℝ):
    exponentialWeight c hc q*SourceClockPhiActualCovarianceStep.sourceGain e=
      SourceClockPhiActualCovarianceStep.sourceGain e*exponentialWeight c hc q:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (_:ℂ) • ((_ :ℂ) • f z)=(_:ℂ) • ((_ :ℂ) • f z)
  exact smul_comm _ _ _
def completeProfile(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t):Op:=
  sourceForwardCore t ht.le*profile c hc hfirst*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
private theorem complete_native_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(q:ℝ)(v:Ambient)
    (hN:GaussCoreDifferential.covariantMomentum v*profile c hc hfirst=
      profile c hc hfirst*exponentialWeight c hc q*GaussCoreDifferential.covariantMomentum v):
    GaussCoreDifferential.covariantMomentum v*completeProfile c hc hfirst t ht=
      completeProfile c hc hfirst t ht*exponentialWeight c hc q*GaussCoreDifferential.covariantMomentum v:=by
  apply LinearMap.ext
  intro f
  have hJ:=LinearMap.congr_fun (actual_forward_native_momentum t ht.le v)
    (profile c hc hfirst (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))
  have hn:=LinearMap.congr_fun hN (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  have hg:=LinearMap.congr_fun (gain_native_commute (Real.sqrt t) v) f
  have hw:=LinearMap.congr_fun (gain_weight_commute c hc q (Real.sqrt t))
    (GaussCoreDifferential.covariantMomentum v f)
  simp only [Module.End.mul_apply] at hJ hn hg hw
  change GaussCoreDifferential.covariantMomentum v
    (sourceForwardCore t ht.le (profile c hc hfirst (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)))=
    sourceForwardCore t ht.le (profile c hc hfirst (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
      (exponentialWeight c hc q (GaussCoreDifferential.covariantMomentum v f))))
  rw [hJ,hn,hg,hw]
theorem actual_complete_profile_scalar_momentum(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(v:Ambient)(hv:v.2=0):
    GaussCoreDifferential.covariantMomentum v*completeProfile c hc hfirst t ht=
      completeProfile c hc hfirst t ht*exponentialWeight c hc 1*GaussCoreDifferential.covariantMomentum v:=
  complete_native_return c hc hfirst t ht 1 v (scalar_profile_return c hc hfirst v hv)
theorem actual_complete_profile_gauge_momentum(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(v:Ambient)(hv:v.1=0):
    GaussCoreDifferential.covariantMomentum v*completeProfile c hc hfirst t ht=
      completeProfile c hc hfirst t ht*exponentialWeight c hc (-1)*GaussCoreDifferential.covariantMomentum v:=
  complete_native_return c hc hfirst t ht (-1) v (gauge_profile_return c hc hfirst v hv)

private theorem forward_weight_smooth(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*b (forwardPoint t x)) z.val:=by
  have hg:ContDiffAt ℝ ∞ (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t)) z.val:=by
    have hr:ContDiffAt ℝ ∞ (forwardRatio ((Real.sqrt t)^2)) z.val:=
      (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
    exact hr.rpow_const_of_ne (forward_ratio_pos _ (sq_nonneg _) z).ne'
  exact (hg.pow 2).mul (by
    simpa only [Function.comp_def] using! (hb ⟨_,forward_chart t ht.le z⟩).comp z.val (forward_smooth t ht.le z))
private theorem form_weight_smooth(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*
      b (forwardPoint t x)*Real.exp ((2*q)*c x)) z.val:=
  (forward_weight_smooth t ht b hb z).mul ((contDiffAt_const.mul (hc z)).exp)
private def formWeight(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Op:=
  multiply (fun x=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) x)^2*
    b (forwardPoint t x)*Real.exp ((2*q)*c x)) (form_weight_smooth t ht c hc q b hb)
private theorem weighted_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (q:ℝ)(v w:Ambient)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(hbfirst:∀x y:SourceCoordinateSlice,x.1=y.1→b x=b y)
    (hv:GaussCoreDifferential.covariantMomentum v*completeProfile c hc hfirst t ht=
      completeProfile c hc hfirst t ht*exponentialWeight c hc q*GaussCoreDifferential.covariantMomentum v)
    (hw:GaussCoreDifferential.covariantMomentum w*completeProfile c hc hfirst t ht=
      completeProfile c hc hfirst t ht*exponentialWeight c hc q*GaussCoreDifferential.covariantMomentum w)
    (f g:QuantumTest):
    sourcePair (completeProfile c hc hfirst t ht f) (sandwich v w b hb (completeProfile c hc hfirst t ht g))=
      sourcePair (GaussCoreDifferential.covariantMomentum v f)
        (formWeight t ht c hc q b hb (GaussCoreDifferential.covariantMomentum w g)):=by
  have hvf:=LinearMap.congr_fun hv f
  have hwg:=LinearMap.congr_fun hw g
  simp only [Module.End.mul_apply] at hvf hwg
  change sourcePair (completeProfile c hc hfirst t ht f)
    (GaussMomentumAdjoint.adjoint v (multiply b hb (GaussCoreDifferential.covariantMomentum w (completeProfile c hc hfirst t ht g))))=_
  rw [GaussNativeForm.adjoint_pair,hvf,hwg]
  change sourcePair (SourceClockPhiProfileCoframeReturn.profileCompleteCore t ht c hc (c_invariant c hfirst)
      (exponentialWeight c hc q (GaussCoreDifferential.covariantMomentum v f)))
    (multiply b hb (SourceClockPhiProfileCoframeReturn.profileCompleteCore t ht c hc (c_invariant c hfirst)
      (exponentialWeight c hc q (GaussCoreDifferential.covariantMomentum w g))))=_
  rw [SourceClockPhiProfileLocalNativeReturn.actual_profile_coframe_multiplier_pair t ht c hc hfirst b hb hbfirst]
  dsimp only [exponentialWeight]
  rw [←multiply_pair]
  apply congrArg (sourcePair (GaussCoreDifferential.covariantMomentum v f))
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change (Real.exp (q*c z):ℂ)*
    ((((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z):ℝ):ℂ)*
      ((Real.exp (q*c z):ℂ)*GaussCoreDifferential.covariantMomentum w g z word))=
    (((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z)*Real.exp ((2*q)*c z):ℝ):ℂ)*
      GaussCoreDifferential.covariantMomentum w g z word
  have he:Real.exp (q*c z)*Real.exp (q*c z)=Real.exp ((2*q)*c z):=by
    rw [←Real.exp_add];congr 1;ring
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  have hec:(Real.exp (q*c z):ℂ)*(Real.exp (q*c z):ℂ)=(Real.exp ((2*q)*c z):ℂ):=by exact_mod_cast he
  rw [←hec]
  ring
private theorem scalar_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (f g:QuantumTest):
    sourcePair (completeProfile c hc hfirst t ht f) (scalarKinetic (completeProfile c hc hfirst t ht g))=
      (1/2:ℂ)*(∑a:ScalarIndex,sourcePair (GaussCoreDifferential.covariantMomentum (scalarDirection a) f)
        (formWeight t ht c hc 1 scalarWeight scalarWeight_smooth
          (GaussCoreDifferential.covariantMomentum (scalarDirection a) g))):=by
  have h(a:ScalarIndex):=weighted_pair t ht c hc hfirst 1 (scalarDirection a) (scalarDirection a)
    scalarWeight scalarWeight_smooth (fun x y h=>by dsimp only [scalarWeight,volume];rw [h])
    (actual_complete_profile_scalar_momentum c hc hfirst t ht _ rfl)
    (actual_complete_profile_scalar_momentum c hc hfirst t ht _ rfl) f g
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  congr 1
  exact Finset.sum_congr rfl (fun a _=>h a)
private theorem gauge_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (f g:QuantumTest):
    sourcePair (completeProfile c hc hfirst t ht f) (gaugeKinetic (completeProfile c hc hfirst t ht g))=
      (1/2:ℂ)*(∑a:LieIndex,∑i:Fin 3,∑j:Fin 3,
        sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
          (formWeight t ht c hc (-1) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
            (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) g))):=by
  have h(a:LieIndex)(i j:Fin 3):=weighted_pair t ht c hc hfirst (-1) (gaugeDirection i a) (gaugeDirection j a)
    (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
    (fun x y h=>by dsimp only [gaugeWeight,volume,inverseSpatial];rw [h])
    (actual_complete_profile_gauge_momentum c hc hfirst t ht _ rfl)
    (actual_complete_profile_gauge_momentum c hc hfirst t ht _ rfl) f g
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_congr rfl (fun j _=>h a i j)
private theorem profile_weight_native(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (p q:ℝ)(v:Ambient):
    GaussCoreDifferential.covariantMomentum v*SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc p q=
      SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc p q*GaussCoreDifferential.covariantMomentum v:=by
  apply native_multiplier_commute
  intro z w s
  have hr:forwardRatio t (z+s • (0,w))=forwardRatio t z:=by
    unfold forwardRatio
    rw [volume_native]
  have hc0:c (z+s • (0,w))=c z:=c_native c hfirst s z w
  change (forwardRatio t (z+s • (0,w)))^p*Real.exp (q*c (z+s • (0,w)))=_
  rw [hr,hc0]
  rfl
private theorem weight_adjoint_pair(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (p q:ℝ)(v:Ambient)(f h:QuantumTest):
    sourcePair (GaussCoreDifferential.covariantMomentum v f)
        (SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc p q h)=
      sourcePair f (SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc p q (GaussMomentumAdjoint.adjoint v h)):=by
  have h0:=LinearMap.congr_fun (profile_weight_native t ht c hc hfirst p q v) f
  simp only [Module.End.mul_apply] at h0
  dsimp only [SourceClockPhiProfileLocalNativeReturn.actualProfileWeight] at h0 ⊢
  rw [multiply_pair,←h0,←GaussNativeForm.adjoint_pair,←multiply_pair]
private theorem gain_square(t:ℝ)(ht:0<t)(z:physicalChart):
    (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val)^2=(forwardRatio t z.val)^(1/3:ℝ):=by
  have hr:=forward_ratio_pos t ht.le z
  unfold SourceClockPhiActualCovarianceStep.gainProfile
  rw [Real.sq_sqrt ht.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 1
  norm_num
private theorem scalar_forward(t:ℝ)(ht:0<t)(z:physicalChart):
    scalarWeight (forwardPoint t z.val)=(forwardRatio t z.val)^(-1:ℝ)*scalarWeight z.val:=by
  rw [forwardPoint,scalar_weight_scale,inv_pow,cube_root_cube _ (forward_ratio_pos t ht.le z).le]
  simp only [Real.rpow_neg_one]
private theorem gauge_forward(t:ℝ)(ht:0<t)(z:physicalChart)(i j:Fin 3):
    gaugeWeight (forwardPoint t z.val) i j=(forwardRatio t z.val)^(1/3:ℝ)*gaugeWeight z.val i j:=
  gauge_weight_scale _ (Real.rpow_pos_of_pos (forward_ratio_pos t ht.le z) _).ne' _ i j
private theorem form_factor(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(q β:ℝ)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hF:∀z:physicalChart,b (forwardPoint t z.val)=(forwardRatio t z.val)^β*b z.val):
    formWeight t ht c hc q b hb=
      SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc (β+1/3) (2*q)*multiply b hb:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos t ht.le ⟨z,hz⟩
    have hg:=gain_square t ht ⟨z,hz⟩
    have hb0:=hF ⟨z,hz⟩
    apply PiLp.ext
    intro word
    change (((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z)^2*b (forwardPoint t z)*Real.exp ((2*q)*c z):ℝ):ℂ)*f z word=
      (((forwardRatio t z)^(β+1/3)*Real.exp ((2*q)*c z):ℝ):ℂ)*((b z:ℂ)*f z word)
    rw [hg,hb0,Real.rpow_add hr]
    push_cast
    ring
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • f z=(_:ℂ) • ((_ :ℂ) • f z)
    rw [hf,smul_zero,smul_zero,smul_zero]
private theorem scalar_factor(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val):
    formWeight t ht c hc 1 scalarWeight scalarWeight_smooth=
      SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc (-2/3) 2*multiply scalarWeight scalarWeight_smooth:=by
  convert form_factor t ht c hc 1 (-1) scalarWeight scalarWeight_smooth (scalar_forward t ht) using 1; norm_num
private theorem gauge_factor(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(i j:Fin 3):
    formWeight t ht c hc (-1) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)=
      SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc (2/3) (-2)*multiply (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j):=by
  convert form_factor t ht c hc (-1) (1/3) (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)
    (fun z=>gauge_forward t ht z i j) using 1; norm_num

theorem actual_complete_profile_scalar_source(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (f g:QuantumTest):
    sourcePair (completeProfile c hc hfirst t ht f) (scalarKinetic (completeProfile c hc hfirst t ht g))=
      sourcePair f (SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc (-2/3) 2 (scalarKinetic g)):=by
  rw [scalar_pair]
  simp_rw [scalar_factor t ht c hc,Module.End.mul_apply,weight_adjoint_pair t ht c hc hfirst]
  simp only [scalarKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
    sourcePair,inner_smul_right,inner_sum,sandwich,LinearMap.comp_apply]
theorem actual_complete_profile_gauge_source(t:ℝ)(ht:0<t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hfirst:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)
    (f g:QuantumTest):
    sourcePair (completeProfile c hc hfirst t ht f) (gaugeKinetic (completeProfile c hc hfirst t ht g))=
      sourcePair f (SourceClockPhiProfileLocalNativeReturn.actualProfileWeight t ht c hc (2/3) (-2) (gaugeKinetic g)):=by
  rw [gauge_pair]
  simp_rw [gauge_factor t ht c hc,Module.End.mul_apply,weight_adjoint_pair t ht c hc hfirst]
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,
    sourcePair,inner_smul_right,inner_sum,sandwich,LinearMap.comp_apply]

end LowEnergy.SourceClockPhiProfileNativeReturn
