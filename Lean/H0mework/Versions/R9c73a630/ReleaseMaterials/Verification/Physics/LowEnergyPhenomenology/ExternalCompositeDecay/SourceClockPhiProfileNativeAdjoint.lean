import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeForwardVariance
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore SourceClockPhiCoframeForwardPair
open SourceClockPhiProfileNativeReturn SourceClockPhiHeatNativeHamiltonianWork SourceClockPhiActualCovarianceStep
open ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource ClockPhiHeatCorrectedCovarianceSource
open scoped ContDiff Topology
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair embed
private theorem gainSmooth(e:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (gainProfile e) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact hr.rpow_const_of_ne (p:=(1/6:ℝ)) (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
private theorem inverseGainSmooth(e:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>Real.rpow (forwardRatio (e^2) x) (-1/6:ℝ)) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio (e^2)) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact hr.rpow_const_of_ne (p:=(-1/6:ℝ)) (forward_ratio_pos (e^2) (sq_nonneg _) z).ne'
private def inverseGain(e:ℝ):End:=multiply (fun x=>Real.rpow (forwardRatio (e^2) x) (-1/6:ℝ)) (inverseGainSmooth e)
private theorem gain_inverse(e:ℝ):sourceGain e*inverseGain e=1:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change ((Real.rpow (forwardRatio (e^2) z) (1/6:ℝ):ℝ):ℂ) • (((Real.rpow (forwardRatio (e^2) z) (-1/6:ℝ):ℝ):ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:=Real.rpow_add (forward_ratio_pos (e^2) (sq_nonneg _) ⟨z,hz⟩) (1/6:ℝ) (-1/6:ℝ)
    norm_num at hp
    have hprod:Real.rpow (forwardRatio (e^2) z) (1/6:ℝ)*Real.rpow (forwardRatio (e^2) z) (-1/6:ℝ)=1:=by
      convert hp.symm using 1; norm_num
    rw [hprod]
    simp
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem volume_native(z:SourceCoordinateSlice)(u:Slice)(a:ℝ):volume (z+a • (0,u))=volume z:=by
  simp only[volume,Prod.fst_add,Prod.smul_fst,smul_zero,add_zero]
private theorem gain_native(e:ℝ)(v:Ambient):covariantMomentum v*sourceGain e=sourceGain e*covariantMomentum v:=by
  have h:=native_multiplier_commute (gainProfile e) (gainSmooth e) (by
    intro z u a
    unfold gainProfile forwardRatio
    rw [volume_native]) v
  exact h
private theorem adjoint_real_commute(v:Ambient)(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (h:covariantMomentum v*multiply b hb=multiply b hb*covariantMomentum v):
    GaussMomentumAdjoint.adjoint v*multiply b hb=multiply b hb*GaussMomentumAdjoint.adjoint v:=by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (multiply b hb g))=
    sourcePair f (multiply b hb (GaussMomentumAdjoint.adjoint v g))
  rw [adjoint_pair,multiply_pair,multiply_pair,adjoint_pair]
  exact congrArg (fun q=>sourcePair q g) (LinearMap.congr_fun h f).symm
private theorem gain_adjoint(e:ℝ)(v:Ambient):
    GaussMomentumAdjoint.adjoint v*sourceGain e=sourceGain e*GaussMomentumAdjoint.adjoint v:=
  adjoint_real_commute v (gainProfile e) _ (gain_native e v)

private theorem profileWeightSmooth(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(k:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun x=>Real.exp (k*c x)) z.val:=
  (contDiffAt_const.mul (hc z)).exp

def nativeProfileWeight(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(k:ℝ):End:=
  multiply (fun x=>Real.exp (k*c x)) (profileWeightSmooth c hc k)
private theorem weight_native(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(k:ℝ)(v:Ambient):
    covariantMomentum v*nativeProfileWeight c hc k=nativeProfileWeight c hc k*covariantMomentum v:=by
  apply native_multiplier_commute
  intro z u a
  rw [hi (z+a • (0,u)) z (by simp)]
private theorem weight_gain(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(k e:ℝ):
    nativeProfileWeight c hc k*sourceGain e=sourceGain e*nativeProfileWeight c hc k:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (Real.exp (k*c z):ℂ) • ((gainProfile e z:ℂ) • f z)=
    (gainProfile e z:ℂ) • ((Real.exp (k*c z):ℂ) • f z)
  exact smul_comm _ _ _
private theorem pair_forward_cancel(t:ℝ)(ht:0≤t)(A B:End)
    (h:sourceForwardCore t ht*A=sourceForwardCore t ht*B):A=B:=by
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  rw [←actual_forward_core_pair t ht f (A g),←actual_forward_core_pair t ht f (B g)]
  exact congrArg (sourcePair (sourceForwardCore t ht f)) (LinearMap.congr_fun h g)

private theorem profile_momentum_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(k:ℝ)(v:Ambient)
    (hp:covariantMomentum v*completeProfile c hc hi 1 (by norm_num)=
      completeProfile c hc hi 1 (by norm_num)*nativeProfileWeight c hc k*covariantMomentum v):
    covariantMomentum v*profile c hc hi=profile c hc hi*nativeProfileWeight c hc k*covariantMomentum v:=by
  let J:=sourceForwardCore 1 (by norm_num)
  let N:=profile c hc hi
  let G:=sourceGain (Real.sqrt 1)
  let W:=nativeProfileWeight c hc k
  let P:=covariantMomentum v
  have hJ:P*J=J*P:=actual_forward_native_momentum _ _ _
  have hG:P*G=G*P:=gain_native _ _
  have hW:W*G=G*W:=weight_gain _ _ _ _
  have hGI:G*inverseGain (Real.sqrt 1)=1:=gain_inverse _
  change P*(J*N*G)=(J*N*G)*W*P at hp
  have he:J*(P*N)=J*(N*W*P):=by
    calc
      _=J*(P*N)*G*inverseGain (Real.sqrt 1):=by
        calc _=J*(P*N)*(G*inverseGain (Real.sqrt 1)):=by rw [hGI,mul_one]
             _=_:=by noncomm_ring
      _=P*(J*N*G)*inverseGain (Real.sqrt 1):=by
        linear_combination (norm:=noncomm_ring) -(hJ*N*G*inverseGain (Real.sqrt 1))
      _=(J*N*G)*W*P*inverseGain (Real.sqrt 1):=by rw [hp]
      _=J*(N*W*P)*(G*inverseGain (Real.sqrt 1)):=by
        calc
          _=J*N*(G*W)*P*inverseGain (Real.sqrt 1):=by noncomm_ring
          _=J*N*(W*G)*P*inverseGain (Real.sqrt 1):=by rw [hW]
          _=J*N*W*(G*P)*inverseGain (Real.sqrt 1):=by noncomm_ring
          _=J*N*W*(P*G)*inverseGain (Real.sqrt 1):=by rw [hG]
          _=_:=by noncomm_ring
      _=_:=by rw [hGI,mul_one]
  exact pair_forward_cancel 1 (by norm_num) _ _ he

private theorem profile_point(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(a:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    clockProfileAction c hc (fun _ _=>hi _ _ rfl) a f z=
      (Real.exp ((25/2:ℝ)*(a*c z)):ℂ) • f (combinedMap (a*c z) z):=rfl
private theorem profile_inverse(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(a:ℝ):
    clockProfileAction c hc (fun _ _=>hi _ _ rfl) (-a)*clockProfileAction c hc (fun _ _=>hi _ _ rfl) a=1:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only[Module.End.mul_apply,Module.End.one_apply,profile_point]
  rw [hi (combinedMap (-a*c z) z) z rfl,smul_smul,←Complex.ofReal_mul,←Real.exp_add]
  have h0:(25/2:ℝ)*(-a*c z)+(25/2:ℝ)*(a*c z)=0:=by ring
  rw [h0,Real.exp_zero,Complex.ofReal_one,one_smul]
  congr 1
  simp only[combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add]
  have h1:a*c z+-a*c z=0:=by ring
  have h2:-(a*c z)+-(-a*c z)=0:=by ring
  simp only[h1,h2,Real.exp_zero,one_smul,add_sub_cancel_right,Prod.eta]


private theorem profile_weight_commute(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(a k:ℝ):
    clockProfileAction c hc (fun _ _=>hi _ _ rfl) a*nativeProfileWeight c hc k=
      nativeProfileWeight c hc k*clockProfileAction c hc (fun _ _=>hi _ _ rfl) a:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only[Module.End.mul_apply,profile_point]
  change (Real.exp ((25/2:ℝ)*(a*c z)):ℂ) • ((Real.exp (k*c (combinedMap (a*c z) z)):ℂ) • f (combinedMap (a*c z) z))=
    (Real.exp (k*c z):ℂ) • ((Real.exp ((25/2:ℝ)*(a*c z)):ℂ) • f (combinedMap (a*c z) z))
  rw [hi (combinedMap (a*c z) z) z rfl]
  exact smul_comm _ _ _
private theorem profile_adjoint_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(k:ℝ)(v:Ambient)
    (hp:covariantMomentum v*profile c hc hi=profile c hc hi*nativeProfileWeight c hc k*covariantMomentum v):
    GaussMomentumAdjoint.adjoint v*profile c hc hi=
      profile c hc hi*nativeProfileWeight c hc k*GaussMomentumAdjoint.adjoint v:=by
  let N:=profile c hc hi
  let Ni:=clockProfileAction c hc (fun _ _=>hi _ _ rfl) (-1)
  let W:=nativeProfileWeight c hc k
  let P:=covariantMomentum v
  have hN:Ni*N=1:=profile_inverse c hc hi 1
  have hNi:N*Ni=1:=by simpa only[N,Ni,profile,neg_neg] using profile_inverse c hc hi (-1)
  have hW:Ni*W=W*Ni:=profile_weight_commute c hc hi (-1) k
  have hP:P*W=W*P:=weight_native c hc hi k v
  have hn:Ni*P=W*P*Ni:=by
    calc
      _=Ni*P*(N*Ni):=by rw [hNi,mul_one]
      _=Ni*(P*N)*Ni:=by noncomm_ring
      _=Ni*(N*W*P)*Ni:=by rw [hp]
      _=(Ni*N)*W*P*Ni:=by noncomm_ring
      _=_:=by rw [hN,one_mul]
  have hpair(f g:QuantumTest):sourcePair f (N g)=sourcePair (Ni f) g:=by
    have h:=clockProfileAction_pair c hc (fun _ _=>hi _ _ rfl) 1 (Ni f) g
    have hv:=LinearMap.congr_fun hNi f
    change N (Ni f)=f at hv
    change sourcePair (N (Ni f)) (N g)=sourcePair (Ni f) g at h
    rw [hv] at h
    exact h
  apply LinearMap.ext
  intro g
  apply SourceCoframeVolume.pair_ext
  intro f
  change sourcePair f (GaussMomentumAdjoint.adjoint v (N g))=
    sourcePair f (N (W (GaussMomentumAdjoint.adjoint v g)))
  calc
    _=sourcePair (P f) (N g):=adjoint_pair _ _ _
    _=sourcePair (Ni (P f)) g:=hpair _ _
    _=sourcePair (W (P (Ni f))) g:=congrArg (fun u=>sourcePair u g) (LinearMap.congr_fun hn f)
    _=sourcePair (P (W (Ni f))) g:=congrArg (fun u=>sourcePair u g) (LinearMap.congr_fun hP (Ni f)).symm
    _=sourcePair (W (Ni f)) (GaussMomentumAdjoint.adjoint v g):=(adjoint_pair _ _ _).symm
    _=sourcePair (Ni f) (W (GaussMomentumAdjoint.adjoint v g)):=(multiply_pair _ _ _ _).symm
    _=_:=(hpair _ _).symm
private theorem complete_adjoint_return(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(k:ℝ)(v:Ambient)
    (hp:covariantMomentum v*completeProfile c hc hi 1 (by norm_num)=
      completeProfile c hc hi 1 (by norm_num)*nativeProfileWeight c hc k*covariantMomentum v):
    GaussMomentumAdjoint.adjoint v*completeProfile c hc hi t ht=
      completeProfile c hc hi t ht*nativeProfileWeight c hc k*GaussMomentumAdjoint.adjoint v:=by
  have hN:=profile_adjoint_return c hc hi k v (profile_momentum_return c hc hi k v hp)
  have hJ:=actual_forward_native_adjoint t ht.le v
  have hG:=gain_adjoint (Real.sqrt t) v
  have hW:=weight_gain c hc k (Real.sqrt t)
  unfold completeProfile
  calc
    _=(GaussMomentumAdjoint.adjoint v*sourceForwardCore t ht.le)*profile c hc hi*sourceGain (Real.sqrt t):=by noncomm_ring
    _=sourceForwardCore t ht.le*(GaussMomentumAdjoint.adjoint v*profile c hc hi)*sourceGain (Real.sqrt t):=by rw [hJ];noncomm_ring
    _=sourceForwardCore t ht.le*(profile c hc hi*nativeProfileWeight c hc k*GaussMomentumAdjoint.adjoint v)*sourceGain (Real.sqrt t):=by rw [hN]
    _=sourceForwardCore t ht.le*profile c hc hi*nativeProfileWeight c hc k*(GaussMomentumAdjoint.adjoint v*sourceGain (Real.sqrt t)):=by noncomm_ring
    _=sourceForwardCore t ht.le*profile c hc hi*(nativeProfileWeight c hc k*sourceGain (Real.sqrt t))*GaussMomentumAdjoint.adjoint v:=by rw [hG];noncomm_ring
    _=_:=by rw [hW];noncomm_ring

/-- Both native legs, including the independent transpose, return through the genuine
variable profile and gain of the same complete clock. -/
theorem actual_complete_profile_scalar_adjoint(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(v:Ambient)(hv:v.2=0):
    GaussMomentumAdjoint.adjoint v*completeProfile c hc hi t ht=
      completeProfile c hc hi t ht*nativeProfileWeight c hc 1*GaussMomentumAdjoint.adjoint v:=by
  apply complete_adjoint_return
  exact actual_complete_profile_scalar_momentum c hc hi 1 (by norm_num) v hv

theorem actual_complete_profile_gauge_adjoint(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀x y:SourceCoordinateSlice,x.1=y.1→c x=c y)(t:ℝ)(ht:0<t)(v:Ambient)(hv:v.1=0):
    GaussMomentumAdjoint.adjoint v*completeProfile c hc hi t ht=
      completeProfile c hc hi t ht*nativeProfileWeight c hc (-1)*GaussMomentumAdjoint.adjoint v:=by
  apply complete_adjoint_return
  exact actual_complete_profile_gauge_momentum c hc hi 1 (by norm_num) v hv

private theorem corrected_first(t ξ η:ℝ):∀x y:SourceCoordinateSlice,x.1=y.1→
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rintro ⟨a,b⟩ ⟨d,e⟩ h
  cases h
  rfl

def correctedNativeWeight(t:ℝ)(ht:0<t)(ξ η k:ℝ):End:=
  nativeProfileWeight (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) k

/-- The actual corrected two-noise clock returns both native scalar legs through the same weight. -/
theorem actual_corrected_scalar_momentum_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(v:Ambient)(hv:v.2=0):
    covariantMomentum v*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η 1*covariantMomentum v ∧
    GaussMomentumAdjoint.adjoint v*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η 1*GaussMomentumAdjoint.adjoint v:=by
  constructor
  · have h : covariantMomentum v*completeProfile (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht=
        completeProfile (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht*
          nativeProfileWeight (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) 1*covariantMomentum v:=
        actual_complete_profile_scalar_momentum (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht v hv
    simpa only[correctedCompleteCore,correctedHeatCore,correctedProfileCore,completeProfile,profile,correctedNativeWeight] using h
  · simpa only[correctedCompleteCore,correctedHeatCore,correctedProfileCore,completeProfile,profile,correctedNativeWeight]
      using actual_complete_profile_scalar_adjoint (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η)
        (corrected_first t ξ η) t ht v hv

/-- The gauge legs retain their true inverse profile and independent transpose in the actual clock. -/
theorem actual_corrected_gauge_momentum_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(v:Ambient)(hv:v.1=0):
    covariantMomentum v*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η (-1)*covariantMomentum v ∧
    GaussMomentumAdjoint.adjoint v*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*correctedNativeWeight t ht ξ η (-1)*GaussMomentumAdjoint.adjoint v:=by
  constructor
  · have h : covariantMomentum v*completeProfile (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht=
        completeProfile (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht*
          nativeProfileWeight (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (-1)*covariantMomentum v:=
        actual_complete_profile_gauge_momentum (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (corrected_first t ξ η) t ht v hv
    simpa only[correctedCompleteCore,correctedHeatCore,correctedProfileCore,completeProfile,profile,correctedNativeWeight] using h
  · simpa only[correctedCompleteCore,correctedHeatCore,correctedProfileCore,completeProfile,profile,correctedNativeWeight]
      using actual_complete_profile_gauge_adjoint (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η)
        (corrected_first t ξ η) t ht v hv
end LowEnergy.FirstCurrentWholeVariance
