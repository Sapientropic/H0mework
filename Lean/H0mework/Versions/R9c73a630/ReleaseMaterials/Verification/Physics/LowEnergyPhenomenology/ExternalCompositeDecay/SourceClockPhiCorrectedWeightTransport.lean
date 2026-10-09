import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardGeneratorTransport
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0RealPrimitives
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCorrectedWeightTransport
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent GaussLiveMomentum
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn
open SourceClockPhiForwardGeneratorTransport SourceClockPhiCombinedScalePressure
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource ClockPhiMatchedNoiseCore
open SourceScalarVirialBulk SourceScalarGaugeScale SourceScalarDoubleCurrent
open SourceClockPhiOriginalGaussianH0RealPrimitives
open scoped ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private theorem multiplier_commute(A:End)(B:SourceCoordinateSlice→FockFiber→L[ℂ]FockFiber)
    (law:∀f z,A f z=B z (f z))(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):Commute A (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change A (multiply b hb f) z=(multiply b hb (A f)) z
  rw [law]
  simp only [multiply_apply]
  rw [law]
  exact map_smul (B z) (b z:ℂ) (f z)
private theorem profile_coframe_multiplier(t:ℝ)(ht:0<t)(ξ η:ℝ)
    (b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀u z,b (combinedMap u z)=b z):
    Commute (correctedProfileCore t ht ξ η) (multiply b hb):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change correctedProfileCore t ht ξ η (multiply b hb f) z=
    multiply b hb (correctedProfileCore t ht ξ η f) z
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
    ((b (combinedMap (1*correctedCoefficient t ξ η z) z):ℂ) • f (combinedMap (1*correctedCoefficient t ξ η z) z))=
    (b z:ℂ) • ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
      f (combinedMap (1*correctedCoefficient t ξ η z) z))
  simp only [one_mul]
  rw [hi]
  exact smul_comm _ _ _
private theorem gain_combined(ε:ℝ):Commute combinedGenerator (SourceClockPhiActualCovarianceStep.sourceGain ε):=by
  let G:=SourceClockPhiActualCovarianceStep.sourceGain ε
  let B:=fun z:SourceCoordinateSlice=>(SourceClockPhiActualCovarianceStep.gainProfile ε z:ℂ) •
    ContinuousLinearMap.id ℂ FockFiber
  have hp:=phi_invariant_local G B (fun _ _=>rfl) (fun _ _=>rfl)
  have hg:=gauge_invariant_local G B (fun _ _=>rfl) (fun _ _=>rfl)
  have h:SourceScalarDoubleCurrent.bracket combinedGenerator G=deltaPhi G-deltaGauge G:=by
    unfold combinedGenerator SourceScalarDoubleCurrent.bracket
    rw [sub_mul,mul_sub]
    have hphi:=SourceScalarAffineScaleTransport.generator_commutator G
    have hgauge:=SourceGaugeScaleTransport.generator_commutator G
    linear_combination (norm:=module) hphi-hgauge
  exact sub_eq_zero.mp (show SourceScalarDoubleCurrent.bracket combinedGenerator G=0 by rw [h,hp,hg,sub_self])

theorem actual_corrected_complete_generator_commute(t:ℝ)(ht:0<t)(ξ η:ℝ):
    Commute combinedGenerator (correctedCompleteCore t ht ξ η):=by
  have hp:Commute combinedGenerator (correctedProfileCore t ht ξ η):=clockProfileAction_D _ _ _ _
  exact ((actual_forward_generator_commute t ht.le).mul_right hp).mul_right (gain_combined _)

theorem actual_corrected_complete_inverse_volume(t:ℝ)(ht:0<t)(ξ η:ℝ):
    inverseVolumeAction*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*forwardUAction t ht.le:=by
  have hP:=profile_coframe_multiplier t ht ξ η (forwardU t) (forwardU_smooth t ht.le) (fun _ _=>rfl)
  have hG:Commute (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)) (forwardUAction t ht.le):=by
    exact multiplier_commute _
      (fun z=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun _ _=>rfl) _ _
  change Commute (correctedProfileCore t ht ξ η) (forwardUAction t ht.le) at hP
  unfold correctedCompleteCore correctedHeatCore
  calc
    _=(inverseVolumeAction*sourceForwardCore t ht.le)*
      (correctedProfileCore t ht ξ η*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by simp only [mul_assoc]
    _=(sourceForwardCore t ht.le*forwardUAction t ht.le)*
      (correctedProfileCore t ht ξ η*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by rw [actual_forward_U_return]
    _=sourceForwardCore t ht.le*((forwardUAction t ht.le*correctedProfileCore t ht ξ η)*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by simp only [mul_assoc]
    _=sourceForwardCore t ht.le*((correctedProfileCore t ht ξ η*forwardUAction t ht.le)*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by rw [hP.eq.symm]
    _=sourceForwardCore t ht.le*(correctedProfileCore t ht ξ η*
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*forwardUAction t ht.le)):=by
        rw [mul_assoc,hG.eq.symm]
    _=_:=by simp only [mul_assoc]

theorem actual_corrected_complete_B3_input_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    SourceClockPhiMatchedDiffusionSource.driftClock (correctedCompleteCore t ht ξ η f)=
      correctedHeatCore t ht ξ η
        (SourceClockPhiMatchedDiffusionSource.driftClock (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)-
          noiseAction t ht ξ η (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (combinedGenerator f))):=by
  have hG:=LinearMap.congr_fun (gain_combined (Real.sqrt t)).eq f
  have hB:=actual_corrected_heat_B3_return t ht ξ η (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  change SourceClockPhiMatchedDiffusionSource.driftClock (correctedCompleteCore t ht ξ η f)=_ at hB
  simp only [Module.End.mul_apply] at hG
  rw [hG] at hB
  exact hB

private theorem forward_coframe_smooth(t:ℝ)(ht:0<t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (fun w=>b (forwardPoint t w)) z.val:=
  ContDiffAt.comp (f:=forwardPoint t) z.val (hb ⟨_,forward_chart t ht.le z⟩) (forward_smooth t ht.le z)

theorem actual_corrected_complete_coframe_multiplier(t:ℝ)(ht:0<t)(ξ η:ℝ)
    (b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hfirst:∀z w:SourceCoordinateSlice,z.1=w.1→b z=b w):
    multiply b hb*correctedCompleteCore t ht ξ η=
      correctedCompleteCore t ht ξ η*
        multiply (fun z=>b (forwardPoint t z)) (forward_coframe_smooth t ht b hb):=by
  let c:SourceCoordinateSlice→ℝ:=fun z=>b (forwardPoint t z)
  let hc:=forward_coframe_smooth t ht b hb
  have hP:=profile_coframe_multiplier t ht ξ η c hc (fun _ z=>hfirst _ _ rfl)
  have hG:Commute (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)) (multiply c hc):=
    multiplier_commute _
      (fun z=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun _ _=>rfl) _ _
  have hF:=actual_forward_multiplier_transport t ht.le b hb
  change multiply b hb*sourceForwardCore t ht.le=sourceForwardCore t ht.le*multiply c hc at hF
  unfold correctedCompleteCore correctedHeatCore
  calc
    _=(multiply b hb*sourceForwardCore t ht.le)*
      (correctedProfileCore t ht ξ η*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by simp only [mul_assoc]
    _=(sourceForwardCore t ht.le*multiply c hc)*
      (correctedProfileCore t ht ξ η*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by rw [hF]
    _=sourceForwardCore t ht.le*((multiply c hc*correctedProfileCore t ht ξ η)*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by simp only [mul_assoc]
    _=sourceForwardCore t ht.le*((correctedProfileCore t ht ξ η*multiply c hc)*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by rw [hP.eq.symm]
    _=sourceForwardCore t ht.le*(correctedProfileCore t ht ξ η*
      (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)*multiply c hc)):=by
        rw [mul_assoc,hG.eq.symm]
    _=_:=by dsimp only [c,hc,forward_coframe_smooth];simp only [mul_assoc]
private theorem forwardGenerator_component(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator f z.val word=(-6:ℂ)*(reciprocalVolume z.val:ℂ)*
      fderiv ℝ (component word f) z.val (euler z.val)-9*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*f z.val word:=by
  change (-9*Complex.I)*((reciprocalVolume z.val:ℂ)*dilation f z.val word)+9*((reciprocalVolume z.val:ℂ)*f z.val word)=_
  rw [dilation_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem driftClock_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    SourceClockPhiMatchedDiffusionSource.driftClock f z word=
      (reciprocalVolume z:ℂ)*combinedGenerator f z word-(1/3:ℂ)*forwardGenerator f z word:=by
  have h:SourceClockPhiMatchedDiffusionSource.driftClock=
      inverseVolumeAction*combinedGenerator-(1/3:ℂ) • forwardGenerator:=by
    rw [forwardGenerator_original]
    unfold SourceClockPhiMatchedDiffusionSource.driftClock SourceClockPhiNativeMatchedSource.matchedColumn
    module
  rw [h]
  rfl
private theorem gain_line(t:ℝ)(ht:0<t)(z:physicalChart)(v:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) (z.val+s • v))
      (-3*t*reciprocalVolume z.val*SourceClockPhiForwardNativeReturn.forwardU t z.val*
        SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val*
          fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hv:HasDerivAt (fun s:ℝ=>GaussNativeEnergy.volume (z.val+s • v))
      (fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=
    ((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hr:HasDerivAt (fun s:ℝ=>forwardRatio t (z.val+s • v))
      (-18*t/GaussNativeEnergy.volume z.val^2*fderiv ℝ GaussNativeEnergy.volume z.val v) 0:=by
    have h:=(hv.add_const (18*t)).div hv (by simpa using (volume_pos z).ne')
    apply h.congr_deriv
    simp only [zero_smul,add_zero]
    field_simp [(volume_pos z).ne']
    ring
  have h:=hr.rpow_const (p:=(1/6:ℝ)) (Or.inl (by simpa using (forward_ratio_pos t ht.le z).ne'))
  change HasDerivAt (fun s:ℝ=>forwardRatio ((Real.sqrt t)^2) (z.val+s • v)^(1/6:ℝ)) _ 0
  rw [Real.sq_sqrt ht.le]
  apply h.congr_deriv
  simp only [zero_smul,add_zero]
  rw [Real.rpow_sub (forward_ratio_pos t ht.le z),Real.rpow_one]
  unfold SourceClockPhiActualCovarianceStep.gainProfile
  rw [Real.sq_sqrt ht.le]
  unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU forwardRatio
  field_simp [(volume_pos z).ne',show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z]]
  ring
private theorem gain_component_derivative(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)
    (v:SourceCoordinateSlice)(word:Occupation):
    fderiv ℝ (component word (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)) z.val v=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (fderiv ℝ (component word f) z.val v-
          (3*t*reciprocalVolume z.val*SourceClockPhiForwardNativeReturn.forwardU t z.val*
            fderiv ℝ GaussNativeEnergy.volume z.val v:ℝ)*f z.val word):=by
  have hx:HasDerivAt (fun s:ℝ=>z.val+s • v) v 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hg:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (gain_line t ht z v)
  have hh:=hg.mul hf
  change HasDerivAt (fun s:ℝ=>SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f (z.val+s • v) word) _ 0 at hh
  have he:=hl.unique hh
  rw [he]
  simp only [Function.comp_def,zero_smul,add_zero,Complex.ofRealCLM_apply,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat]
  rw [show (component word f) z.val=f z.val word from rfl]
  ring
private theorem volume_euler(z:SourceCoordinateSlice):
    fderiv ℝ volume z (SourceCoframeVolume.euler z)=3*volume z:=by
  rw [SourceCoframeVolume.volume_derivative]
  change z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5=_
  unfold volume
  ring
private theorem gain_combined_point(t:ℝ)(_ht:0<t)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    combinedGenerator (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*combinedGenerator f z.val word:=by
  exact congrArg (fun q:QuantumTest=>q z.val word) (LinearMap.congr_fun (gain_combined (Real.sqrt t)).eq f)
private theorem gain_driftClock(t:ℝ)(ht:0<t)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    SourceClockPhiMatchedDiffusionSource.driftClock (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f) z.val word=
      (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*
        (SourceClockPhiMatchedDiffusionSource.driftClock f z.val word-
          ((reciprocalVolume z.val-SourceClockPhiForwardNativeReturn.forwardU t z.val:ℝ):ℂ)*f z.val word):=by
  rw [driftClock_component,gain_combined_point t ht,forwardGenerator_component,gain_component_derivative t ht,
    volume_euler,driftClock_component,forwardGenerator_component]
  change (reciprocalVolume z.val:ℂ)*_-(1/3:ℂ)*((-6:ℂ)*(reciprocalVolume z.val:ℂ)*_-
      9*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*
        ((SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*f z.val word))=_
  unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
  push_cast
  have hv:(GaussNativeEnergy.volume z.val:ℂ)≠0:=by exact_mod_cast (volume_pos z).ne'
  have hw:(GaussNativeEnergy.volume z.val+18*t:ℂ)≠0:=by exact_mod_cast (show GaussNativeEnergy.volume z.val+18*t≠0 by linarith [volume_pos z])
  have hw':(t:ℂ)*18+GaussNativeEnergy.volume z.val≠0:=by
    convert hw using 1
    ring
  ring_nf
  field_simp [hv,hw,hw']
  have hi:((t:ℂ)*18+GaussNativeEnergy.volume z.val)*((t:ℂ)*18+GaussNativeEnergy.volume z.val)⁻¹=1:=mul_inv_cancel₀ hw'
  linear_combination (norm:=ring) -(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z.val:ℂ)*(f z.val word)*hi

theorem actual_gain_B3_return(t:ℝ)(ht:0<t)(f:QuantumTest):
    SourceClockPhiMatchedDiffusionSource.driftClock (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)=
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
        (SourceClockPhiMatchedDiffusionSource.driftClock f-(inverseVolumeAction-forwardUAction t ht.le) f):=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    change _=(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ)*
      (SourceClockPhiMatchedDiffusionSource.driftClock f z word-
        ((reciprocalVolume z:ℂ)*f z word-(forwardU t z:ℂ)*f z word))
    have h:=gain_driftClock t ht f ⟨z,hz⟩ word
    simpa only [Complex.ofReal_sub,sub_mul] using h
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [hzero,hzero]

theorem actual_corrected_complete_matched_tester(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    SourceClockPhiNativeMatchedSource.matchedTester (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η
        (SourceClockPhiNativeMatchedSource.matchedTester f-noiseAction t ht ξ η (combinedGenerator f)):=by
  have hB:=actual_corrected_complete_B3_input_return t ht ξ η f
  have hU:=LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht ξ η) f
  have hc:Commute (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)) (noiseAction t ht ξ η):=
    multiplier_commute _
      (fun z=>(SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z:ℂ) • ContinuousLinearMap.id ℂ FockFiber)
      (fun _ _=>rfl) _ _
  have hg:=LinearMap.congr_fun hc.eq (combinedGenerator f)
  simp only [Module.End.mul_apply] at hU hg
  rw [actual_gain_B3_return t ht] at hB
  change _=correctedHeatCore t ht ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (SourceClockPhiMatchedDiffusionSource.driftClock f-
      (inverseVolumeAction-forwardUAction t ht.le) f)-noiseAction t ht ξ η
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) (combinedGenerator f))) at hB
  rw [←hg] at hB
  have hM:SourceClockPhiNativeMatchedSource.matchedTester=
      SourceClockPhiMatchedDiffusionSource.driftClock-inverseVolumeAction:=by
    unfold SourceClockPhiNativeMatchedSource.matchedTester SourceClockPhiMatchedDiffusionSource.driftClock
    module
  rw [hM]
  simp only [LinearMap.sub_apply]
  rw [hB,hU]
  simp only [map_sub,LinearMap.sub_apply]
  simp only [correctedCompleteCore,Module.End.mul_apply]
  module

end LowEnergy.SourceClockPhiCorrectedWeightTransport
