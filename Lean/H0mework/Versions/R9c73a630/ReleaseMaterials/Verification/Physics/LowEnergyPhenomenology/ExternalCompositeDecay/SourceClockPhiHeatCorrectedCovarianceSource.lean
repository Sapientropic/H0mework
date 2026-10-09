import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatComparisonWork
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCovariancePhase
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianPlaneSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatCorrectedCovarianceSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource
open SourceClockPhiCombinedScalePressure SourceClockPhiCoframeForwardCore
open SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent GaussCoframeCore
open ClockPhiHeatComparisonWork ClockPhiHeatCovariancePhase
open MeasureTheory Set Filter
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev D:End:=combinedGenerator
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
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
private def angle(t:ℝ)(z:SourceCoordinateSlice):ℝ:=clockPhase (heatLog t z)
private def rotated(t:ℝ)(ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  ξ*Real.cos (angle t z)+η*Real.sin (angle t z)
private def perpendicular(t:ℝ)(ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  -ξ*Real.sin (angle t z)+η*Real.cos (angle t z)
def correctedCoefficient(t:ℝ)(ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatMean t z+Real.sqrt (heatVariance t z)*rotated t ξ η z
private theorem angle_smooth(t:ℝ)(ht:0<t)(z:physicalChart):ContDiffAt ℝ ∞ (angle t) z.val:=
  (clockPhase_smooth _ (log_pos t ht z)).comp z.val (log_smooth t ht z)
theorem coefficient_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (correctedCoefficient t ξ η) z.val:=by
  have hL:=log_smooth t ht z
  have hw:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>Real.sqrt (heatVariance t x)) z.val:=
    (hL.div_const 9).sqrt (ne_of_gt (div_pos (log_pos t ht z) (by norm_num)))
  have hr:ContDiffAt ℝ ∞ (rotated t ξ η) z.val:=
    (contDiffAt_const.mul (angle_smooth t ht z).cos).add
      (contDiffAt_const.mul (angle_smooth t ht z).sin)
  exact (hL.neg.div_const 6).add (hw.mul hr)
def correctedProfileCore(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  clockProfileAction (correctedCoefficient t ξ η) (coefficient_smooth t ht ξ η) (fun _ _=>rfl) 1
def correctedHeatCore(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  sourceForwardCore t ht.le*correctedProfileCore t ht ξ η
def correctedCompleteCore(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  correctedHeatCore t ht ξ η*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
private theorem corrected_profile_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedProfileCore t ht ξ η f) (correctedProfileCore t ht ξ η g)=sourcePair f g:=
  clockProfileAction_pair _ _ _ _ _ _
private theorem corrected_heat_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedHeatCore t ht ξ η f) (correctedHeatCore t ht ξ η g)=sourcePair f g:=by
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η f))
    (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η g))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair,corrected_profile_pair]
private theorem corrected_heat_norm(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    ‖embed (correctedHeatCore t ht ξ η f)‖=‖embed f‖:=by
  have h:=congrArg Complex.re (corrected_heat_pair t ht ξ η f f)
  change (inner ℂ (embed (correctedHeatCore t ht ξ η f)) (embed (correctedHeatCore t ht ξ η f))).re=
    (inner ℂ (embed f) (embed f)).re at h
  change RCLike.re (inner ℂ (embed (correctedHeatCore t ht ξ η f)) (embed (correctedHeatCore t ht ξ η f)))=
    RCLike.re (inner ℂ (embed f) (embed f)) at h
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (embed (correctedHeatCore t ht ξ η f)),norm_nonneg (embed f)]
private theorem corrected_profile_D(t:ℝ)(ht:0<t)(ξ η:ℝ):
    Commute D (correctedProfileCore t ht ξ η):=
  clockProfileAction_D _ _ _ _
private theorem corrected_profile_point(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    correctedProfileCore t ht ξ η f z=(Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z):ℂ) •
      f (combinedMap (correctedCoefficient t ξ η z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η z)):ℂ) •
    f (combinedMap (1*correctedCoefficient t ξ η z) z)=_
  simp only [one_mul]
private def extraCoefficient(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  2*Real.sqrt (heatLog t z)*(reciprocalVolume z-SourceClockPhiForwardNativeReturn.forwardU t z)*
    phaseSpeed (heatLog t z)
def covarianceNoise(t:ℝ)(ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatKappa t z*rotated t ξ η z+extraCoefficient t z*perpendicular t ξ η z
private def firstCoefficient(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatKappa t z*Real.cos (angle t z)-extraCoefficient t z*Real.sin (angle t z)
private def secondCoefficient(t:ℝ)(z:SourceCoordinateSlice):ℝ:=
  heatKappa t z*Real.sin (angle t z)+extraCoefficient t z*Real.cos (angle t z)
private theorem noise_columns(t ξ η:ℝ)(z:SourceCoordinateSlice):
    covarianceNoise t ξ η z=ξ*firstCoefficient t z+η*secondCoefficient t z:=by
  unfold covarianceNoise rotated perpendicular firstCoefficient secondCoefficient
  ring
private theorem clock_coefficient_square(t:ℝ)(ht:0<t)(z:physicalChart):
    heatKappa t z.val^2+extraCoefficient t z.val^2=
      (1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2):=by
  have hL:heatLog t z.val=Real.log ((GaussNativeEnergy.volume z.val+18*t)/GaussNativeEnergy.volume z.val):=by
    unfold heatLog reciprocalVolume;congr 1;field_simp [(volume_pos z).ne']
  have h:=actual_rotation_covariance (GaussNativeEnergy.volume z.val) t (volume_pos z) ht
  dsimp only at h
  rw [←hL] at h
  have hs:(Real.sqrt (heatLog t z.val))^2=heatLog t z.val:=Real.sq_sqrt (log_pos t ht z).le
  unfold heatKappa extraCoefficient SourceClockPhiForwardNativeReturn.forwardU reciprocalVolume
  rw [mul_pow,mul_pow,mul_pow,hs]
  simpa only [one_div,show (2:ℝ)^2=4 by norm_num] using h
private theorem covariance_column_square(t:ℝ)(ht:0<t)(z:physicalChart):
    firstCoefficient t z.val^2+secondCoefficient t z.val^2=
      (1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2):=by
  have hs:=Real.sin_sq_add_cos_sq (angle t z.val)
  have h:=clock_coefficient_square t ht z
  have he:firstCoefficient t z.val^2+secondCoefficient t z.val^2=
      (heatKappa t z.val^2+extraCoefficient t z.val^2)*
        (Real.sin (angle t z.val)^2+Real.cos (angle t z.val)^2):=by
    unfold firstCoefficient secondCoefficient
    ring
  rw [he,hs,mul_one]
  exact h
private def scalarClockLog(t V:ℝ):ℝ:=Real.log (1+18*t/V)
private def scalarClock(t ξ η V:ℝ):ℝ:=
  -scalarClockLog t V/6+Real.sqrt (scalarClockLog t V/9)*
    (ξ*Real.cos (clockPhase (scalarClockLog t V))+η*Real.sin (clockPhase (scalarClockLog t V)))
private def scalarNoise(t ξ η V:ℝ):ℝ:=
  ((1/V-1/(V+18*t))/Real.sqrt (scalarClockLog t V))*
      (ξ*Real.cos (clockPhase (scalarClockLog t V))+η*Real.sin (clockPhase (scalarClockLog t V)))+
    (2*Real.sqrt (scalarClockLog t V)*(1/V-1/(V+18*t))*phaseSpeed (scalarClockLog t V))*
      (-ξ*Real.sin (clockPhase (scalarClockLog t V))+η*Real.cos (clockPhase (scalarClockLog t V)))
private theorem scalar_log_derivative(t V:ℝ)(ht:0<t)(hV:0<V):
    HasDerivAt (scalarClockLog t) (-(1/V-1/(V+18*t))) V:=by
  have hW:0<V+18*t:=by positivity
  have hx:0<1+18*t/V:=by positivity
  have h:=(((hasDerivAt_const V (18*t)).div (hasDerivAt_id V) hV.ne').const_add 1).log hx.ne'
  dsimp at h
  convert! h using 1
  field_simp
  ring
private theorem scalarClock_derivative(t ξ η V:ℝ)(ht:0<t)(hV:0<V):
    HasDerivAt (scalarClock t ξ η) (((1/V-1/(V+18*t))-scalarNoise t ξ η V)/6) V:=by
  have hL:0<scalarClockLog t V:=by
    apply Real.log_pos
    have hp:0<18*t/V:=by positivity
    linarith
  have hl:=scalar_log_derivative t V ht hV
  have hψ:=(clockPhase_derivative (scalarClockLog t V) hL).comp V hl
  have hr:=(hψ.cos.const_mul ξ).add (hψ.sin.const_mul η)
  have hw:=SourceClockPhiHeatComparisonJet.clock_sqrt_variance_derivative V t hV ht
  have hm:=SourceClockPhiHeatComparisonJet.clock_mean_derivative V t hV ht
  have h:=hm.add (hw.mul hr)
  convert! h using 1
  unfold scalarNoise scalarClockLog
  dsimp only [Function.comp_def,Pi.add_apply]
  unfold scalarClockLog at hL
  rw [Real.sqrt_div hL.le]
  norm_num
  ring
private def correctedDelta(t ξ η:ℝ)(z:SourceCoordinateSlice):ℝ:=
  reciprocalVolume z-SourceClockPhiForwardNativeReturn.forwardU t z-covarianceNoise t ξ η z
private theorem volume_euler_jet(z:SourceCoordinateSlice):
    HasDerivAt (fun s:ℝ=>GaussNativeEnergy.volume (z+s • euler z)) (3*GaussNativeEnergy.volume z) 0:=by
  have he(s:ℝ):z+s • euler z=scale (1+s) z:=by
    apply Prod.ext
    · change z.1+s • z.1=(1+s) • z.1
      module
    · change z.2+s • 0=z.2
      simp only [smul_zero,add_zero]
  have h:=(((hasDerivAt_id (0:ℝ)).const_add 1).pow 3).mul_const (GaussNativeEnergy.volume z)
  simpa only [he,volume_scale,Pi.pow_apply,Pi.add_apply,id_eq,add_zero,one_pow,Nat.cast_ofNat,mul_one,one_mul] using h
private theorem coefficient_euler_jet(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    HasDerivAt (fun s:ℝ=>correctedCoefficient t ξ η (z.val+s • euler z.val))
      ((GaussNativeEnergy.volume z.val/2)*correctedDelta t ξ η z.val) 0:=by
  have h:=(scalarClock_derivative t ξ η (GaussNativeEnergy.volume z.val) ht (volume_pos z)).comp_of_eq (0:ℝ)
    (volume_euler_jet z.val) (by simp)
  have hv(x:SourceCoordinateSlice):scalarClockLog t (GaussNativeEnergy.volume x)=heatLog t x:=by
    unfold scalarClockLog heatLog reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
  have he(s:ℝ):scalarClock t ξ η (GaussNativeEnergy.volume (z.val+s • euler z.val))=
      correctedCoefficient t ξ η (z.val+s • euler z.val):=by
    unfold scalarClock correctedCoefficient heatMean heatVariance rotated angle
    rw [hv]
  have hd:(((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))-
      scalarNoise t ξ η (GaussNativeEnergy.volume z.val))/6)*(3*GaussNativeEnergy.volume z.val)=
      (GaussNativeEnergy.volume z.val/2)*correctedDelta t ξ η z.val:=by
    unfold correctedDelta covarianceNoise scalarNoise heatKappa extraCoefficient rotated perpendicular angle
    rw [hv]
    unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
    simp only [one_div]
    ring
  simpa only [Function.comp_def,he,hd] using h
private theorem corrected_coefficient_derivative(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart)(v:SourceCoordinateSlice):
    fderiv ℝ (correctedCoefficient t ξ η) z.val v=
      (correctedDelta t ξ η z.val/6)*fderiv ℝ GaussNativeEnergy.volume z.val v:=by
  have he:correctedCoefficient t ξ η=fun x:SourceCoordinateSlice=>scalarClock t ξ η (GaussNativeEnergy.volume x):=by
    funext x
    unfold correctedCoefficient scalarClock scalarClockLog heatMean heatVariance heatLog reciprocalVolume rotated angle
    rw [div_eq_mul_inv (18*t)]
    simp only [heatLog,reciprocalVolume]
  have h:=((scalarClock_derivative t ξ η (GaussNativeEnergy.volume z.val) ht (volume_pos z)).hasFDerivAt).comp z.val
    ((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hf:=congrArg (fun L:SourceCoordinateSlice→L[ℝ]ℝ=>L v) h.fderiv
  change fderiv ℝ (fun x:SourceCoordinateSlice=>scalarClock t ξ η (GaussNativeEnergy.volume x)) z.val v=
    fderiv ℝ GaussNativeEnergy.volume z.val v*
      (((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))-
        scalarNoise t ξ η (GaussNativeEnergy.volume z.val))/6) at hf
  rw [←he] at hf
  have hv:scalarClockLog t (GaussNativeEnergy.volume z.val)=heatLog t z.val:=by
    unfold scalarClockLog heatLog reciprocalVolume
    rw [div_eq_mul_inv (18*t)]
  have hd:((1/GaussNativeEnergy.volume z.val-1/(GaussNativeEnergy.volume z.val+18*t))-
      scalarNoise t ξ η (GaussNativeEnergy.volume z.val))=correctedDelta t ξ η z.val:=by
    unfold correctedDelta covarianceNoise scalarNoise heatKappa extraCoefficient rotated perpendicular angle
    rw [hv]
    unfold reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
    simp only [one_div]
  rw [hf,hd,mul_comm]
private theorem volume_euler_value(z:SourceCoordinateSlice):
    fderiv ℝ GaussNativeEnergy.volume z (euler z)=3*GaussNativeEnergy.volume z:=by
  rw [volume_derivative]
  change z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5+z.1 0*z.1 2*z.1 5=_
  unfold GaussNativeEnergy.volume
  ring
theorem actual_corrected_row_coefficient(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart)(i:Fin 6):
    3*t*(reciprocalVolume z.val)^2*volumeGradient z.val i-
      fderiv ℝ (correctedCoefficient t ξ η) z.val (coframeDirection i)-
      6*t*(reciprocalVolume z.val)^2*volumeGradient z.val i*
        fderiv ℝ (correctedCoefficient t ξ η) z.val (euler z.val)=
      forwardRatio t z.val*covarianceNoise t ξ η z.val*volumeGradient z.val i/6:=by
  rw [corrected_coefficient_derivative t ht ξ η z (coframeDirection i),
    corrected_coefficient_derivative t ht ξ η z (euler z.val),
    volume_coordinate_derivative,volume_euler_value]
  unfold correctedDelta reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU forwardRatio
  have hW:0<GaussNativeEnergy.volume z.val+18*t:=by linarith [volume_pos z]
  have hm:(GaussNativeEnergy.volume z.val+18*t)*(GaussNativeEnergy.volume z.val+18*t)⁻¹=1:=mul_inv_cancel₀ hW.ne'
  field_simp [(volume_pos z).ne',hW.ne']
  linear_combination (norm:=ring_nf) volumeGradient z.val i*GaussNativeEnergy.volume z.val*hm
private def inputMap(t ξ η:ℝ)(z:SourceCoordinateSlice):SourceCoordinateSlice:=
  combinedMap (correctedCoefficient t ξ η z) z
private theorem inputMap_euler_jet(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    HasDerivAt (fun s:ℝ=>inputMap t ξ η (z.val+s • euler z.val))
      (euler z.val+((GaussNativeEnergy.volume z.val/2)*correctedDelta t ξ η z.val) •
        (SourceScalarVirialBulk.phiEuler (inputMap t ξ η z.val)-SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ η z.val))) 0:=by
  let c:=correctedCoefficient t ξ η z.val
  let dc:=(GaussNativeEnergy.volume z.val/2)*correctedDelta t ξ η z.val
  have hc:=coefficient_euler_jet t ht ξ η z
  have he:=hc.exp
  have hn:=hc.neg.exp
  have hco:HasDerivAt (fun s:ℝ=>z.val.1+s • z.val.1) z.val.1 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const z.val.1).const_add z.val.1
  have h:=hco.prodMk (((he.smul_const (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)).sub_const SourceScalarVirialBulk.vacuumSlice).prodMk
    (hn.smul_const z.val.2.2))
  have hp:correctedCoefficient t ξ η (z.val+(0:ℝ) • euler z.val)=c:=by simp [c]
  simp only [Pi.neg_apply,hp] at h
  have hd:(z.val.1,(Real.exp c*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice),(Real.exp (-c)*(-dc)) • z.val.2.2)=
      euler z.val+dc • (SourceScalarVirialBulk.phiEuler (inputMap t ξ η z.val)-
        SourceGaugeRadialCurrent.gaugeEuler (inputMap t ξ η z.val)):=by
    simp only [inputMap,combinedMap_apply,SourceScalarVirialBulk.phiEuler,SourceGaugeRadialCurrent.gaugeEuler,euler]
    apply Prod.ext
    · simp
    apply Prod.ext
    · change (Real.exp c*dc) • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)=
        0+dc • (SourceScalarVirialBulk.vacuumSlice+(Real.exp c • (z.val.2.1+SourceScalarVirialBulk.vacuumSlice)-SourceScalarVirialBulk.vacuumSlice)-0)
      module
    · change (Real.exp (-c)*(-dc)) • z.val.2.2=0+dc • (0-Real.exp (-c) • z.val.2.2)
      module
  apply (h.congr_deriv hd).congr_of_eventuallyEq
  exact Eventually.of_forall (fun s=>by
    simp only [inputMap,combinedMap_apply,euler,Prod.fst_add,Prod.snd_add,Prod.smul_mk,smul_zero,add_zero])

private theorem component_fderiv(f:QuantumTest)(z v:SourceCoordinateSlice)(word:Occupation):
    fderiv ℝ f z v word=fderiv ℝ (component word f) z v:=by
  have h:=congrArg (fun g:GaussDensityCore.ScalarTest=>g z) (GaussCoframeCore.component_derivative v f word)
  change GaussCoframeCore.derivative v f z word=GaussDensityCore.derivative v (component word f) z at h
  simpa only [GaussCoframeCore.derivative_apply,GaussDensityCore.derivative_apply] using h
private theorem combined_component(f:QuantumTest)(z:SourceCoordinateSlice)(word:Occupation):
    combinedGenerator f z word=fderiv ℝ (component word f) z
      (SourceScalarVirialBulk.phiEuler z-SourceGaugeRadialCurrent.gaugeEuler z)+(25/2:ℂ)*f z word:=by
  have h:=congrArg (fun v:FockFiber=>v word) (combined_generator_point f z)
  simpa only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,component_fderiv] using h
private theorem input_euler_derivative(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest)(z:physicalChart)(word:Occupation):
    fderiv ℝ (component word (correctedProfileCore t ht ξ η f)) z.val (euler z.val)=
      (Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z.val):ℂ)*
        (fderiv ℝ (component word f) (inputMap t ξ η z.val) (euler z.val)+
          ((GaussNativeEnergy.volume z.val/2)*correctedDelta t ξ η z.val:ℝ)*
            combinedGenerator f (inputMap t ξ η z.val) word):=by
  have hc:=coefficient_euler_jet t ht ξ η z
  have hx:=inputMap_euler_jet t ht ξ η z
  have hz:HasDerivAt (fun s:ℝ=>z.val+s • euler z.val) (euler z.val) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (euler z.val)).const_add z.val
  have hf:=(((component word f).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=inputMap t ξ η z.val)).comp_hasDerivAt_of_eq (0:ℝ) hx (by simp)
  have hl:=(((component word (correctedProfileCore t ht ξ η f)).contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
    (x:=z.val)).comp_hasDerivAt_of_eq (0:ℝ) hz (by simp)
  have he0:=(hc.const_mul (25/2:ℝ)).exp
  have he:=Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) he0
  have hh:=he.mul hf
  have heq:(fun s:ℝ=>(Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (z.val+s • euler z.val)):ℂ)*
      f (inputMap t ξ η (z.val+s • euler z.val)) word)=
      fun s:ℝ=>correctedProfileCore t ht ξ η f (z.val+s • euler z.val) word:=by
    funext s
    rw [corrected_profile_point]
    rfl
  have hcomp(q:QuantumTest)(x:SourceCoordinateSlice):(component word q) x=q x word:=rfl
  dsimp only [Function.comp_def,Complex.ofRealCLM_apply,Pi.mul_apply] at hh hl
  simp only [hcomp] at hh hl
  change HasDerivAt (fun s:ℝ=>(Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η (z.val+s • euler z.val)):ℂ)*
    f (inputMap t ξ η (z.val+s • euler z.val)) word) _ 0 at hh
  rw [heq] at hh
  have h:=hl.unique hh
  rw [h,combined_component]
  simp only [zero_smul,add_zero,map_add,map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.ofReal_eq_complex_ofReal,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

theorem noise_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (covarianceNoise t ξ η) z.val:=by
  have hL:=log_smooth t ht z
  have hΔ:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>reciprocalVolume x-SourceClockPhiForwardNativeReturn.forwardU t x) z.val:=
    (reciprocal_volume_smooth z).sub (SourceClockPhiForwardNativeReturn.forwardU_smooth t ht.le z)
  have hs:=hL.sqrt (log_pos t ht z).ne'
  have hk:ContDiffAt ℝ ∞ (heatKappa t) z.val:=hΔ.div hs (Real.sqrt_pos.mpr (log_pos t ht z)).ne'
  have he:ContDiffAt ℝ ∞ (extraCoefficient t) z.val:=
    ((contDiffAt_const.mul hs).mul hΔ).mul ((phaseSpeed_smooth _ (log_pos t ht z)).comp z.val hL)
  have hc:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>Real.cos (angle t x)) z.val:=(angle_smooth t ht z).cos
  have hn:ContDiffAt ℝ ∞ (fun x:SourceCoordinateSlice=>Real.sin (angle t x)) z.val:=(angle_smooth t ht z).sin
  exact (hk.mul ((contDiffAt_const.mul hc).add (contDiffAt_const.mul hn))).add
    (he.mul ((contDiffAt_const.mul hn).add (contDiffAt_const.mul hc)))
private theorem delta_smooth(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart):
    ContDiffAt ℝ ∞ (correctedDelta t ξ η) z.val:=
  ((reciprocal_volume_smooth z).sub (SourceClockPhiForwardNativeReturn.forwardU_smooth t ht.le z)).sub (noise_smooth t ht ξ η z)
def noiseAction(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=multiply (covarianceNoise t ξ η) (noise_smooth t ht ξ η)
private def deltaAction(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=multiply (correctedDelta t ξ η) (delta_smooth t ht ξ η)
private theorem inputMap_chart(t ξ η:ℝ)(z:physicalChart):inputMap t ξ η z.val∈physicalChart:=
  ((SourceGaugeScaleTransport.scale_chart_iff (Real.exp (-correctedCoefficient t ξ η z.val)) (Real.exp_pos _)
    (SourceScalarAffineScaleTransport.scaleEquiv (correctedCoefficient t ξ η z.val) z.val)).trans
    (SourceScalarAffineScaleTransport.scale_chart_iff (correctedCoefficient t ξ η z.val) z.val)).mpr z.property
private theorem forward_component(f:QuantumTest)(z:physicalChart)(word:Occupation):
    forwardGenerator f z.val word=(-6:ℂ)*(reciprocalVolume z.val:ℂ)*
      fderiv ℝ (component word f) z.val (euler z.val)-
      (9:ℂ)*(word.card+3:ℂ)*(reciprocalVolume z.val:ℂ)*f z.val word:=by
  change (-9*Complex.I)*((reciprocalVolume z.val:ℂ)*dilation f z.val word)+
    9*((reciprocalVolume z.val:ℂ)*f z.val word)=_
  rw [dilation_apply]
  ring_nf
  simp only [Complex.I_sq]
  ring
private theorem input_forward_drift(t:ℝ)(ht:0<t)(ξ η:ℝ):
    forwardGenerator*correctedProfileCore t ht ξ η=
      correctedProfileCore t ht ξ η*(forwardGenerator-(3:ℂ) • (deltaAction t ht ξ η*combinedGenerator)):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext;intro word
    let hp:physicalChart:=⟨z,hz⟩
    let hm:physicalChart:=⟨inputMap t ξ η z,inputMap_chart t ξ η hp⟩
    change forwardGenerator (correctedProfileCore t ht ξ η f) z word=
      correctedProfileCore t ht ξ η (forwardGenerator f-(3:ℂ) • deltaAction t ht ξ η (combinedGenerator f)) z word
    rw [forward_component _ hp,input_euler_derivative _ _ _ _ _ hp,corrected_profile_point,corrected_profile_point]
    change (-6:ℂ)*(reciprocalVolume z:ℂ)*
      ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z):ℂ)*
        (fderiv ℝ (component word f) (inputMap t ξ η z) (euler z)+
          ((GaussNativeEnergy.volume z/2)*correctedDelta t ξ η z:ℝ)*combinedGenerator f (inputMap t ξ η z) word))-
      (9:ℂ)*(word.card+3:ℂ)*(reciprocalVolume z:ℂ)*
        ((Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z):ℂ)*f (inputMap t ξ η z) word)=
      (Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z):ℂ)*
        (forwardGenerator f (inputMap t ξ η z) word-
          3*((correctedDelta t ξ η (inputMap t ξ η z):ℂ)*combinedGenerator f (inputMap t ξ η z) word))
    rw [forward_component f hm]
    have he:euler (inputMap t ξ η z)=euler z:=rfl
    have hu:reciprocalVolume (inputMap t ξ η z)=reciprocalVolume z:=rfl
    have hd:correctedDelta t ξ η (inputMap t ξ η z)=correctedDelta t ξ η z:=rfl
    rw [he,hu,hd]
    simp only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
    have hV: (GaussNativeEnergy.volume z:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (volume_pos hp).ne'
    unfold reciprocalVolume
    push_cast
    field_simp [hV]
    ring
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    rw [h0,h0]

open SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource
private theorem drift_forward_split:
    driftClock=inverseVolumeAction*combinedGenerator-(1/3:ℂ) • forwardGenerator:=by
  rw [forwardGenerator_original]
  unfold driftClock matchedColumn
  module
private theorem corrected_multiplier(t:ℝ)(ht:0<t)(ξ η:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hi:∀u z,c (combinedMap u z)=c z):
    Commute (correctedProfileCore t ht ξ η) (multiply c hc):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change correctedProfileCore t ht ξ η (multiply c hc f) z=multiply c hc (correctedProfileCore t ht ξ η f) z
  rw [corrected_profile_point]
  change (Real.exp ((25/2:ℝ)*correctedCoefficient t ξ η z):ℂ) •
      ((c (combinedMap (correctedCoefficient t ξ η z) z):ℂ) • f (combinedMap (correctedCoefficient t ξ η z) z))=
    (c z:ℂ) • correctedProfileCore t ht ξ η f z
  rw [corrected_profile_point,hi]
  exact smul_comm _ _ _
private theorem corrected_heat_UD(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    (inverseVolumeAction*combinedGenerator) (correctedHeatCore t ht ξ η f)=
      correctedHeatCore t ht ξ η (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (combinedGenerator f)):=by
  have hJ:=LinearMap.congr_fun (SourceClockPhiForwardGeneratorTransport.actual_forward_generator_commute t ht.le).eq
    (correctedProfileCore t ht ξ η f)
  have hN:=LinearMap.congr_fun (corrected_profile_D t ht ξ η).eq f
  have hU:=LinearMap.congr_fun (SourceClockPhiForwardNativeReturn.actual_forward_U_return t ht.le)
    (correctedProfileCore t ht ξ η (combinedGenerator f))
  have hM:=LinearMap.congr_fun (corrected_multiplier t ht ξ η
    (SourceClockPhiForwardNativeReturn.forwardU t) (SourceClockPhiForwardNativeReturn.forwardU_smooth t ht.le) (fun _ _=>rfl)).eq
    (combinedGenerator f)
  simp only [Module.End.mul_apply] at hJ hN hU hM
  change correctedProfileCore t ht ξ η (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (combinedGenerator f))=
    SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (correctedProfileCore t ht ξ η (combinedGenerator f)) at hM
  change inverseVolumeAction (combinedGenerator (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η f)))=_
  rw [hJ,hN,hU,←hM]
  rfl
private theorem corrected_forward_delta(t:ℝ)(ht:0<t)(ξ η:ℝ):
    SourceClockPhiForwardNativeReturn.forwardUAction t ht.le+deltaAction t ht ξ η=inverseVolumeAction-noiseAction t ht ξ η:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (SourceClockPhiForwardNativeReturn.forwardU t z:ℂ) • f z+(correctedDelta t ξ η z:ℂ) • f z=
    (reciprocalVolume z:ℂ) • f z-(covarianceNoise t ξ η z:ℂ) • f z
  unfold correctedDelta
  simp only [Complex.ofReal_sub]
  module
private theorem actual_corrected_heat_B3(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    driftClock (correctedHeatCore t ht ξ η f)=
      correctedHeatCore t ht ξ η (driftClock f-noiseAction t ht ξ η (combinedGenerator f)):=by
  have hK(q:QuantumTest):sourceForwardCore t ht.le (correctedProfileCore t ht ξ η q)=correctedHeatCore t ht ξ η q:=rfl
  have hJ:=LinearMap.congr_fun (SourceClockPhiForwardDriftTransport.actual_forward_drift_commute t ht.le).eq
    (correctedProfileCore t ht ξ η f)
  have hN:=LinearMap.congr_fun (input_forward_drift t ht ξ η) f
  simp only [Module.End.mul_apply] at hJ hN
  have hLV:forwardGenerator (correctedHeatCore t ht ξ η f)=
      correctedHeatCore t ht ξ η (forwardGenerator f-(3:ℂ) • deltaAction t ht ξ η (combinedGenerator f)):=by
    rw [←hK,hJ,hN]
    exact hK _
  have hB(q:QuantumTest):driftClock q=inverseVolumeAction (combinedGenerator q)-(1/3:ℂ) • forwardGenerator q:=
    LinearMap.congr_fun drift_forward_split q
  have hF:=LinearMap.congr_fun (corrected_forward_delta t ht ξ η) (combinedGenerator f)
  change SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (combinedGenerator f)+
    deltaAction t ht ξ η (combinedGenerator f)=inverseVolumeAction (combinedGenerator f)-noiseAction t ht ξ η (combinedGenerator f) at hF
  have he:=congrArg (correctedHeatCore t ht ξ η) hF
  simp only [map_add,map_sub] at he
  rw [hB]
  change (inverseVolumeAction*combinedGenerator) (correctedHeatCore t ht ξ η f)-
    (1/3:ℂ) • forwardGenerator (correctedHeatCore t ht ξ η f)=_
  rw [corrected_heat_UD,hLV,hB]
  simp only [map_sub,map_smul]
  linear_combination (norm:=module) he
private def firstNoiseAction(t:ℝ)(ht:0<t):End:=noiseAction t ht 1 0
private def secondNoiseAction(t:ℝ)(ht:0<t):End:=noiseAction t ht 0 1
private theorem noise_action_linear(t:ℝ)(ht:0<t)(ξ η:ℝ):
    noiseAction t ht ξ η=(ξ:ℂ) • firstNoiseAction t ht+(η:ℂ) • secondNoiseAction t ht:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (covarianceNoise t ξ η z:ℂ) • f z=
    (ξ:ℂ) • ((covarianceNoise t 1 0 z:ℂ) • f z)+(η:ℂ) • ((covarianceNoise t 0 1 z:ℂ) • f z)
  rw [noise_columns,noise_columns,noise_columns]
  simp only [one_mul,zero_mul,zero_add,add_zero,Complex.ofReal_add,Complex.ofReal_mul,smul_smul,add_smul]
private theorem multiplier_density(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:QuantumTest)(z:SourceCoordinateSlice):
    (densityPair (multiply c hc f) (multiply c hc f) z).re=c z^2*(densityPair f f z).re:=by
  change (inner ℂ (GaussFockWeights.weight (fun N=>GaussDensityCore.complexDensity N z)
    ((c z:ℂ) • f z)) ((c z:ℂ) • f z)).re=_
  rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  change ((c z:ℂ)*((c z:ℂ)*densityPair f f z)).re=_
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring
private theorem comparison_columns(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖embed (firstNoiseAction t ht f)‖^2+‖embed (secondNoiseAction t ht f)‖^2+
      (1/2:ℝ)*‖embed (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le f)‖^2=
      (1/2:ℝ)*‖embed (inverseVolumeAction f)‖^2:=by
  have hp(z:SourceCoordinateSlice):
      (densityPair (firstNoiseAction t ht f) (firstNoiseAction t ht f) z).re+
      (densityPair (secondNoiseAction t ht f) (secondNoiseAction t ht f) z).re+
      (1/2:ℝ)*(densityPair (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le f)
        (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le f) z).re=
      (1/2:ℝ)*(densityPair (inverseVolumeAction f) (inverseVolumeAction f) z).re:=by
    change (densityPair (multiply (covarianceNoise t 1 0) (noise_smooth t ht 1 0) f) (multiply (covarianceNoise t 1 0) (noise_smooth t ht 1 0) f) z).re+
      (densityPair (multiply (covarianceNoise t 0 1) (noise_smooth t ht 0 1) f) (multiply (covarianceNoise t 0 1) (noise_smooth t ht 0 1) f) z).re+
      (1/2:ℝ)*(densityPair (multiply (SourceClockPhiForwardNativeReturn.forwardU t) _ f)
        (multiply (SourceClockPhiForwardNativeReturn.forwardU t) _ f) z).re=
      (1/2:ℝ)*(densityPair (multiply reciprocalVolume _ f) (multiply reciprocalVolume _ f) z).re
    rw [multiplier_density,multiplier_density,multiplier_density,multiplier_density]
    by_cases hz:z∈physicalChart
    · have hc:=covariance_column_square t ht ⟨z,hz⟩
      rw [noise_columns,noise_columns]
      simp only [one_mul,zero_mul,zero_add,add_zero]
      have hh:=congrArg (fun a:ℝ=>a*(densityPair f f z).re) hc
      nlinarith only [hh]
    · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
      simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero,add_zero]
  have hi0:Integrable (fun z=>(densityPair (firstNoiseAction t ht f) (firstNoiseAction t ht f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have hi1:Integrable (fun z=>(densityPair (secondNoiseAction t ht f) (secondNoiseAction t ht f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have hi2:Integrable (fun z=>(densityPair (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le f)
      (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le f) z).re)
      GaussHistoryHilbert.configurationMeasure:=(densityPair_integrable _ _).re
  have hi01:Integrable (fun z:SourceCoordinateSlice=>(densityPair (firstNoiseAction t ht f) (firstNoiseAction t ht f) z).re+
      (densityPair (secondNoiseAction t ht f) (secondNoiseAction t ht f) z).re)
      GaussHistoryHilbert.configurationMeasure:=hi0.add hi1
  have he:=integral_congr_ae (μ:=GaussHistoryHilbert.configurationMeasure) (Eventually.of_forall hp)
  rw [integral_add hi01 (hi2.const_mul (1/2:ℝ)),integral_add hi0 hi1,
    integral_const_mul,integral_const_mul] at he
  have hn(q:QuantumTest):‖embed q‖^2=(∫z,(densityPair q q z).re ∂GaussHistoryHilbert.configurationMeasure):=
    GaussBoundedMultiplier.norm_square_integral q
  rw [←hn,←hn,←hn,←hn] at he
  exact he
private theorem source_square_real(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  change RCLike.re (inner ℂ (embed f) (embed f))=‖embed f‖^2
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem gaussian_affine_norm(a b c:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>‖embed (a+(x.1:ℂ) • b+(x.2:ℂ) • c)‖^2) (γ.prod γ) ∧
      (∫x:ℝ×ℝ,‖embed (a+(x.1:ℂ) • b+(x.2:ℂ) • c)‖^2 ∂γ.prod γ)=
      ‖embed a‖^2+‖embed b‖^2+‖embed c‖^2:=by
  have h:=SourceClockPhiGaussianPlaneSource.actual_gaussian_affine_source_pair a b c a b c (1:End)
  change Integrable (fun x:ℝ×ℝ=>sourcePair (a+(x.1:ℂ) • b+(x.2:ℂ) • c)
      (a+(x.1:ℂ) • b+(x.2:ℂ) • c)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (a+(x.1:ℂ) • b+(x.2:ℂ) • c)
      (a+(x.1:ℂ) • b+(x.2:ℂ) • c) ∂γ.prod γ)=sourcePair a a+sourcePair b b+sourcePair c c at h
  have hi:Integrable (fun x:ℝ×ℝ=>‖embed (a+(x.1:ℂ) • b+(x.2:ℂ) • c)‖^2) (γ.prod γ):=by
    simpa only [RCLike.re_eq_complex_re,source_square_real] using h.1.re
  refine ⟨hi,?_⟩
  have hre:=integral_re h.1
  simp only [RCLike.re_eq_complex_re,source_square_real] at hre
  rw [hre,h.2,Complex.add_re,Complex.add_re,source_square_real,source_square_real,source_square_real]
open SourceClockPhiWholeSignedWorkIntegrable
private theorem corrected_comparison_point(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    comparisonEnergy (correctedHeatCore t ht ξ η f)=
      ‖embed (driftClock f+(ξ:ℂ) • (-(firstNoiseAction t ht (D f)))+
        (η:ℂ) • (-(secondNoiseAction t ht (D f))))‖^2+
      (1/2:ℝ)*‖embed (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (D f))‖^2:=by
  unfold comparisonEnergy
  rw [actual_corrected_heat_B3,corrected_heat_norm]
  change ‖embed (driftClock f-noiseAction t ht ξ η (D f))‖^2+
    (1/2:ℝ)*‖embed ((inverseVolumeAction*combinedGenerator) (correctedHeatCore t ht ξ η f))‖^2=_
  rw [corrected_heat_UD,corrected_heat_norm]
  have he:driftClock f-noiseAction t ht ξ η (D f)=
      driftClock f+(ξ:ℂ) • (-(firstNoiseAction t ht (D f)))+(η:ℂ) • (-(secondNoiseAction t ht (D f))):=by
    rw [noise_action_linear]
    simp only [LinearMap.add_apply,LinearMap.smul_apply]
    module
  rw [he]

/-- The source-generated two-noise coupling conserves the original finite-core comparison form in expectation. -/
theorem actual_corrected_comparison_conservation(t:ℝ)(ht:0<t)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>comparisonEnergy (correctedHeatCore t ht x.1 x.2 f)) (γ.prod γ) ∧
      (∫x:ℝ×ℝ,comparisonEnergy (correctedHeatCore t ht x.1 x.2 f) ∂γ.prod γ)=comparisonEnergy f:=by
  have h:=gaussian_affine_norm (driftClock f) (-(firstNoiseAction t ht (D f))) (-(secondNoiseAction t ht (D f)))
  have hc:Integrable (fun _:ℝ×ℝ=>(1/2:ℝ)*‖embed (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (D f))‖^2)
      (γ.prod γ):=integrable_const _
  refine ⟨(h.1.add hc).congr (Eventually.of_forall (fun x=>(corrected_comparison_point t ht x.1 x.2 f).symm)),?_⟩
  simp_rw [corrected_comparison_point]
  rw [integral_add h.1 hc,h.2]
  simp only [integral_const,probReal_univ,one_smul,map_neg,norm_neg]
  have hcol:=comparison_columns t ht (D f)
  unfold comparisonEnergy
  nlinarith only [hcol]

theorem actual_covariance_noise_affine(t ξ η:ℝ)(z:SourceCoordinateSlice):
    covarianceNoise t ξ η z=ξ*covarianceNoise t 1 0 z+η*covarianceNoise t 0 1 z:=by
  rw [noise_columns,noise_columns,noise_columns]
  simp only [one_mul,zero_mul,zero_add,add_zero]
theorem actual_covariance_noise_square(t:ℝ)(ht:0<t)(z:physicalChart):
    covarianceNoise t 1 0 z.val^2+covarianceNoise t 0 1 z.val^2=
      (1/2)*(reciprocalVolume z.val^2-(SourceClockPhiForwardNativeReturn.forwardU t z.val)^2):=by
  rw [noise_columns,noise_columns]
  simpa only [one_mul,zero_mul,zero_add,add_zero] using covariance_column_square t ht z

theorem actual_corrected_profile_gradient(t:ℝ)(ht:0<t)(ξ η:ℝ)(z:physicalChart)(v:SourceCoordinateSlice):
    fderiv ℝ (correctedCoefficient t ξ η) z.val v=
      ((reciprocalVolume z.val-SourceClockPhiForwardNativeReturn.forwardU t z.val-covarianceNoise t ξ η z.val)/6)*
        fderiv ℝ GaussNativeEnergy.volume z.val v:=by
  exact corrected_coefficient_derivative t ht ξ η z v
end LowEnergy.ClockPhiHeatCorrectedCovarianceSource

namespace LowEnergy.ClockPhiHeatCorrectedCovarianceSource
open GaussCoreHilbert GaussCoreDifferential SourceClockPhiMatchedDiffusionSource
open SourceClockPhiCombinedScalePressure ClockPhiMatchedNoiseCore SourcePhysicalKineticSquare

theorem actual_corrected_heat_B3_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    driftClock (correctedHeatCore t ht ξ η f)=
      correctedHeatCore t ht ξ η (driftClock f-noiseAction t ht ξ η (combinedGenerator f)):=
  actual_corrected_heat_B3 t ht ξ η f

theorem actual_corrected_heat_UD_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    (inverseVolumeAction*combinedGenerator) (correctedHeatCore t ht ξ η f)=
      correctedHeatCore t ht ξ η
        (SourceClockPhiForwardNativeReturn.forwardUAction t ht.le (combinedGenerator f)):=
  corrected_heat_UD t ht ξ η f
end LowEnergy.ClockPhiHeatCorrectedCovarianceSource
