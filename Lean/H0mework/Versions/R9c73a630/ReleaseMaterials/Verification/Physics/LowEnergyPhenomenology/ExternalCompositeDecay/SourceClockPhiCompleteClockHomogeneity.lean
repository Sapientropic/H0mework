import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScale
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeStrongJet
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep
open ClockPhiConservativeHeatSource ClockPhiHeatCorrectedCovarianceSource ClockPhiMatchedNoiseCore
open SourcePhysicalKineticSquare ClockPhiHeatCovariancePhase
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev T (u:ℝ):End:=SourceCoframeScaleTransport.coreFlow u
private abbrev r(u:ℝ):ℝ:=SourceCoframeScaleTransport.rate u

def dilatedClock(u t:ℝ):ℝ:=t/(r u)^3
private theorem dilated_positive(u t:ℝ)(ht:0<t):0<dilatedClock u t:=
  div_pos ht (pow_pos (Real.exp_pos _) 3)
private theorem ratio_scale(t a:ℝ)(ha:0<a)(z:SourceCoordinateSlice):
    forwardRatio t (scale a z)=forwardRatio (t/a^3) z ∧
    backwardRatio t (scale a z)=backwardRatio (t/a^3) z:=by
  unfold forwardRatio backwardRatio
  rw [volume_scale]
  by_cases hv:volume z=0
  · simp only [hv,mul_zero,div_zero,and_self]
  · constructor <;> field_simp [hv,ha.ne']
private theorem backward_scale(t a:ℝ)(ha:0<a)(z:SourceCoordinateSlice):
    backwardPoint t (scale a z)=scale a (backwardPoint (t/a^3) z):=by
  unfold backwardPoint
  rw [(ratio_scale t a ha z).2]
  simp only [scale,smul_smul,mul_comm]
private theorem log_scale(t a:ℝ)(ha:0<a)(z:SourceCoordinateSlice):
    heatLog t (scale a z)=heatLog (t/a^3) z:=by
  have h:1+18*t*reciprocalVolume (scale a z)=1+18*(t/a^3)*reciprocalVolume z:=by
    unfold reciprocalVolume
    rw [volume_scale]
    by_cases hv:volume z=0
    · simp only [hv,mul_zero,inv_zero]
    · field_simp [hv,ha.ne']
  exact congrArg Real.log h
private theorem coefficient_scale(t a ξ η:ℝ)(ha:0<a)(z:SourceCoordinateSlice):
    correctedCoefficient t ξ η (scale a z)=correctedCoefficient (t/a^3) ξ η z:=by
  change -(heatLog t (scale a z))/6+Real.sqrt (heatLog t (scale a z)/9)*
      (ξ*Real.cos (clockPhase (heatLog t (scale a z)))+η*Real.sin (clockPhase (heatLog t (scale a z))))=
    -(heatLog (t/a^3) z)/6+Real.sqrt (heatLog (t/a^3) z/9)*
      (ξ*Real.cos (clockPhase (heatLog (t/a^3) z))+η*Real.sin (clockPhase (heatLog (t/a^3) z)))
  rw [log_scale t a ha z]
private theorem combined_scale(c a:ℝ)(z:SourceCoordinateSlice):
    combinedMap c (scale a z)=scale a (combinedMap c z):=rfl
private theorem gain_scale(t a:ℝ)(ht:0<t)(ha:0<a)(z:SourceCoordinateSlice):
    gainProfile (Real.sqrt t) (scale a z)=gainProfile (Real.sqrt (t/a^3)) z:=by
  unfold gainProfile
  rw [Real.sq_sqrt ht.le,Real.sq_sqrt (div_pos ht (pow_pos ha 3)).le,
    (ratio_scale t a ha z).1]
private theorem forward_transport(u t:ℝ)(ht:0<t)(f:QuantumTest):
    T u (sourceForwardCore t ht.le f)=
      sourceForwardCore (dilatedClock u t) (dilated_positive u t ht).le (T u f):=by
  apply DFunLike.ext;intro z
  apply PiLp.ext;intro word
  have hr:0<r u:=Real.exp_pos _
  have hb:18*t<volume (scale (r u) z) ↔ 18*dilatedClock u t<volume z:=by
    rw [volume_scale]
    unfold dilatedClock
    rw [← mul_div_assoc,div_lt_iff₀ (pow_pos hr 3)]
    rw [mul_comm (volume z)]
  rw [SourceCoframeScaleTransport.coreFlow_apply]
  change (Real.exp ((word.card+4:ℝ)*u):ℂ)*forwardValue t f (scale (r u) z) word=
    forwardValue (dilatedClock u t) (T u f) z word
  by_cases hc:18*dilatedClock u t<volume z
  · simp only [forwardValue,if_pos hc,if_pos (hb.mpr hc)]
    rw [(ratio_scale t (r u) hr z).2,backward_scale t (r u) hr z,
      SourceCoframeScaleTransport.coreFlow_apply]
    dsimp only [dilatedClock,r]
    ring
  · simp only [forwardValue,if_neg hc,if_neg (fun h=>hc (hb.mp h)),PiLp.zero_apply,mul_zero]
private theorem profile_transport(u t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    T u (correctedProfileCore t ht ξ η f)=
      correctedProfileCore (dilatedClock u t) (dilated_positive u t ht) ξ η (T u f):=by
  apply DFunLike.ext;intro z
  apply PiLp.ext;intro word
  have hr:0<r u:=Real.exp_pos _
  change (Real.exp ((word.card+4:ℝ)*u):ℂ)*
      ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient t ξ η (scale (r u) z))):ℂ)*
        f (combinedMap (1*correctedCoefficient t ξ η (scale (r u) z)) (scale (r u) z)) word)=
    (Real.exp ((25/2:ℝ)*(1*correctedCoefficient (dilatedClock u t) ξ η z)):ℂ)*
      (T u f) (combinedMap (1*correctedCoefficient (dilatedClock u t) ξ η z) z) word
  simp only [one_mul]
  rw [coefficient_scale t (r u) ξ η hr z,combined_scale,SourceCoframeScaleTransport.coreFlow_apply]
  dsimp only [dilatedClock,r]
  ring
private theorem gain_transport(u t:ℝ)(ht:0<t)(f:QuantumTest):
    T u (sourceGain (Real.sqrt t) f)=sourceGain (Real.sqrt (dilatedClock u t)) (T u f):=by
  apply DFunLike.ext;intro z
  apply PiLp.ext;intro word
  change (Real.exp ((word.card+4:ℝ)*u):ℂ)*((gainProfile (Real.sqrt t) (scale (r u) z):ℂ)*f (scale (r u) z) word)=
    (gainProfile (Real.sqrt (dilatedClock u t)) z:ℂ)*((Real.exp ((word.card+4:ℝ)*u):ℂ)*f (scale (r u) z) word)
  rw [gain_scale t (r u) ht (Real.exp_pos _) z]
  dsimp only [dilatedClock,r]
  ring

/-- The original complete corrected clock is covariant under the original coframe source flow, with unchanged noises and phase. The rescaled clock is generated by the same source volume. -/
theorem actual_complete_clock_finite_homogeneity(u t:ℝ)(ht:0<t)(ξ η:ℝ):
    T u*correctedCompleteCore t ht ξ η=
      correctedCompleteCore (dilatedClock u t) (dilated_positive u t ht) ξ η*T u:=by
  apply LinearMap.ext;intro f
  change T u (sourceForwardCore t ht.le (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)))=
    sourceForwardCore (dilatedClock u t) (dilated_positive u t ht).le
      (correctedProfileCore (dilatedClock u t) (dilated_positive u t ht) ξ η
        (sourceGain (Real.sqrt (dilatedClock u t)) (T u f)))
  rw [forward_transport u t ht,profile_transport u t ht ξ η,gain_transport u t ht]
end LowEnergy.ReverseNativeClock
