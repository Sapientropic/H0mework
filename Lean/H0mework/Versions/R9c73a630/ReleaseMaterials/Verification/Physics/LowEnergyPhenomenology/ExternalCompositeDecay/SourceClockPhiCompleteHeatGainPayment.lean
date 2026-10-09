import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiComparisonNativeClosedGraph
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiActualCovarianceStep
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeSignedWorkIntegrable
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainCoefficient
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiCompleteHeatGainPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeDilation SourceCoframeVolumeCurrent
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiMatchedDiffusionSource
open SourceClockPhiComparisonNativeClosedGraph SourceClockPhiActualCovarianceStep ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore SourceGaugeRadialCurrent
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
private abbrev Op:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:Op:=inverseVolumeAction
private abbrev D:Op:=combinedGenerator
private abbrev Dc:Op:=dilation

def completeHeatCore(t:ℝ)(ht:0<t)(ξ:ℝ):Op:=sourceHeatCore t ht ξ*sourceGain (Real.sqrt t)

private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:Op=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=(-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=1:=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert! h using 1
  congr 1
  ring
private theorem inverse_combined:Commute U D:=by
  have hp:=SourceScalarAffineScaleTransport.generator_commutator U
  have hg:=SourceGaugeScaleTransport.generator_commutator U
  rw [SourceScalarInverseBulk.inverse_phi] at hp
  rw [SourceScalarInverseBulk.inverse_gauge] at hg
  change U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)=
    (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)*U
  linear_combination (norm:=noncomm_ring) -hp+hg
private theorem comparison_inverse_current:
    driftClock*U-U*driftClock=(-6:ℂ) • (U*U):=by
  apply LinearMap.ext
  intro f
  have hD:=LinearMap.congr_fun inverse_combined.eq f
  have hDc:=LinearMap.congr_fun inverse_dilation (U f)
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply] at hD hDc
  have hdc:Dc (U (U f))=U (Dc (U f))+(2*Complex.I) • U (U f):=by
    linear_combination (norm:=module) hDc
  change (U (D (U f))+(3*Complex.I) • Dc (U (U f))+(3:ℂ) • U (U f))-
    U (U (D f)+(3*Complex.I) • Dc (U f)+(3:ℂ) • U f)=(-6:ℂ) • U (U f)
  rw [←hD,hdc]
  simp only [map_add,map_smul,smul_add,smul_smul]
  have hc:(3*Complex.I)*(2*Complex.I)=(-6:ℂ):=by
    calc _=6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hc]
  module

private theorem B_pair(f g:QuantumTest):sourcePair (driftClock f) g= -sourcePair f (driftClock g):=by
  have h:=actual_B3_formal_pair (coreEquiv f) (coreEquiv g)
  change inner ℂ (embed (driftClock (coreEquiv.symm (coreEquiv f)))) (embed g)=
    inner ℂ (embed f) (embed ((-driftClock) (coreEquiv.symm (coreEquiv g)))) at h
  rw [coreEquiv.symm_apply_apply,coreEquiv.symm_apply_apply] at h
  simpa only [sourcePair,LinearMap.neg_apply,map_neg,inner_neg_right] using h
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ f g
theorem comparison_inverse_hardy(f:QuantumTest):3*‖embed (U f)‖≤‖embed (driftClock f)‖:=by
  have h:=LinearMap.congr_fun comparison_inverse_current f
  change driftClock (U f)-U (driftClock f)=(-6:ℂ) • U (U f) at h
  have hp:=congrArg (fun q:QuantumTest=>sourcePair f q) h
  simp only [sourcePair,map_sub,map_smul,inner_sub_right,inner_smul_right] at hp
  have hb0:=congrArg Neg.neg (B_pair f (U f))
  simp only [neg_neg] at hb0
  have hb:=hb0.symm
  have hu:=U_pair f (driftClock f)
  have huu:=U_pair f (U f)
  change inner ℂ (embed f) (embed (driftClock (U f)))= -inner ℂ (embed (driftClock f)) (embed (U f)) at hb
  change inner ℂ (embed f) (embed (U (driftClock f)))=inner ℂ (embed (U f)) (embed (driftClock f)) at hu
  change inner ℂ (embed f) (embed (U (U f)))=inner ℂ (embed (U f)) (embed (U f)) at huu
  rw [hb,hu,huu] at hp
  have hr:=congrArg Complex.re hp
  have hself:(inner ℂ (embed (U f)) (embed (U f))).re=‖embed (U f)‖^2:=by
    simpa only using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed (U f))
  simp only [Complex.sub_re,Complex.neg_re,Complex.mul_re,hself] at hr
  norm_num at hr
  have hs:(inner ℂ (embed (U f)) (embed (driftClock f))).re=
      (inner ℂ (embed (driftClock f)) (embed (U f))).re:=by
    simpa only using! inner_re_symm (𝕜:=ℂ) (embed (U f)) (embed (driftClock f))
  have hbound:(inner ℂ (embed (driftClock f)) (embed (U f))).re≤
      ‖embed (driftClock f)‖*‖embed (U f)‖:=by
    simpa only using! re_inner_le_norm (𝕜:=ℂ) (embed (driftClock f)) (embed (U f))
  have hsum:3*‖embed (U f)‖^2≤‖embed (driftClock f)‖*‖embed (U f)‖:=by
    linarith [hr,hs,hbound]
  by_cases hz:‖embed (U f)‖=0
  · rw [hz,mul_zero];exact norm_nonneg _
  · have hn:0<‖embed (U f)‖:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith
private theorem density_gain(e:ℝ)(f:QuantumTest)(z:SourceCoordinateSlice):
    densityPair (sourceGain e f) (sourceGain e f) z=
      ((gainProfile e z)^2:ℝ)*densityPair f f z:=by
  rw [densityPair_sum,densityPair_sum]
  change (∑word:Occupation,GaussDensityCore.complexDensity word.card z*
    star ((gainProfile e z:ℂ)*f z word)*((gainProfile e z:ℂ)*f z word))=
    (((gainProfile e z)^2:ℝ):ℂ)*(∑word:Occupation,GaussDensityCore.complexDensity word.card z*star (f z word)*f z word)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
  ring
private theorem density_inverse(f:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (U f) z=(reciprocalVolume z:ℂ)*densityPair f f z:=by
  rw [densityPair_sum,densityPair_sum]
  change (∑word:Occupation,GaussDensityCore.complexDensity word.card z*star (f z word)*
    ((reciprocalVolume z:ℂ)*f z word))=_
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring
private theorem density_self_nonneg(f:QuantumTest)(z:SourceCoordinateSlice):
    0≤RCLike.re (densityPair f f z):=by
  by_cases hz:z∈physicalChart
  · change 0≤RCLike.re (inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
      (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,le_refl]

private theorem actual_gain_norm(t:ℝ)(ht:0<t)(f:QuantumTest):
    ‖embed (sourceGain (Real.sqrt t) f)‖^2≤‖embed f‖^2+
      6*t*(sourcePair f (U f)).re:=by
  let G:=sourceGain (Real.sqrt t)
  have hp(z:SourceCoordinateSlice):RCLike.re (densityPair (G f) (G f) z)≤
      RCLike.re (densityPair f f z)+6*t*RCLike.re (densityPair f (U f) z):=by
    by_cases hz:z∈physicalChart
    · have hg:=SourceClockPhiCompleteHeatGainCoefficient.actual_complete_heat_gain_square_price t ht ⟨z,hz⟩
      have hn:=density_self_nonneg f z
      have h:=mul_le_mul_of_nonneg_right hg hn
      dsimp only [G]
      rw [density_gain,density_inverse]
      change (((((gainProfile (Real.sqrt t) z)^2:ℝ):ℂ)*densityPair f f z).re≤
        (densityPair f f z).re+6*t*((reciprocalVolume z:ℂ)*densityPair f f z).re)
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      simpa only [add_mul,one_mul,mul_assoc] using! h
    · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
      rw [show densityPair (G f) (G f) z=0 by dsimp only [G];rw [density_gain];simp only [densityPair,hf,map_zero,inner_zero_left,mul_zero]]
      rw [density_inverse]
      simp only [densityPair,hf,map_zero,inner_zero_left,mul_zero,add_zero,le_refl]
  have hL:Integrable (fun z=>RCLike.re (densityPair (G f) (G f) z)) GaussHistoryHilbert.configurationMeasure:=
    (densityPair_integrable (G f) (G f)).re (𝕜:=ℂ)
  have h0:Integrable (fun z=>RCLike.re (densityPair f f z)) GaussHistoryHilbert.configurationMeasure:=
    (densityPair_integrable f f).re (𝕜:=ℂ)
  have hU:Integrable (fun z=>RCLike.re (densityPair f (U f) z)) GaussHistoryHilbert.configurationMeasure:=
    (densityPair_integrable f (U f)).re (𝕜:=ℂ)
  have h:=integral_mono hL (h0.add (hU.const_mul (6*t))) hp
  rw [←GaussBoundedMultiplier.norm_square_integral] at h
  dsimp only [Pi.add_apply] at h
  rw [integral_add h0 (hU.const_mul (6*t)),←GaussBoundedMultiplier.norm_square_integral,integral_const_mul] at h
  have hu:(∫z,RCLike.re (densityPair f (U f) z) ∂GaussHistoryHilbert.configurationMeasure)=(sourcePair f (U f)).re:=by
    rw [integral_re (densityPair_integrable f (U f)),←sourcePair_integral]
    rfl
  rw [hu] at h
  exact h

private theorem actual_complete_heat_norm_square(t:ℝ)(ht:0<t)(ξ:ℝ)(f:QuantumTest):
    ‖embed (completeHeatCore t ht ξ f)‖^2≤‖embed f‖^2+
      2*t*‖embed (driftClock f)‖*‖embed f‖:=by
  change ‖embed (sourceHeatCore t ht ξ (sourceGain (Real.sqrt t) f))‖^2≤_
  rw [sourceHeat_norm]
  have hg:=actual_gain_norm t ht f
  have hu:=comparison_inverse_hardy f
  have hi:(sourcePair f (U f)).re≤‖embed f‖*‖embed (U f)‖:=by
    simpa only [sourcePair] using! re_inner_le_norm (𝕜:=ℂ) (embed f) (embed (U f))
  have hi':6*t*(sourcePair f (U f)).re≤6*t*(‖embed f‖*‖embed (U f)‖):=
    mul_le_mul_of_nonneg_left hi (by positivity)
  have hu':(2*t*‖embed f‖)*(3*‖embed (U f)‖)≤
      (2*t*‖embed f‖)*‖embed (driftClock f)‖:=
    mul_le_mul_of_nonneg_left hu (by positivity)
  nlinarith

theorem actual_complete_heat_gain_payment(t:ℝ)(ht:0<t)(η:ℝ)(hη:0<η)(ξ:ℝ)(f:QuantumTest):
    ‖embed (completeHeatCore t ht ξ f)‖^2≤
      η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+
        (1+t^2/η)*‖embed f‖^2:=by
  have hg:=actual_complete_heat_norm_square t ht ξ f
  let B:ℝ:=‖embed (driftClock f)‖
  let F:ℝ:=‖embed f‖
  have he:B^2≤SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f:=by
    change ‖embed (driftClock f)‖^2≤‖embed (driftClock f)‖^2+
      (1/2:ℝ)*‖embed ((inverseVolumeAction*combinedGenerator) f)‖^2
    exact le_add_of_nonneg_right (by positivity)
  have hy:2*t*B*F≤η*B^2+(t^2/η)*F^2:=by
    have ha:η*(η*B^2+(t^2/η)*F^2)=η^2*B^2+t^2*F^2:=by
      field_simp [hη.ne']
    have hb:η*(2*t*B*F)≤η*(η*B^2+(t^2/η)*F^2):=by
      rw [ha]
      nlinarith [sq_nonneg (η*B-t*F)]
    exact (mul_le_mul_iff_right₀ hη).mp hb
  have he':η*B^2≤η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f:=
    mul_le_mul_of_nonneg_left he hη.le
  change ‖embed (completeHeatCore t ht ξ f)‖^2≤η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+(1+t^2/η)*F^2
  change ‖embed (completeHeatCore t ht ξ f)‖^2≤F^2+2*t*B*F at hg
  nlinarith

end LowEnergy.SourceClockPhiCompleteHeatGainPayment
