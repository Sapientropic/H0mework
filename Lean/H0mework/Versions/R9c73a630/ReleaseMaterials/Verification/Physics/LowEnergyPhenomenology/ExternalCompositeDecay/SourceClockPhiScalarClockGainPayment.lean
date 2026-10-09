import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarUncertaintyPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentJointBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn
open SourceClockPhiCorrectedWeightTransport ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiActualCovarianceStep SourceScalarInverseNativeEnergy MeasureTheory
open scoped InnerProductSpace ContDiff
private abbrev n : ℝ := sourceTime 0
private abbrev U := inverseVolumeAction
private abbrev K := correctedCompleteCore
private abbrev G (s:ℝ) := sourceGain (Real.sqrt s)
private abbrev config := GaussHistoryHilbert.configurationMeasure
attribute [local irreducible] embed sourcePair
private theorem complete_pair (s:ℝ)(hs:0<s)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (K s hs ξ η f) (K s hs ξ η g)=sourcePair (G s f) (G s g):=by
  change sourcePair
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (G s f)))
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η (G s g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem density_gain (s:ℝ)(f g:QuantumTest)(z:SourceCoordinateSlice):
    densityPair (G s f) (G s g) z=((gainProfile (Real.sqrt s) z)^2:ℝ)*densityPair f g z:=by
  rw [densityPair_sum,densityPair_sum]
  change (∑word:Occupation,GaussDensityCore.complexDensity word.card z*
    star ((gainProfile (Real.sqrt s) z:ℂ)*f z word)*((gainProfile (Real.sqrt s) z:ℂ)*g z word))=
    (((gainProfile (Real.sqrt s) z)^2:ℝ):ℂ)*(∑word:Occupation,GaussDensityCore.complexDensity word.card z*star (f z word)*g z word)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  simp only [star_mul,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
  ring
private theorem density_forward (s:ℝ)(hs:0<s)(f:QuantumTest)(z:SourceCoordinateSlice):
    densityPair f (forwardUAction s hs.le f) z=(forwardU s z:ℂ)*densityPair f f z:=
  inner_smul_right _ _ _
private theorem density_nonnegative (f:QuantumTest)(z:SourceCoordinateSlice):0 ≤ (densityPair f f z).re:=by
  by_cases hz:z∈physicalChart
  · have h:=GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
      (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    exact (sq_nonneg _).trans_eq h.symm
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem gain_mass_coefficient (c:ℝ)(hc:0≤c)(s:ℝ)(hs:0<s)
    (hbudget:18*s*c≤183*n)(z:physicalChart):
    gainProfile (Real.sqrt s) z.val^2*(c-183*n*forwardU s z.val)≤c:=by
  have hv:=volume_pos z
  have hr:=forward_ratio_pos s hs.le z
  have hr1:1≤forwardRatio s z.val:=by
    unfold forwardRatio
    rw [le_div_iff₀ hv]
    linarith
  have hg:gainProfile (Real.sqrt s) z.val^2=(forwardRatio s z.val)^(1/3:ℝ):=by
    unfold gainProfile
    rw [Real.sq_sqrt hs.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num
  have hp:(forwardRatio s z.val)^(1/3:ℝ)=(forwardRatio s z.val)^(-2/3:ℝ)*forwardRatio s z.val:=by
    calc
      _=(forwardRatio s z.val)^((-2/3:ℝ)+1):=by norm_num
      _=(forwardRatio s z.val)^(-2/3:ℝ)*(forwardRatio s z.val)^(1:ℝ):=Real.rpow_add hr _ _
      _=_:=by rw [Real.rpow_one]
  have hu:forwardU s z.val*forwardRatio s z.val=reciprocalVolume z.val:=by
    unfold forwardU forwardRatio reciprocalVolume
    have hw:volume z.val+18*s≠0:=by linarith
    field_simp [hv.ne',hw]
  have he:forwardRatio s z.val=1+18*s*reciprocalVolume z.val:=by
    unfold forwardRatio reciprocalVolume
    field_simp [hv.ne']
  have hq0:0≤(forwardRatio s z.val)^(-2/3:ℝ):=Real.rpow_nonneg hr.le _
  have hq1:(forwardRatio s z.val)^(-2/3:ℝ)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
  have hU:0≤reciprocalVolume z.val:=inv_nonneg.mpr hv.le
  have hinner:c+(18*s*c-183*n)*reciprocalVolume z.val≤c:=by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbudget) hU]
  rw [hg,hp]
  calc
    _=(forwardRatio s z.val)^(-2/3:ℝ)*(c*forwardRatio s z.val-183*n*(forwardU s z.val*forwardRatio s z.val)):=by ring
    _=(forwardRatio s z.val)^(-2/3:ℝ)*(c+(18*s*c-183*n)*reciprocalVolume z.val):=by rw [hu,he];ring
    _≤(forwardRatio s z.val)^(-2/3:ℝ)*c:=mul_le_mul_of_nonneg_left hinner hq0
    _≤c:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 hc

/-- The actual gain is paid by original U mass, uniformly in both noise coordinates.
The small clock condition depends only on the requested scalar norm coefficient. -/
theorem actual_corrected_scalar_gain_mass_payment (c:ℝ)(hc:0≤c)(s:ℝ)(hs:0<s)
    (hbudget:18*s*c≤183*n)(ξ η:ℝ)(w:QuantumTest):
    c*‖embed (K s hs ξ η w)‖^2-183*n*(sourcePair (K s hs ξ η w) (U (K s hs ξ η w))).re≤
      c*‖embed w‖^2:=by
  have hU:=LinearMap.congr_fun (actual_corrected_complete_inverse_volume s hs ξ η) w
  change U (K s hs ξ η w)=K s hs ξ η (forwardUAction s hs.le w) at hU
  have hn(q:QuantumTest):(sourcePair q q).re=‖embed q‖^2:=by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜:=ℂ) (embed q)
  have hnorm:‖embed (K s hs ξ η w)‖^2=‖embed (G s w)‖^2:=by
    rw [←hn,←hn,complete_pair]
  have hp(z:SourceCoordinateSlice):c*(densityPair (G s w) (G s w) z).re-
      183*n*(densityPair (G s w) (G s (forwardUAction s hs.le w)) z).re≤c*(densityPair w w z).re:=by
    rw [density_gain,density_gain,density_forward s hs]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    by_cases hz:z∈physicalChart
    · have h:=mul_le_mul_of_nonneg_right (gain_mass_coefficient c hc s hs hbudget ⟨z,hz⟩) (density_nonnegative w z)
      nlinarith only [h]
    · have hw:w z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (w.tsupport_subset h))
      simp only [densityPair,hw,map_zero,inner_zero_left,Complex.zero_re,mul_zero,sub_zero,le_refl]
  have hgg:Integrable (fun z=>(densityPair (G s w) (G s w) z).re) config:=(densityPair_integrable _ _).re
  have hgu:Integrable (fun z=>(densityPair (G s w) (G s (forwardUAction s hs.le w)) z).re) config:=(densityPair_integrable _ _).re
  have hww:Integrable (fun z=>(densityPair w w z).re) config:=(densityPair_integrable _ _).re
  have h:=integral_mono ((hgg.const_mul c).sub (hgu.const_mul (183*n))) (hww.const_mul c) hp
  erw [integral_sub (hgg.const_mul c) (hgu.const_mul (183*n)),integral_const_mul,integral_const_mul,integral_const_mul] at h
  have hi(f g:QuantumTest):(∫z:SourceCoordinateSlice,(densityPair f g z).re ∂config)=(sourcePair f g).re:=by
    change (∫z:SourceCoordinateSlice,RCLike.re (densityPair f g z) ∂config)=(sourcePair f g).re
    rw [integral_re (densityPair_integrable _ _),←sourcePair_integral]
    rfl
  rw [hi,hi,hi,hn,hn] at h
  rw [hnorm,hU,complete_pair]
  exact h

/-- The actual shifted source squares pay the full gain, leaving ten native rows' energy units
and three field-square units as signed debits on the updated state. -/
theorem actual_corrected_scalar_square_payment (c:ℝ)(hc:0≤c)(s:ℝ)(hs:0<s)
    (hbudget:18*s*c≤183*n)(ξ η:ℝ)(w:QuantumTest):
    let u:=K s hs ξ η w
    c*‖embed u‖^2-13*n*inverseNativeEnergy u-6*n*scalarPaymentSquare u≤
      c*‖embed w‖^2-10*n*inverseNativeEnergy u-3*n*scalarPaymentSquare u:=by
  dsimp only
  have hg:=actual_corrected_scalar_gain_mass_payment c hc s hs hbudget ξ η w
  have hd:=actual_scalar_payment_mass_debit (K s hs ξ η w)
  nlinarith only [hg,hd]
end LowEnergy.FirstCurrentJointBudget
