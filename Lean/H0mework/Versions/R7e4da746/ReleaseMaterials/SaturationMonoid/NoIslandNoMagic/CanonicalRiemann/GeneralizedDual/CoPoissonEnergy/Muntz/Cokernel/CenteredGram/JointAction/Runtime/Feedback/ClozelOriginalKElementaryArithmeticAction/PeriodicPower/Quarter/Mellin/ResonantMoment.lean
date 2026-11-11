import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ResonantMoment
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Continuous
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Point OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.ReciprocalMean.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Clock
open scoped Topology InnerProductSpace
open private edgePrimitive_continuous from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ForcingTail
open private logSource_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Source
local notation "q" => (1/4:ℝ)
local notation "box" => burnolRadiusTruncatedFourierRaw q (intervalConstant q)

def weightedPeriodic (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  (x:ℂ)^(1-star c.value)*periodicRaw c x

private def regularPart (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  aliasRaw c x-jumpCoefficient c*box x-resolvedRaw c 0

private theorem weighted_split (c : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    weightedPeriodic c x=ForcingPrimitive.leadingCoefficient c+
      ForcingWhole.coefficient c*ForcingPrimitive.edgePrimitive c x+(x:ℂ)^(1-star c.value)*regularPart c x := by
  have actual:=ForcingPrimitive.weighted_forcing c x positive
  unfold weightedPeriodic periodicRaw resolvedFourierRaw regularPart
  linear_combination actual

private theorem weighted_derivative (c : BurnolCompletedMellinCoordinate) (x : ℝ) (inside : x∈Ioo (0:ℝ) q) :
    HasDerivAt (weightedPeriodic c) ((x:ℂ)^(-star c.value)*companionRaw c x) x := by
  have power:=burnolMellinTailPower_hasDerivAt (star c.value-1) inside.1
  have firstExponent:-(star c.value-1)=1-star c.value:=by ring
  have nextExponent:-(star c.value-1+1)= -star c.value:=by ring
  simp only [firstExponent,nextExponent] at power
  have source:=((actual_resolved_derivative c x inside.1.ne').add
    (actual_alias_derivative c x ⟨by linarith [inside.1],by linarith [inside.2]⟩)).sub_const (resolvedRaw c 0)
  have generated:=power.mul source
  have powerRead:(x:ℂ)^(1-star c.value)=(x:ℂ)^(-star c.value)*(x:ℂ) := by
    rw [show 1-star c.value= -star c.value+1 by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr inside.1.ne'),Complex.cpow_one]
  convert! generated using 1
  unfold companionRaw resolvedSlope
  rw [powerRead]
  unfold resolvedFourierRaw
  simp only [Pi.add_apply]
  field_simp [Complex.ofReal_ne_zero.mpr inside.1.ne']
  ring

private theorem origin_power (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x:ℝ=>(x:ℂ)^(1-star c.value)) (𝓝[>] 0) (𝓝 0) := by
  have positive:0<(1-star c.value).re := by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne]
  have nonzero:(1-star c.value:ℂ)≠0:=ne_of_apply_ne Complex.re positive.ne'
  have source:=(Complex.continuousAt_ofReal_cpow_const (0:ℝ) (1-star c.value) (Or.inl positive)).tendsto
  simpa only [Complex.ofReal_zero,Complex.zero_cpow nonzero] using source.mono_left nhdsWithin_le_nhds

private theorem regular_origin (c : BurnolCompletedMellinCoordinate) : ContinuousAt (regularPart c) 0 := by
  have aliases:ContinuousAt (aliasRaw c) 0 :=
    (actual_alias_raw_continuous c).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  exact (aliases.sub (continuousAt_const.mul
    (burnolRadiusTruncatedFourierRaw_continuous (intervalConstant q)).continuousAt)).sub continuousAt_const

theorem actual_weighted_origin (c : BurnolCompletedMellinCoordinate) :
    Tendsto (weightedPeriodic c) (𝓝[>] 0) (𝓝 (ForcingPrimitive.leadingCoefficient c)) := by
  have edge:Tendsto (ForcingPrimitive.edgePrimitive c) (𝓝[>] 0) (𝓝 0) := by
    have origin:Tendsto (ForcingPrimitive.edgePrimitive c) (𝓝[>] 0)
        (𝓝 (ForcingPrimitive.edgePrimitive c 0)) :=
      ((edgePrimitive_continuous c).continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [ForcingPrimitive.edgePrimitive,intervalIntegral.integral_same] using
      origin
  have regular:Tendsto (regularPart c) (𝓝[>] 0) (𝓝 (regularPart c 0)) :=
    (regular_origin c).tendsto.mono_left nhdsWithin_le_nhds
  have constant:Tendsto (fun _:ℝ=>ForcingPrimitive.leadingCoefficient c) (𝓝[>] 0)
      (𝓝 (ForcingPrimitive.leadingCoefficient c)):=tendsto_const_nhds
  have generated:=(constant.add (edge.const_mul (ForcingWhole.coefficient c))).add
    ((origin_power c).mul regular)
  simp only [mul_zero,zero_mul,add_zero] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with x positive
  exact (weighted_split c x positive).symm

private theorem weighted_endpoint (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    Tendsto (weightedPeriodic c) (𝓝[<] q) (𝓝 0) := by
  have regular:ContinuousAt (weightedPeriodic c) q :=
    (Complex.continuousAt_ofReal_cpow_const q (1-star c.value) (Or.inr (by norm_num))).mul
      (((actual_resolved_continuousAt c q (by norm_num)).add
        (actual_alias_derivative c q (by norm_num)).continuousAt).sub continuousAt_const)
  have source:weightedPeriodic c q=0 := by
    rw [weightedPeriodic,actual_original_periodic_zero_quarter c zero,mul_zero]
  rw [←source]
  exact regular.tendsto.mono_left nhdsWithin_le_nhds

private theorem moment_eq_interval (c : BurnolCompletedMellinCoordinate) :
    mellin (companionWholeRaw c) (1-star c.value)=
      ∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-star c.value)*companionRaw c x := by
  have exponent:1-star c.value-1= -star c.value:=by ring
  rw [mellin,exponent]
  have source:(fun x:ℝ=>(x:ℂ)^(-star c.value) • companionWholeRaw c x)=
      (symmetricInterval q).indicator (fun x:ℝ=>(x:ℂ)^(-star c.value)*companionRaw c x) := by
    funext x
    by_cases inside:x∈symmetricInterval q
    · rw [indicator_of_mem inside,companionWholeRaw,indicator_of_mem inside,smul_eq_mul]
    · rw [indicator_of_notMem inside,companionWholeRaw,indicator_of_notMem inside,smul_zero]
  rw [source,setIntegral_indicator (measurableSet_symmetricInterval q)]
  have same:Ioi (0:ℝ)∩symmetricInterval q=Ioc 0 q := by
    ext x
    simp only [mem_inter_iff,mem_Ioi,symmetricInterval,mem_Icc,mem_Ioc]
    constructor
    · rintro ⟨positive,_,upper⟩
      exact ⟨positive,upper⟩
    · rintro ⟨positive,upper⟩
      exact ⟨positive,by linarith,upper⟩
  rw [same,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q)]

private theorem moment_integrable (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    IntervalIntegrable (fun x:ℝ=>(x:ℂ)^(-star c.value)*companionRaw c x) volume 0 q := by
  have strip:-1<(1-star c.value).re := by simp only [sub_re,one_re,star_def,conj_re];linarith [c.belowOne]
  have source:=actual_companion_log_mellin c zero 0 (1-star c.value) strip
  rw [logSource_zero] at source
  have exponent:1-star c.value-1= -star c.value:=by ring
  change IntegrableOn (fun x:ℝ=>(x:ℂ)^(1-star c.value-1) • companionWholeRaw c x) (Ioi 0) at source
  rw [exponent] at source
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤q)]
  apply (source.mono_set Ioc_subset_Ioi_self).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  rw [companionWholeRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith [inside.1],inside.2⟩),smul_eq_mul]

/-- The original q zero pays the entire resonant companion moment, including the source's power head. -/
theorem actual_companion_resonant_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0) :
    mellin (companionWholeRaw c) (1-star c.value)= -ForcingPrimitive.leadingCoefficient c := by
  rw [moment_eq_interval]
  have actual:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num : (0:ℝ)<q)
    (weighted_derivative c) (moment_integrable c zero) (actual_weighted_origin c) (weighted_endpoint c zero)
  exact actual.trans (by rw [zero_sub])

theorem actual_difference_resonant_moment (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value=0)
    (h : ℝ) (nonnegative : 0≤h) :
    HasMellin (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.DirectBound.directRaw c h) (1-star c.value)
      (-(h:ℂ)*Complex.exp ((star c.value-1/2)*(h:ℂ))*ForcingPrimitive.leadingCoefficient c) := by
  have actual:=actual_resonant_mellin c zero h nonnegative
  rw [actual_companion_resonant_moment c zero] at actual
  convert! actual using 1
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ResonantMoment
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
