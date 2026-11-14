import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
import H0mework.Versions.R7e4da746.Arithmetic.RieszGreen.SourceIntegral
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalSameNArithmeticGreen
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "bRaw" => burnolRieszSingleFourierSourceRaw
local notation "b" => burnolRieszSingleFourierSource
local notation "C" => ConstantDual.seed

private theorem source_linear_origin (c:BurnolCompletedMellinCoordinate) :
    Tendsto (fun x:ℝ=>(x:ℂ)*star (bRaw c x)) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have actual:=(halfWeight_origin.mul (source_halfWeight_origin c).star).norm
  simp only [star_zero,mul_zero,norm_zero] at actual
  apply actual.congr
  intro x
  simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg |x|)]
  rw [←mul_assoc,←sq,Real.sq_sqrt (abs_nonneg x)]

private theorem source_linear_derivative (c:BurnolCompletedMellinCoordinate)
    (x:ℝ) (nonzero:x≠0) :
    HasDerivAt (fun y:ℝ=>(y:ℂ)*star (bRaw c y))
      (star (weightedRaw c x)+(1/2:ℂ)*star (bRaw c x)) x := by
  have actual:=Complex.ofRealCLM.hasDerivAt.mul (source_hasDerivAt c x nonzero).star
  convert! actual using 1
  simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,star_div₀,star_sub,star_mul,
    star_ofNat,star_one,star_div₀,Complex.star_def,Complex.conj_ofReal]
  field_simp [Complex.ofReal_ne_zero.mpr nonzero]
  ring

private theorem raw_integrable (v:Hq) (raw:ℝ→ℂ)
    (read:(v:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw) :
    IntegrableOn (fun x=>star (raw x)) (symmetricInterval q) := by
  apply (L2.integrable_inner (𝕜:=ℂ) v (intervalConstant q)).congr
  filter_upwards [read,intervalConstant_coeFn q] with x value unit
  rw [value,unit]
  simp [RCLike.inner_apply]

private theorem source_mass_green (c:BurnolCompletedMellinCoordinate)
    (r:ℝ) (positive:0<r) (bounded:r≤q) :
    (∫x:ℝ in (-r)..r,star (weightedRaw c x)+(1/2:ℂ)*star (bRaw c x))=
      (r:ℂ)*(star (bRaw c r)+star (bRaw c (-r))) := by
  let density:=fun x:ℝ=>star (weightedRaw c x)+(1/2:ℂ)*star (bRaw c x)
  let flux:=fun x:ℝ=>(x:ℂ)*star (bRaw c x)
  have full:IntegrableOn density (symmetricInterval q):=
    (raw_integrable (weightedState c) (weightedRaw c) (weightedState_read c)).add
      ((raw_integrable (b c:Hq) (bRaw c) (burnolRieszSingleFourierSource_ae_raw c)).const_mul (1/2:ℂ))
  have middle:IntervalIntegrable density volume (-r) r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -r≤r)]
    exact full.mono_set (Icc_subset_Icc (by linarith) bounded)
  have left:IntervalIntegrable density volume (-r) 0:=middle.mono_set (by
    rw [uIcc_of_le (by linarith : -r≤0),uIcc_of_le (by linarith : -r≤r)]
    exact Icc_subset_Icc le_rfl positive.le)
  have right:IntervalIntegrable density volume 0 r:=middle.mono_set (by
    rw [uIcc_of_le positive.le,uIcc_of_le (by linarith : -r≤r)]
    exact Icc_subset_Icc (by linarith) le_rfl)
  have continuous (x:ℝ) (nonzero:x≠0):ContinuousAt flux x:=
    Complex.continuous_ofReal.continuousAt.mul (burnolRieszSingleFourierSourceRaw_continuousAt c nonzero).star
  have negativeFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by linarith : -r<(0:ℝ))
    (fun x hx=>source_linear_derivative c x (by linarith [hx.2])) left
    ((continuous (-r) (by linarith)).tendsto.mono_left nhdsWithin_le_nhds)
    ((source_linear_origin c).mono_left nhdsWithin_le_nhds)
  have positiveFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto positive
    (fun x hx=>source_linear_derivative c x (by linarith [hx.1])) right
    ((source_linear_origin c).mono_left nhdsWithin_le_nhds)
    ((continuous r positive.ne').tendsto.mono_left nhdsWithin_le_nhds)
  change (∫x:ℝ in (-r)..r,density x)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals left right,negativeFTC,positiveFTC]
  dsimp [flux]
  push_cast
  ring

private theorem extension_raw (v:Hq) (raw:ℝ→ℂ)
    (read:(v:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw) :
    (E v:ℝ→ℂ)=ᵐ[volume] (symmetricInterval q).indicator raw := by
  have localRead:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp read
  filter_upwards [burnolQuarterZeroExtension_coe v,localRead] with x extension value
  rw [extension]
  by_cases inside:x∈symmetricInterval q
  · rw [indicator_of_mem inside,indicator_of_mem inside,value inside]
  · rw [indicator_of_notMem inside,indicator_of_notMem inside]

private theorem channel_seed_price (v:Hq) (raw:ℝ→ℂ)
    (read:(v:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)] raw)
    (a:ℝ) (positive:0<a) :
    inner ℂ (E v) (ContinuousChannels.channel 1 a C)=
      ∫x:ℝ in (-min q (q/a))..min q (q/a),star (raw x) := by
  let r:=min q (q/a)
  have rp:0<r:=lt_min (by norm_num) (div_pos (by norm_num) positive)
  have channel:=DualSourceRaw.channel_coeFn C ConstantDual.seedRaw ConstantDual.seed_coeFn a positive
  have actual:(fun x:ℝ=>inner ℂ ((E v) x) ((ContinuousChannels.channel 1 a C) x))=ᵐ[volume]
      (symmetricInterval r).indicator (fun x=>star (raw x)) := by
    filter_upwards [extension_raw v raw read,channel] with x extension seed
    rw [extension,seed]
    have incidence:(x∈symmetricInterval q ∧ |a*x|≤q) ↔ x∈symmetricInterval r := by
      rw [show x∈symmetricInterval q ↔ |x|≤q from abs_le.symm,
        show x∈symmetricInterval r ↔ |x|≤r from abs_le.symm,
        abs_mul,abs_of_pos positive,mul_comm a |x|,←le_div_iff₀ positive,le_min_iff]
    by_cases inside:x∈symmetricInterval r
    · obtain ⟨small,moved⟩:=incidence.mpr inside
      rw [indicator_of_mem small,ConstantDual.seedRaw,if_pos moved,indicator_of_mem inside]
      simp [RCLike.inner_apply]
    · rw [indicator_of_notMem inside]
      by_cases small:x∈symmetricInterval q
      · have outside:¬|a*x|≤q:=fun moved=>inside (incidence.mp ⟨small,moved⟩)
        rw [indicator_of_mem small,ConstantDual.seedRaw,if_neg outside]
        simp
      · rw [indicator_of_notMem small]
        simp
  rw [L2.inner_def,integral_congr_ae actual,integral_indicator (measurableSet_symmetricInterval r)]
  change (∫x:ℝ in Icc (-r) r,star (raw x))=_
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : -r≤r)]

private def sourceFunctional (c:BurnolCompletedMellinCoordinate) : BurnolL2→L[ℂ] ℂ :=
  innerSL ℂ (E (Euler.sourceEuler c:Hq))-(1/2:ℂ) • innerSL ℂ (E (b c:Hq))

def contact (c:BurnolCompletedMellinCoordinate) (a:ℝ) : ℂ :=
  let r:=min q (q/a)
  (r:ℂ)*(star (bRaw c r)+star (bRaw c (-r)))-
    (∫x:ℝ in (-r)..r,star (bRaw c x))-(2*r:ℝ)*star (Kernel.beta c)

/-- Both the source endpoint and its actual interval mean remain in each positive-scale contact. -/
theorem actual_unit_channel_green (c:BurnolCompletedMellinCoordinate) (a:ℝ) (positive:0<a) :
    sourceFunctional c (ContinuousChannels.channel 1 a C)=contact c a := by
  let r:=min q (q/a)
  have rp:0<r:=lt_min (by norm_num) (div_pos (by norm_num) positive)
  have rb:r≤q:=min_le_left _ _
  have br:IntegrableOn (fun x=>star (bRaw c x)) (symmetricInterval q):=
    raw_integrable (b c:Hq) (bRaw c) (burnolRieszSingleFourierSource_ae_raw c)
  have wr:IntegrableOn (fun x=>star (weightedRaw c x)) (symmetricInterval q):=
    raw_integrable (weightedState c) (weightedRaw c) (weightedState_read c)
  have bi:IntervalIntegrable (fun x=>star (bRaw c x)) volume (-r) r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -r≤r)]
    exact br.mono_set (Icc_subset_Icc (by linarith) rb)
  have wi:IntervalIntegrable (fun x=>star (weightedRaw c x)) volume (-r) r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -r≤r)]
    exact wr.mono_set (Icc_subset_Icc (by linarith) rb)
  have raw:(Euler.sourceEuler c:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]
      fun x=>weightedRaw c x-Kernel.beta c := by
    filter_upwards [Euler.sourceEuler_read c] with x value
    rw [value]
    unfold weightedRaw centeredRaw
    ring
  change inner ℂ (E (Euler.sourceEuler c:Hq)) (ContinuousChannels.channel 1 a C)-
    (1/2:ℂ)*inner ℂ (E (b c:Hq)) (ContinuousChannels.channel 1 a C)=_
  rw [channel_seed_price _ _ raw a positive,
    channel_seed_price _ _ (burnolRieszSingleFourierSource_ae_raw c) a positive]
  change (∫x:ℝ in (-r)..r,star (weightedRaw c x-Kernel.beta c))-
    (1/2:ℂ)*(∫x:ℝ in (-r)..r,star (bRaw c x))=contact c a
  simp_rw [star_sub]
  rw [intervalIntegral.integral_sub wi intervalIntegrable_const,intervalIntegral.integral_const]
  have source:=source_mass_green c r rp rb
  rw [intervalIntegral.integral_add wi (bi.const_mul (1/2:ℂ)),
    intervalIntegral.integral_const_mul] at source
  unfold contact
  change _=(r:ℂ)*(star (bRaw c r)+star (bRaw c (-r)))-
    (∫x:ℝ in (-r)..r,star (bRaw c x))-(2*r:ℝ)*star (Kernel.beta c)
  rw [Complex.real_smul]
  push_cast
  linear_combination source

def contactProgramme (c:BurnolCompletedMellinCoordinate) (N:ℕ) : ℂ :=
  (∑n∈Finset.Ico 1 N,contact c n)-∫a:ℝ in Ioc 0 (N:ℝ),contact c a

/-- The original finite reverse source pays the entire compensated Green programme at its own cutoff. -/
theorem actual_same_N_unit_green (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    sourceFunctional c (DualSource.source N C)=contactProgramme c N := by
  have continuousSource:=ContinuousChannels.channel_integrable 1 N C
  have integrable:=((sourceFunctional c).integrable_comp continuousSource)
  have same:(fun a:ℝ=>sourceFunctional c (ContinuousChannels.channel 1 a C))=ᵐ[volume.restrict (Ioc 0 (N:ℝ))]
      contact c := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a member
    exact actual_unit_channel_green c a member.1
  rw [DualSource.source,map_sub,map_sum,
    ←(sourceFunctional c).integral_comp_comm continuousSource,integral_congr_ae same]
  unfold contactProgramme
  congr 1
  exact Finset.sum_congr rfl (fun n member=>actual_unit_channel_green c n
    (by exact_mod_cast (Finset.mem_Ico.mp member).1))

/-- This strong source equation consumes both true Euler drives before the arithmetic limit. -/
theorem actual_same_N_B_unit_price (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    (c.value-1)*inner ℂ (E (b c:Hq)) (DualSource.source N C)+
      star (Kernel.A c)*inner ℂ Response.wholeU (DualSource.source N C)-
      star (Kernel.beta c)*inner ℂ Response.wholeV (DualSource.source N C)=contactProgramme c N := by
  have source:=actual_same_N_unit_green c N
  change inner ℂ (E (Euler.sourceEuler c:Hq)) (DualSource.source N C)-
    (1/2:ℂ)*inner ℂ (E (b c:Hq)) (DualSource.source N C)=_ at source
  rw [Euler.sourceEuler_eq] at source
  simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,
    inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply,star_div₀,
    star_ofNat,star_one,star_star] at source
  change ((c.value-(1/2:ℂ))*inner ℂ (E (b c:Hq)) (DualSource.source N C)+
    star (Kernel.A c)*inner ℂ Response.wholeU (DualSource.source N C)-
    star (Kernel.beta c)*inner ℂ Response.wholeV (DualSource.source N C))-
    (1/2:ℂ)*inner ℂ (E (b c:Hq)) (DualSource.source N C)=_ at source
  linear_combination source

/-- The original full Y source consumes the computed finite arithmetic effects together. -/
theorem actual_B_unit_green_tendsto (c:BurnolCompletedMellinCoordinate) :
    Tendsto (contactProgramme c) atTop
      (𝓝 ((c.value-1)*inner ℂ (E (b c:Hq)) ConstantDual.value+
        star (Kernel.A c)*inner ℂ Response.wholeU ConstantDual.value-
        star (Kernel.beta c)*inner ℂ Response.wholeV ConstantDual.value)) := by
  have actual:=((sourceFunctional c).continuous.tendsto _).comp ConstantDual.original_tendsto
  change Tendsto (fun N:ℕ=>sourceFunctional c (DualSource.source N C)) atTop _ at actual
  have input:(fun N:ℕ=>sourceFunctional c (DualSource.source N C))=contactProgramme c:=
    funext (actual_same_N_unit_green c)
  rw [input] at actual
  have output:sourceFunctional c ConstantDual.value=
      (c.value-1)*inner ℂ (E (b c:Hq)) ConstantDual.value+
        star (Kernel.A c)*inner ℂ Response.wholeU ConstantDual.value-
        star (Kernel.beta c)*inner ℂ Response.wholeV ConstantDual.value := by
    change inner ℂ (E (Euler.sourceEuler c:Hq)) ConstantDual.value-
      (1/2:ℂ)*inner ℂ (E (b c:Hq)) ConstantDual.value=_
    rw [Euler.sourceEuler_eq]
    simp only [Submodule.coe_add,Submodule.coe_sub,Submodule.coe_smul,map_add,map_sub,map_smul,
      inner_add_left,inner_sub_left,inner_smul_left,starRingEnd_apply,star_div₀,
      star_ofNat,star_one,star_star]
    change ((c.value-(1/2:ℂ))*inner ℂ (E (b c:Hq)) ConstantDual.value+
      star (Kernel.A c)*inner ℂ Response.wholeU ConstantDual.value-
      star (Kernel.beta c)*inner ℂ Response.wholeV ConstantDual.value)-
      (1/2:ℂ)*inner ℂ (E (b c:Hq)) ConstantDual.value=_
    ring
  rw [output] at actual
  exact actual

end OriginalSameNArithmeticGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
