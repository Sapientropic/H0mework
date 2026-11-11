import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Mean
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Tail OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ReciprocalMoment
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.RegularForward OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Reciprocal.Source
open scoped Topology
open private reciprocal_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
local notation "q" => (1/4:ℝ)
local notation "μplus" => volume.restrict (Ioi (0:ℝ))

private def tailPower (c:BurnolCompletedMellinCoordinate):ℝ→ℂ:=
  (Ioi q).indicator (fun x:ℝ=>(x:ℂ)^(star c.value-2))

private theorem tail_domain (c:BurnolCompletedMellinCoordinate):Integrable (tailPower c) μplus:=by
  have power:IntegrableOn (fun x:ℝ=>(x:ℂ)^(star c.value-2)) (Ioi q):=
    integrableOn_Ioi_cpow_of_lt (by change c.value.re-2 < -1;linarith [c.belowOne]) (by norm_num)
  exact (power.integrable_indicator measurableSet_Ioi).integrableOn

private theorem tail_mean (c:BurnolCompletedMellinCoordinate):
    (∫x:ℝ,tailPower c x ∂μplus)=-(q:ℂ)^(star c.value-1)/(star c.value-1):=by
  rw [tailPower,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤q)),
    integral_Ioi_cpow_of_lt (by change c.value.re-2 < -1;linarith [c.belowOne]) (by norm_num : (0:ℝ)<q),
    show star c.value-2+1=star c.value-1 by ring]

private theorem regular_domain (c:BurnolCompletedMellinCoordinate) (zero:riemannZeta c.value=0):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*regularCompactRaw c x) μplus:=by
  obtain ⟨L,nonnegative,growth⟩:=actual_regular_global_growth c zero
  exact (reciprocal_integrable (regularCompactRaw c) (actual_regular_measurable c) L nonnegative growth
    (actual_regular_outer_zero c)).integrableOn

private theorem joint_weighted_source (c:BurnolCompletedMellinCoordinate):
    (fun x:ℝ=>(x:ℂ)⁻¹*jointSourceRaw c x)=ᵐ[μplus]
      fun x:ℝ=>(x:ℂ)⁻¹*regularCompactRaw c x+(x:ℂ)⁻¹*dualFourierRaw c x-
        ForcingPrimitive.leadingCoefficient c*tailPower c x:=by
  filter_upwards [ae_restrict_of_ae (actual_joint_source_raw c),
    ae_restrict_of_ae (actual_joint_homogeneous_raw c),ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne q)] with x raw full positive notEndpoint
  change 0<x at positive
  have source:jointSourceRaw c x=quarterRaw c x+dualFourierRaw c x-
      ForcingPrimitive.leadingCoefficient c*(x:ℂ)^(star c.value-1):=by
    rw [raw] at full
    simpa only [abs_of_pos positive] using full
  by_cases inside:x<q
  · rw [source,quarterRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,inside.le⟩),
      actual_periodic_split c x positive,regularCompactRaw,
      indicator_of_mem (show x∈Ioo (-q) q from ⟨by linarith,inside⟩),regularLocal,
      abs_of_pos positive,min_eq_right inside.le,tailPower,
      indicator_of_notMem (show x∉Ioi q from not_lt.mpr inside.le),mul_zero]
    ring
  · have outside:q<x:=lt_of_le_of_ne (le_of_not_gt inside) (Ne.symm notEndpoint)
    rw [source,quarterRaw,indicator_of_notMem (show x∉symmetricInterval q from fun h=>not_lt.mpr h.2 outside),
      zero_add,actual_regular_outer_zero c x (by simpa only [abs_of_pos positive] using outside.le),
      mul_zero,zero_add,tailPower,indicator_of_mem (show x∈Ioi q from outside)]
    have powered:(x:ℂ)⁻¹*(x:ℂ)^(star c.value-1)=(x:ℂ)^(star c.value-2):=by
      rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
      congr 1
      ring
    rw [mul_sub,mul_left_comm _ (ForcingPrimitive.leadingCoefficient c),powered]

theorem actual_joint_reciprocal_integrable (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    Integrable (fun x:ℝ=>(x:ℂ)⁻¹*jointSourceRaw c x) μplus:=by
  have original:=((regular_domain c zero).add (actual_positive_reciprocal_integrable c)).sub
    ((tail_domain c).const_mul (ForcingPrimitive.leadingCoefficient c))
  apply original.congr
  exact (joint_weighted_source c).symm

/-- The original joint source pays its origin and exterior reciprocal contacts together. -/
theorem actual_joint_reciprocal_mean (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    jointReciprocalMean c=wholeReciprocalFinitePart c+dualReciprocalMean c:=by
  unfold jointReciprocalMean
  rw [integral_congr_ae (joint_weighted_source c)]
  have original:Integrable (fun x:ℝ=>(x:ℂ)⁻¹*regularCompactRaw c x+(x:ℂ)⁻¹*dualFourierRaw c x) μplus:=
    (regular_domain c zero).add (actual_positive_reciprocal_integrable c)
  rw [integral_sub original ((tail_domain c).const_mul _),
    integral_add (regular_domain c zero) (actual_positive_reciprocal_integrable c),
    integral_const_mul,actual_regular_mean,tail_mean]
  unfold wholeReciprocalFinitePart dualReciprocalMean
  ring

theorem actual_complete_joint_unit (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0):
    jointReciprocalMean c=wholeReciprocalFinitePart c-
      2*deriv (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Continuation.poleFreeSource c) 1/(1-star c.value):=by
  rw [actual_joint_reciprocal_mean c zero,actual_dual_reciprocal_mean c zero]
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Mean
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
