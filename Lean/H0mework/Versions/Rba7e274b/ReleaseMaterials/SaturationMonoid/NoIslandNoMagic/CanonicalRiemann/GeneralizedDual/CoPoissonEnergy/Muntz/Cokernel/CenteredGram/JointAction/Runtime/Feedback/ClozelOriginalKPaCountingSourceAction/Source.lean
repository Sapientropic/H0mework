import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitivePhysicalSourceAction.Consumer
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance paCountingSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)
local notation "counting" => burnolUnitCountingPrimitiveL2

/-- The existing actual counting scale source acts as a whole L2 material before any Pa or target price read. -/
def actualCountingActor (c:BurnolCompletedMellinCoordinate) (u:ℝ):BurnolL2:=
 burnolUnitTailSlope c u • burnolSourceScalePrimitive counting u

/-- Actual head and the paid counting actor programme construct the finite protected-origin source; original unit-tail target is not an input. -/
def actualFiniteCountingUnitSource (c:BurnolCompletedMellinCoordinate) (lower:ℝ):BurnolL2:=
 burnolUnitPowerWeight c q • burnolSourceScalePrimitive counting q-
 ∫ u:ℝ in lower..q,actualCountingActor c u

def actualCountingOriginResidual (c:BurnolCompletedMellinCoordinate) (lower:ℝ):BurnolL2:=
 -(∫ u:ℝ in 0..lower,actualCountingActor c u)

/-- Existing source qualification pays the whole counting actor, including its protected origin. -/
theorem actual_counting_actor_integrable (c:BurnolCompletedMellinCoordinate) (upper:ℝ) (nonnegative:0≤upper):
 IntervalIntegrable (actualCountingActor c) volume 0 upper :=by
 rw [intervalIntegrable_iff_integrableOn_Ioc_of_le nonnegative]
 exact burnolUnitTailSlope_integrable c counting upper

/-- The actual cutoff source update consumes the new counting actor interval, not a target value or a reindexed receiver. -/
theorem actual_counting_source_update (c:BurnolCompletedMellinCoordinate)
 (first second:ℝ) (positive:0≤second) (ordered:second≤first) (bounded:first≤q):
 actualFiniteCountingUnitSource c second=actualFiniteCountingUnitSource c first-
 ∫ u:ℝ in second..first,actualCountingActor c u :=by
 have source:=actual_counting_actor_integrable c q (by norm_num)
 have left:=source.mono_set (show Set.uIcc second first⊆Set.uIcc 0 q by
  rw [Set.uIcc_of_le ordered,Set.uIcc_of_le (by norm_num : (0:ℝ)≤q)]
  intro u inside
  exact ⟨positive.trans inside.1,inside.2.trans bounded⟩)
 have right:=source.mono_set (show Set.uIcc first q⊆Set.uIcc 0 q by
  rw [Set.uIcc_of_le bounded,Set.uIcc_of_le (by norm_num : (0:ℝ)≤q)]
  intro u inside
  exact ⟨(positive.trans ordered).trans inside.1,inside.2⟩)
 have generated:=intervalIntegral.integral_add_adjacent_intervals left right
 unfold actualFiniteCountingUnitSource
 rw [←generated]
 module

/-- The actual complete original unit response consumes the full counting source programme and its exact lower-origin material. -/
theorem actual_original_counting_source_residual (c:BurnolCompletedMellinCoordinate)
 (lower:ℝ) (nonnegative:0≤lower) (bounded:lower≤q):
 burnolUnitTailResponse c 4-actualFiniteCountingUnitSource c lower=actualCountingOriginResidual c lower :=by
 have whole:=actual_counting_actor_integrable c q (by norm_num)
 have origin:=actual_counting_actor_integrable c lower nonnegative
 have rest:=whole.mono_set (show Set.uIcc lower q⊆Set.uIcc 0 q by
  rw [Set.uIcc_of_le bounded,Set.uIcc_of_le (by norm_num : (0:ℝ)≤q)]
  intro u inside
  exact ⟨nonnegative.trans inside.1,inside.2⟩)
 have generated:=intervalIntegral.integral_add_adjacent_intervals origin rest
 unfold burnolUnitTailResponse burnolUnitTailPrimitiveValue actualFiniteCountingUnitSource actualCountingOriginResidual
 rw [show (4:ℝ)⁻¹=q by norm_num]
 change burnolUnitPowerWeight c q • burnolSourceScalePrimitive counting q-
  (∫ u:ℝ in Set.Ioc 0 q,actualCountingActor c u)-
  (burnolUnitPowerWeight c q • burnolSourceScalePrimitive counting q-
   ∫ u:ℝ in lower..q,actualCountingActor c u)=_
 rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),←generated]
 module

def actualCountingSourceError (c:BurnolCompletedMellinCoordinate) (lower:ℝ):ℝ:=
 ‖c.value-1‖*‖counting‖*lower^(c.value.re-1/2)/(c.value.re-1/2)

/-- The same actual source scaling norm pays the full L2 origin error before physical projection; admitted rho alone pays the local real integration rate. -/
theorem actual_counting_origin_error (c:BurnolCompletedMellinCoordinate) (lower:ℝ) (nonnegative:0≤lower):
 ‖actualCountingOriginResidual c lower‖≤actualCountingSourceError c lower :=by
 unfold actualCountingOriginResidual
 rw [norm_neg]
 have exponent:-1<c.value.re-3/2:=by linarith [c.rightHalf]
 have source:=intervalIntegral.norm_integral_le_integral_norm nonnegative (f:=actualCountingActor c) (μ:=volume)
 have actual:(∫ u:ℝ in 0..lower,‖actualCountingActor c u‖)=actualCountingSourceError c lower :=by
  have actors:(∫ u:ℝ in 0..lower,‖actualCountingActor c u‖)=
   ∫ u:ℝ in 0..lower,‖c.value-1‖*u^(c.value.re-3/2)*‖counting‖:=by
   apply intervalIntegral.integral_congr_ae_restrict
   rw [Set.uIoc_of_le nonnegative]
   filter_upwards [ae_restrict_mem measurableSet_Ioc] with u inside
   unfold actualCountingActor
   exact burnolUnitTailSlope_norm c counting u inside.1
  rw [actors]
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
   integral_rpow (Or.inl exponent)]
  unfold actualCountingSourceError
  have rate:0<c.value.re-1/2:=by linarith [c.rightHalf]
  rw [show c.value.re-3/2+1=c.value.re-1/2 by ring,Real.zero_rpow rate.ne']
  ring
 exact source.trans_eq actual

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
