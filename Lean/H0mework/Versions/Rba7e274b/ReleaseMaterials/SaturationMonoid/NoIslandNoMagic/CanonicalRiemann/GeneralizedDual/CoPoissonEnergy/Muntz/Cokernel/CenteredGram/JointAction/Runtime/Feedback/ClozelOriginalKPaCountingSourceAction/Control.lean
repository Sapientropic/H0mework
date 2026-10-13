import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Source
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
local instance paCountingControlComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "q" => (1/4:ℝ)

def actualCountingCutoff (n:Nat):ℝ:=q*(1/2:ℝ)^n

/-- Actual source depths select a decreasing protected-origin cutoff in the same counting programme; they are not runtime events. -/
theorem actual_counting_cutoff_source (n:Nat):
 0≤actualCountingCutoff n ∧ actualCountingCutoff n≤q ∧
 actualCountingCutoff (n+1)≤actualCountingCutoff n :=by
 unfold actualCountingCutoff
 have decay:(1/2:ℝ)^n≤1:=pow_le_one₀ (by norm_num) (by norm_num)
 have nonnegative:(0:ℝ)≤(1/2:ℝ)^n:=by positivity
 refine ⟨by positivity,?_,?_⟩
 · exact (mul_le_mul_of_nonneg_left decay (by norm_num)).trans_eq (by ring)
 · rw [pow_succ]
   nlinarith

theorem actual_counting_cutoff_tendsto:
 Tendsto actualCountingCutoff atTop (𝓝 0) :=by
 unfold actualCountingCutoff
 simpa only [mul_zero] using
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).const_mul q

theorem actual_counting_source_error_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (fun n=>actualCountingSourceError c (actualCountingCutoff n)) atTop (𝓝 0) :=by
 have rate:0<c.value.re-1/2:=by linarith [c.rightHalf]
 have power:=((Real.continuous_rpow_const rate.le).tendsto (0:ℝ)).comp actual_counting_cutoff_tendsto
 rw [Real.zero_rpow rate.ne'] at power
 unfold actualCountingSourceError
 simpa only [mul_zero,zero_div,Function.comp_def] using (power.const_mul (‖c.value-1‖*‖burnolUnitCountingPrimitiveL2‖)).div_const (c.value.re-1/2)

/-- The full unit-tail counting material consumes its actual source-origin bound and existing scaling closure before Pa projection. -/
theorem actual_original_counting_source_tendsto (c:BurnolCompletedMellinCoordinate):
 Tendsto (fun n=>actualFiniteCountingUnitSource c (actualCountingCutoff n)) atTop (𝓝 (burnolUnitTailResponse c 4)) :=by
 apply tendsto_iff_norm_sub_tendsto_zero.mpr
 have source (n:Nat):‖burnolUnitTailResponse c 4-actualFiniteCountingUnitSource c (actualCountingCutoff n)‖≤
  actualCountingSourceError c (actualCountingCutoff n):=by
  rw [actual_original_counting_source_residual c _ (actual_counting_cutoff_source n).1 (actual_counting_cutoff_source n).2.1]
  exact actual_counting_origin_error c _ (actual_counting_cutoff_source n).1
 have controlled:=squeeze_zero (fun n=>norm_nonneg _) source (actual_counting_source_error_tendsto c)
 simpa only [norm_sub_rev] using controlled

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCountingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
