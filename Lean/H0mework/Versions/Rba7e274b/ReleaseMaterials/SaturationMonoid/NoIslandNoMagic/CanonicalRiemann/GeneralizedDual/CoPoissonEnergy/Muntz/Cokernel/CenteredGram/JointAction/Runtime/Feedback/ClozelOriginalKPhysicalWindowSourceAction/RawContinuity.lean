import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.PairedRaw

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance physicalRawComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


theorem actual_original_R_full_raw_continuousAt (h x : ℝ) (nonzero : x ≠ 0) :
    ContinuousAt (actualOriginalRWholeRaw observation nontrivial half h) x := by
  unfold actualOriginalRWholeRaw
  have native := (actual_original_R_raw_continuous observation nontrivial half h).continuousAt
    (Ioi_mem_nhds (abs_pos.mpr nonzero))
  exact native.comp continuous_abs.continuousAt

theorem actual_tate_fourier_R_full_raw_continuousAt (h x : ℝ) (nonzero : x ≠ 0) :
    ContinuousAt (actualTateFourierRWholeRaw observation nontrivial half h) x := by
  unfold actualTateFourierRWholeRaw
  have native := (actual_tate_fourier_R_raw_continuous observation nontrivial half h).continuousAt
    (Ioi_mem_nhds (abs_pos.mpr nonzero))
  exact native.comp continuous_abs.continuousAt

theorem actual_original_F_R_full_raw_continuousAt (h x : ℝ) (nonzero : x ≠ 0) :
    ContinuousAt (actualOriginalFourierRWholeRaw observation nontrivial half h) x := by
  unfold actualOriginalFourierRWholeRaw burnolTateReciprocalRaw
  have source := (actual_tate_fourier_R_full_raw_continuousAt observation nontrivial half h x⁻¹ (inv_ne_zero nonzero)).comp
    (continuousAt_id.inv₀ nonzero)
  have weight : ContinuousAt (fun x : ℝ => ((|x| : ℝ) : ℂ)⁻¹) x := by
    fun_prop (disch := exact_mod_cast (abs_pos.mpr nonzero).ne')
  exact weight.mul source

theorem actual_original_pair_sibling_raw_continuousAt (h x : ℝ) (nonzero : x ≠ 0) :
    ContinuousAt (actualOriginalPairedRWholeRaw observation nontrivial half h) x ∧
    ContinuousAt (actualOriginalSiblingRWholeRaw observation nontrivial half h) x := by
  have first := actual_original_R_full_raw_continuousAt observation nontrivial half h x nonzero
  have second := actual_original_F_R_full_raw_continuousAt observation nontrivial half h x nonzero
  exact ⟨(first.add second).const_mul (1 / 2 : ℂ), (first.sub second).const_mul (1 / 2 : ℂ)⟩


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
