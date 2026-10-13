import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.FullRaw

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
local instance twinFullRawComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


theorem actual_tate_fourier_R_material_even (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    reflectL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h)) =
    OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h) := by
  let material := actualTateFourierSourceMaterial observation nontrivial half h
  have original := OriginalPaPhysicalGreen.sourceVolterraResolvent_reflect c (burnolTateReciprocalL2 material)
  have even : reflectL2 material = material := by
    dsimp only [material, actualTateFourierSourceMaterial]
    rw [← burnolTateReciprocal_reflect, ← fourierL2_reflectL2_commute,
      actual_original_source_even observation nontrivial half h nonnegative bounded]
  change reflectL2 (burnolTateReciprocalL2 (burnolDirectRightResolvent ((c).value/2)
    (burnolTateReciprocalL2 (burnolTateReciprocalL2 material)))) =
    burnolTateReciprocalL2 (burnolDirectRightResolvent ((c).value/2)
      (burnolTateReciprocalL2 (reflectL2 (burnolTateReciprocalL2 material)))) at original
  rw [burnolTateReciprocalL2_involutive, ← burnolTateReciprocal_reflect,
    ← burnolTateReciprocal_reflect, burnolTateReciprocalL2_involutive, even] at original
  have generated := congrArg burnolTateReciprocalL2 original
  rw [burnolTateReciprocalL2_involutive, burnolTateReciprocalL2_involutive] at generated
  simpa only [OriginalKCombCofinalRAction.original_R_direct,
    OriginalKCombCofinalTwoDirection.coordinate_value] using generated


def actualTateFourierRWholeRaw (h x : ℝ) : ℂ :=
  actualTateFourierRRaw observation nontrivial half h |x|

/-- Both real half-axes are the same already-generated even original R material, not independent receivers. -/
theorem actual_tate_fourier_R_full_source_raw (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h) : ℝ → ℂ) =ᵐ[volume]
      actualTateFourierRWholeRaw observation nontrivial half h := by
  let acted := OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (actualTateFourierSourceMaterial observation nontrivial half h)
  have halfRead := (ae_restrict_iff' measurableSet_Ioi).mp
    (actual_tate_fourier_R_source_raw observation nontrivial half h)
  have sourceEven := actual_tate_fourier_R_material_even observation nontrivial half h nonnegative bounded
  filter_upwards [halfRead, negMeasurePreserving.quasiMeasurePreserving.ae halfRead,
    Lp.coeFn_compMeasurePreserving acted negMeasurePreserving, volume.ae_ne (0 : ℝ)]
    with x positiveRead negativeRead reflected nonzero
  change acted x = _
  change reflectL2 acted x = acted (-x) at reflected
  rw [sourceEven] at reflected
  unfold actualTateFourierRWholeRaw
  by_cases positive : 0 < x
  · rw [abs_of_pos positive]
    exact positiveRead positive
  · have negative : x < 0 := lt_of_le_of_ne (le_of_not_gt positive) nonzero
    rw [abs_of_neg negative, reflected]
    exact negativeRead (neg_pos.mpr negative)


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
