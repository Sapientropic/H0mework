import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Regularity

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
local instance twinWindowComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


def actualTateFourierSourceMaterial (h : ℝ) : BurnolL2 :=
  burnolTateReciprocalL2 (fourierL2 (actualSourceMaterial observation nontrivial half h))

def actualTateFourierRRaw (h x : ℝ) : ℂ :=
  -(2 : ℂ) * (x : ℂ)^(-observation.coordinate) *
    ∫ t : ℝ in Ioc 0 x, (t : ℂ)^(observation.coordinate-1) * actualTateFourierSourceMaterial observation nontrivial half h t

/-- This is the Fourier face of the original R occurrence, transported by the already-paid true Tate conjugation. -/
theorem actual_original_F_R_source (h : ℝ) :
    fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h)) =
    burnolTateReciprocalL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h)) := by
  rw [OriginalKCombCofinalRAction.original_R_direct]
  rw [FiniteMobiusResolventFlux.fourier_R (observation.coordinate/2)
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)]
  rw [FiniteMobiusResolventFlux.Rplus_tate (observation.coordinate/2)
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half)]
  rfl

/-- The same original material's actual Tate/Fourier source is read through the existing radial primitive, before its physical face. -/
theorem actual_tate_fourier_R_source_raw (h : ℝ) :
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualTateFourierSourceMaterial observation nontrivial half h) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      actualTateFourierRRaw observation nontrivial half h := by
  have source := ae_restrict_of_ae (s := Ioi (0 : ℝ))
    (OriginalFourierMobiusReturnSource.original_R_raw (OriginalKQuarterTailPhysicalSource.actualStarSource c)
      (actualTateFourierSourceMaterial observation nontrivial half h))
  rw [OriginalKCombCofinalRAction.original_R_direct]
  filter_upwards [source, ae_restrict_mem measurableSet_Ioi] with x original positive
  change 0 < x at positive
  have actualRead : burnolDirectRightResolvent (observation.coordinate / 2)
      (actualTateFourierSourceMaterial observation nontrivial half h) x =
      OriginalFourierMobiusReturnSource.actualReturnTimeRaw
        (OriginalKQuarterTailPhysicalSource.actualStarSource c)
        (actualTateFourierSourceMaterial observation nontrivial half h) x := by
    simpa only [OriginalKQuarterTailPhysicalSource.actualStarSource, star_star,
      OriginalKCombCofinalTwoDirection.coordinate_value] using original
  rw [actualRead]
  have actual := OriginalFourierMobiusReturnSource.original_R_radial_time (OriginalKQuarterTailPhysicalSource.actualStarSource c)
    (actualTateFourierSourceMaterial observation nontrivial half h) x positive
  simpa only [actualTateFourierRRaw, OriginalFourierMobiusReturnSource.actualReturnTimeRaw,
    OriginalKQuarterTailPhysicalSource.actualStarSource, star_star,
    OriginalKCombCofinalTwoDirection.coordinate_value] using actual


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
