import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.FourierMobiusReturn.RadialReturn
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
local instance physicalWindowComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualSourceMaterial (h : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.completeSource observation nontrivial half h

def actualOriginalRRaw (h x : ℝ) : ℂ :=
  -(2 : ℂ) * (x : ℂ)^(-observation.coordinate) *
    ∫ t : ℝ in Ioc 0 x, (t : ℂ)^(observation.coordinate-1) * actualSourceMaterial observation nontrivial half h t

/-- The already-generated actual original R material is read through the paid whole Bochner and radial source consumers. -/
theorem actual_original_R_source_raw (h : ℝ) :
    (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h) : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      actualOriginalRRaw observation nontrivial half h := by
  have source := ae_restrict_of_ae (s := Ioi (0 : ℝ))
    (OriginalFourierMobiusReturnSource.original_R_raw (OriginalKQuarterTailPhysicalSource.actualStarSource c) (actualSourceMaterial observation nontrivial half h))
  rw [OriginalKCombCofinalRAction.original_R_direct]
  filter_upwards [source, ae_restrict_mem measurableSet_Ioi] with x original positive
  change 0 < x at positive
  have actualRead : burnolDirectRightResolvent (observation.coordinate / 2)
      (actualSourceMaterial observation nontrivial half h) x =
      OriginalFourierMobiusReturnSource.actualReturnTimeRaw
        (OriginalKQuarterTailPhysicalSource.actualStarSource c)
        (actualSourceMaterial observation nontrivial half h) x := by
    simpa only [OriginalKQuarterTailPhysicalSource.actualStarSource, star_star,
      OriginalKCombCofinalTwoDirection.coordinate_value] using original

  rw [actualRead]
  have actual := OriginalFourierMobiusReturnSource.original_R_radial_time (OriginalKQuarterTailPhysicalSource.actualStarSource c)
    (actualSourceMaterial observation nontrivial half h) x positive
  simpa only [actualOriginalRRaw, OriginalFourierMobiusReturnSource.actualReturnTimeRaw, OriginalKQuarterTailPhysicalSource.actualStarSource, star_star,
    OriginalKCombCofinalTwoDirection.coordinate_value] using actual

/-- The existing physical source gap directly pays the smaller original negative window; the larger window is retained. -/
theorem actual_own_physical_negative_window (h : ℝ) (nonnegative : 0 ≤ h) (H : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation (-h)
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half H) : BurnolL2)) =
    (Real.exp (-h/2) : ℂ) * FiniteMobiusResolventFlux.actualMean
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half H) : BurnolL2) := by
  exact FiniteMobiusResolventFlux.actual_mean_source_negative
    (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half H)) (-h) (neg_nonpos.mpr nonnegative)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
