import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
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
local instance projectionPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualPhysicalPairedBoundaryRead (h t : ℝ) : ℂ :=
  let test := P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t - 1) * inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2 : ℂ) * OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c test t -
    OriginalRieszSource.Kernel.A c * actualPhysicalPairedGeneratedSeedPrice observation nontrivial half h t +
    OriginalRieszSource.Kernel.beta c * actualPhysicalPairedGeneratedSeedPrice observation nontrivial half h t

def actualPhysicalSiblingBoundaryRead (h t : ℝ) : ℂ :=
  let test := P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t - 1) * inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2 : ℂ) * OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c test t -
    OriginalRieszSource.Kernel.A c * actualPhysicalSiblingGeneratedSeedPrice observation nontrivial half h t -
    OriginalRieszSource.Kernel.beta c * actualPhysicalSiblingGeneratedSeedPrice observation nontrivial half h t

/-- Both original whole B cotests consume their actual expanding source profiles and all C velocity/mean contact fees. -/
theorem actual_boundary_integral_consumes_physical_windows (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (t : ℝ) (positive : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) t =
      actualPhysicalPairedBoundaryRead observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) t =
      actualPhysicalSiblingBoundaryRead observation nontrivial half h t := by
  have source := actual_physical_four_generated_contact_price observation nontrivial half h nonnegative bounded t positive
  constructor
  · unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead actualPhysicalPairedBoundaryRead
    dsimp only
    rw [source.1, source.2.1]
  · unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead actualPhysicalSiblingBoundaryRead
    dsimp only
    rw [source.2.2.1, source.2.2.2]
    ring

def actualPhysicalWindowFullBoundaryPrice (h : ℝ) : ℂ :=
  (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    (2 * actualPhysicalPairedBoundaryRead observation nontrivial half h h) +
  star (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    star (2 * actualPhysicalSiblingBoundaryRead observation nontrivial half h h)

/-- The literal complete original boundary inventory consumes all four source windows; Fourier signs arise from this same R occurrence. -/
theorem actual_full_boundary_consumes_physical_windows (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    OriginalKBoundarySourceAction.actualFullBoundarySourcePrice observation nontrivial half h =
      actualPhysicalWindowFullBoundaryPrice observation nontrivial half h := by
  have source := actual_boundary_integral_consumes_physical_windows observation nontrivial half h nonnegative bounded h nonnegative
  have feet := actual_physical_pair_sibling_fourier observation nontrivial half h nonnegative bounded
  have siblingNeg : OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
      (-(P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))) h =
      -OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
        (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) h := by
    unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead OriginalKBoundarySourceAction.actualCorrectedVelocityPrice
      OriginalKBoundarySourceAction.actualSeedWindowPrice
    simp only [map_neg, Submodule.coe_neg, inner_neg_left, star_neg,
      intervalIntegral.integral_neg, mul_neg]
    ring
  unfold OriginalKBoundarySourceAction.actualFullBoundarySourcePrice OriginalKBoundarySourceAction.actualFullBoundaryPairPrice
    OriginalKBoundarySourceAction.actualFullBoundarySiblingPrice actualPhysicalWindowFullBoundaryPrice
  dsimp only
  rw [feet.1, feet.2, siblingNeg, source.1, source.2]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
