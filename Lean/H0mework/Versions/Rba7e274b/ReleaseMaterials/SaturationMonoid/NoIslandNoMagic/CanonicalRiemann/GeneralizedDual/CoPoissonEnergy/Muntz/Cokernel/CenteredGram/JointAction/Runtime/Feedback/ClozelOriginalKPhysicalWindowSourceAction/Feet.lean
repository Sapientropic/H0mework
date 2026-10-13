import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Effect
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Feet
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
local instance projectionFeetComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

/-- The two Fourier feet are restrictions of the same actual even R response, with their source-generated signs. -/
theorem actual_physical_pair_sibling_fourier (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Fphysical (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) =
      P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) ∧
    Fphysical (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) =
      -(P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) := by
  have even := actual_original_R_material_even observation nontrivial half h nonnegative bounded
  have pairSource : fourierL2 (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) =
      OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.pairedResponse OriginalKCombCofinalPaAction.paired
    rw [map_smul, map_add, fourierL2_fourierL2]
    change (1/2 : ℂ) • (fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h)) +
      reflectL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualSourceMaterial observation nontrivial half h))) = _
    rw [even, add_comm]
    rfl
  have siblingSource : fourierL2 (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) =
      -(OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) := by
    unfold OriginalKFullSourceRResponse.siblingResponse OriginalKCombCofinalPaAction.sibling
    rw [map_smul, map_sub, fourierL2_fourierL2]
    change (1/2 : ℂ) • (fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (actualSourceMaterial observation nontrivial half h)) -
      reflectL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualSourceMaterial observation nontrivial half h))) = _
    rw [even]
    dsimp only [actualSourceMaterial]
    module
  constructor
  · apply Subtype.ext
    change fourierL2 (evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius
      (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) = _
    rw [fourierL2_evenBurnolPhysicalProjection, pairSource]
    rfl
  · apply Subtype.ext
    change fourierL2 (evenBurnolPhysicalProjection burnolUnscaledCommonGapRadius
      (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) = _
    rw [fourierL2_evenBurnolPhysicalProjection, siblingSource, map_neg]
    rfl

private theorem seed_window_price_neg (test : BurnolPaAmbientCarrier) (t : ℝ) :
    OriginalKBoundarySourceAction.actualSeedWindowPrice (-test) t =
      -OriginalKBoundarySourceAction.actualSeedWindowPrice test t := by
  unfold OriginalKBoundarySourceAction.actualSeedWindowPrice
  simp only [Submodule.coe_neg, map_neg, star_neg]
  ring

/-- All four physical/Fourier contact prices consume the actual source annulus and its negative gap action. -/
theorem actual_physical_four_contact_window_price (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) t =
      actualPhysicalPairedSeedPrice observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (Fphysical (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))) t =
      actualPhysicalPairedSeedPrice observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) t =
      actualPhysicalSiblingSeedPrice observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (Fphysical (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))) t =
      -actualPhysicalSiblingSeedPrice observation nontrivial half h t := by
  have feet := actual_physical_pair_sibling_fourier observation nontrivial half h nonnegative bounded
  have source := actual_physical_seed_window_price observation nontrivial half h nonnegative bounded t positive
  refine ⟨source.1, ?_, source.2, ?_⟩
  · rw [feet.1]
    exact source.1
  · rw [feet.2, seed_window_price_neg, source.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
