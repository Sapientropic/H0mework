import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Feet
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance qbPriceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction
def actualNonPaPairBoundaryProgramme (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t - 1) * inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ) * OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c test t -
    OriginalRieszSource.Kernel.A c * actualNonPaPairSeedProgramme observation nontrivial half h t +
    OriginalRieszSource.Kernel.beta c * actualNonPaPairSeedProgramme observation nontrivial half h t

def actualNonPaSiblingBoundaryProgramme (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t - 1) * inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ) * OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c test t -
    OriginalRieszSource.Kernel.A c * actualNonPaSiblingSeedProgramme observation nontrivial half h t -
    OriginalRieszSource.Kernel.beta c * actualNonPaSiblingSeedProgramme observation nontrivial half h t

/-- Each QB boundary foot consumes all source-generated contact programmes while retaining its exact C velocity integral. -/
theorem actual_QB_boundary_programmes (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
      (Q (actualNonPaPairedR observation nontrivial half h)) t =
      actualNonPaPairBoundaryProgramme observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c
      (Q (actualNonPaSiblingR observation nontrivial half h)) t =
      actualNonPaSiblingBoundaryProgramme observation nontrivial half h t := by
  have source := actual_nonPa_four_source_contact_prices observation nontrivial half h nonnegative bounded t positive
  constructor
  · unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead actualNonPaPairBoundaryProgramme
    dsimp only
    rw [source.1,source.2.1]
  · unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead actualNonPaSiblingBoundaryProgramme
    dsimp only
    rw [source.2.2.1,source.2.2.2]
    ring

private theorem source_boundary_read_neg (test : BurnolPaAmbientCarrier) (t : ℝ) :
    OriginalKBoundarySourceAction.actualBoundaryIntegralRead c (-test) t =
      -OriginalKBoundarySourceAction.actualBoundaryIntegralRead c test t := by
  unfold OriginalKBoundarySourceAction.actualBoundaryIntegralRead OriginalKBoundarySourceAction.actualCorrectedVelocityPrice
    OriginalKBoundarySourceAction.actualSeedWindowPrice
  simp only [map_neg,Submodule.coe_neg,inner_neg_left,star_neg,intervalIntegral.integral_neg,mul_neg]
  ring

def actualQBSourceBoundaryPrice (h : ℝ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    (2*actualNonPaPairBoundaryProgramme observation nontrivial half h h) +
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) *
    star (2*actualNonPaSiblingBoundaryProgramme observation nontrivial half h h)

/-- The existing pure-nonPa Ward consumer now reads the actual generated four-foot QB source inventory. -/
theorem actual_nonPa_boundary_consumes_QB_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKNonPaSourceWardAction.actualNonPaBoundarySourcePrice observation nontrivial half h =
      actualQBSourceBoundaryPrice observation nontrivial half h := by
  have source := actual_QB_boundary_programmes observation nontrivial half h nonnegative bounded h nonnegative
  have feet := actual_nonPa_Q_fourier_feet observation nontrivial half h
  unfold OriginalKNonPaSourceWardAction.actualNonPaBoundarySourcePrice actualQBSourceBoundaryPrice
  dsimp only
  rw [feet.1,feet.2,source_boundary_read_neg observation nontrivial half,source.1,source.2]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
