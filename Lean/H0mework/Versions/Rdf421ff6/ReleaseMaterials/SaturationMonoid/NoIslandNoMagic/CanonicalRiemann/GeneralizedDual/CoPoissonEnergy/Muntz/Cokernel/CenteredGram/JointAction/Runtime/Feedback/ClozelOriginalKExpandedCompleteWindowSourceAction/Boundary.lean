import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedCompleteWindowSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local instance boundaryComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction

def actualCompleteWindowPairBoundaryProgramme (h : ℝ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value h-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualPairWindowCvelPrice observation nontrivial half h -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h h +
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h h

def actualCompleteWindowSiblingBoundaryProgramme (h : ℝ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value h-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualSiblingWindowCvelPrice observation nontrivial half h -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h h -
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h h

def actualCompleteWindowQBSourcePrice (h : ℝ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*(2*actualCompleteWindowPairBoundaryProgramme observation nontrivial half h) +
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*star (2*actualCompleteWindowSiblingBoundaryProgramme observation nontrivial half h)

/-- Original QB consumes complete finite source window vectors through the weighted expansion fields, retaining all contact, pole and C inventory. -/
theorem actual_QB_consumes_complete_window_source (h : ℝ) (nonnegative : 0 ≤ h) :
    OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice observation nontrivial half h =
      actualCompleteWindowQBSourcePrice observation nontrivial half h := by
  have source := actual_Cvel_consumes_complete_window_fields observation nontrivial half h nonnegative
  unfold OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice
    OriginalKQBSourceWindowAction.actualNonPaPairBoundaryProgramme OriginalKQBSourceWindowAction.actualNonPaSiblingBoundaryProgramme
    actualCompleteWindowQBSourcePrice actualCompleteWindowPairBoundaryProgramme actualCompleteWindowSiblingBoundaryProgramme
  dsimp only
  rw [source.1,source.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
