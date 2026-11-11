import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Feet
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
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

def actualCompressedPairBoundaryProgramme (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaPairedR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualPairCvelSourcePrice observation nontrivial half h t -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h t +
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaPairSeedProgramme observation nontrivial half h t

def actualCompressedSiblingBoundaryProgramme (h t : ℝ) : ℂ :=
  let test := Q (actualNonPaSiblingR observation nontrivial half h)
  (pairedMellinTranslationCharacter (c).value t-1)*inner ℂ test (burnolCompletedMellinRieszVector c) -
    (1/2:ℂ)*actualSiblingCvelSourcePrice observation nontrivial half h t -
    Kernel.A c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h t -
    Kernel.beta c*OriginalKQBSourceWindowAction.actualNonPaSiblingSeedProgramme observation nontrivial half h t

def actualCompressedQBSourcePrice (h : ℝ) : ℂ :=
  (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*(2*actualCompressedPairBoundaryProgramme observation nontrivial half h h) +
  star (2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h)*star (2*actualCompressedSiblingBoundaryProgramme observation nontrivial half h h)

/-- Original QB consumes the two complete expansion fields after source-generated compression, retaining all contact and C inventory. -/
theorem actual_QB_consumes_compressed_Cvel_source (h : ℝ) (nonnegative : 0 ≤ h) :
    OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice observation nontrivial half h =
      actualCompressedQBSourcePrice observation nontrivial half h := by
  have source := actual_pair_sibling_Cvel_source_prices observation nontrivial half h h nonnegative
  unfold OriginalKQBSourceWindowAction.actualQBSourceBoundaryPrice
    OriginalKQBSourceWindowAction.actualNonPaPairBoundaryProgramme OriginalKQBSourceWindowAction.actualNonPaSiblingBoundaryProgramme
    actualCompressedQBSourcePrice actualCompressedPairBoundaryProgramme actualCompressedSiblingBoundaryProgramme
  dsimp only
  rw [source.1,source.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
