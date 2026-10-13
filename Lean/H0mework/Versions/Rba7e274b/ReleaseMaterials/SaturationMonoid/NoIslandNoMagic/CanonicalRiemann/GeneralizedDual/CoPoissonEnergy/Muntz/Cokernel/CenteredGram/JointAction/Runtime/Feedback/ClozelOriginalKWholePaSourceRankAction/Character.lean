import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Rank
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Inventory
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaCrossComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius

def actualOriginalCrossFactor (h : ℝ) : ℂ :=
  2*OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
    (pairedMellinTranslationCharacter observation.coordinate h - pairedMellinTranslationCharacter (star observation.coordinate) h)

def actualWholePaUnitPairPrice : ℂ :=
  inner ℂ (actualOriginalUnitPaPair observation nontrivial half)
    (burnolCompletedMellinRieszVector c + Fphysical (burnolCompletedMellinRieszVector c))
def actualWholePaUnitSiblingPrice : ℂ :=
  inner ℂ (burnolCompletedMellinRieszVector c - Fphysical (burnolCompletedMellinRieszVector c))
    (actualOriginalUnitPaSibling observation nontrivial half)

def actualNonPaPairKernelPrice (h : ℝ) : ℂ :=
  OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half (actualNonPaR observation nontrivial half h)
def actualNonPaSiblingKernelPrice (h : ℝ) : ℂ :=
  OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half (actualNonPaR observation nontrivial half h)

def actualWholePaRankSourceCharacter (h : ℝ) : ℂ :=
  actualOriginalCrossFactor observation h *
    (star (actualWholePaSourceCoefficient observation nontrivial half h / 2) *
        actualWholePaUnitPairPrice observation nontrivial half + actualNonPaPairKernelPrice observation nontrivial half h) +
  star (actualOriginalCrossFactor observation h) *
    ((actualWholePaSourceCoefficient observation nontrivial half h / 2) *
        actualWholePaUnitSiblingPrice observation nontrivial half + actualNonPaSiblingKernelPrice observation nontrivial half h)

/-- The independent original K/FK Cross reader consumes the full Pa source's generated ranks and the complete remaining nonPa response, in its original units. -/
theorem actual_original_cross_consumes_whole_Pa_rank_source (h : ℝ) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualWholePaRankSourceCharacter observation nontrivial half h := by
  have response := actual_whole_R_Pa_nonPa observation nontrivial half h
  have pairedRank := actual_whole_Pa_paired_source_rank observation nontrivial half h
  have siblingRank := actual_whole_Pa_sibling_source_rank observation nontrivial half h
  have pairedSplit : OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h =
      actualWholePaPairedR observation nontrivial half h + actualNonPaPairedR observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.pairedResponse
    rw [response]
    unfold actualWholePaPairedR actualNonPaPairedR OriginalKCombCofinalPaAction.paired
    rw [map_add]
    module
  have siblingSplit : OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h =
      actualWholePaSiblingR observation nontrivial half h + actualNonPaSiblingR observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.siblingResponse
    rw [response]
    unfold actualWholePaSiblingR actualNonPaSiblingR OriginalKCombCofinalPaAction.sibling
    rw [map_add]
    module
  unfold OriginalKPairedResponseGramAction.originalKernelCross actualWholePaRankSourceCharacter actualOriginalCrossFactor
    actualWholePaUnitPairPrice actualWholePaUnitSiblingPrice actualNonPaPairKernelPrice actualNonPaSiblingKernelPrice
    OriginalKPairedResponseGramAction.originalPairKernelRead OriginalKPairedResponseGramAction.originalSiblingKernelRead
  dsimp only
  rw [pairedSplit,siblingSplit,map_add,map_add,pairedRank,siblingRank]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,starRingEnd_apply]
  dsimp only [actualNonPaPairedR,actualNonPaSiblingR]
  ring

/-- The original current, with every existing residual, consumes the generated full-Pa rank character. -/
theorem actual_current_character_consumes_whole_Pa_rank_source (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
      actualWholePaRankSourceCharacter observation nontrivial half h := by
  have source := OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action observation nontrivial half h nonnegative bounded n
  rw [actual_original_cross_consumes_whole_Pa_rank_source observation nontrivial half h] at source
  exact source.symm

theorem actual_whole_Pa_rank_source_character_closure (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded)
      atTop (𝓝 (actualWholePaRankSourceCharacter observation nontrivial half h)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_consumes_whole_Pa_rank_source observation nontrivial half h] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
