import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Boundary
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local notation "P" => burnolEvenAmbientProjection
local instance characterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
open OriginalKWholePaSourceRankAction

def actualCorrectionStockSourceCharacter (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKNonPaSourceWardAction.actualWholePaUnitCrossPrice observation nontrivial half h +
    actualCorrectionStockQBPrice observation nontrivial half h N +
    2*(observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaPairedR observation nontrivial half h)) +
    2*star (observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaSiblingR observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) +
    2*OriginalKOutsideQuarterSourceAction.actualOutsideQuarterFlux observation nontrivial half h

/-- The original Cross reads the complete original source function integral fees after the physical raw source programme. -/
theorem actual_original_cross_consumes_correction_stock_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (N : ℕ) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualCorrectionStockSourceCharacter observation nontrivial half h N := by
  rw [OriginalKOutsideQuarterSourceAction.actual_original_cross_consumes_outside_quarter_source observation nontrivial half h nonnegative bounded]
  unfold OriginalKOutsideQuarterSourceAction.actualOutsideQuarterSourceCharacter actualCorrectionStockSourceCharacter
  rw [actual_QB_consumes_correction_stock_source observation nontrivial half h nonnegative bounded N]

theorem actual_current_consumes_correction_stock_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (n N : Nat) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
        actualCorrectionStockSourceCharacter observation nontrivial half h N := by
  rw [←actual_original_cross_consumes_correction_stock_source observation nontrivial half h nonnegative bounded N]
  exact (OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action observation nontrivial half h nonnegative bounded n).symm

theorem actual_correction_stock_source_closure (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (N : ℕ) :
    Tendsto (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded) atTop
      (𝓝 (actualCorrectionStockSourceCharacter observation nontrivial half h N)) := by
  have source := OriginalKWaveSourceAction.actual_original_band_source_character_closure observation nontrivial half h nonnegative bounded
  rw [actual_original_cross_consumes_correction_stock_source observation nontrivial half h nonnegative bounded N] at source
  exact source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
