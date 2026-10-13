import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWaveSourceAction.Character
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
open Complex MeasureTheory BurnolPhysicalState
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance sourcePhysicalAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "E" => OriginalKCombCofinalPaAction.E

/-- The original whole Pa stock consumes its actual source conservation before a flux price is read. -/
theorem actual_whole_Pa_source_action (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    E (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) =
    (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) •
      OriginalKPairedResponseGramAction.actualBoundaryPaStock observation nontrivial half h nonnegative bounded +
    OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded := by
  have source := OriginalKPairedResponseGramAction.actual_original_Pa_stock_conservation
    observation nontrivial half h nonnegative bounded
  exact sub_eq_iff_eq_add.mp source |>.trans (add_comm _ _)

local notation "P" => burnolEvenAmbientProjection

/-- The complete dependent physical face retains the original boundary, original K and the same-born Pa wave. -/
theorem actual_whole_physical_source_forcing (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) :
    P (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) =
    (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h) •
      OriginalKPairedResponseGramAction.BoundarySource.generatedBoundary
        (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded -
    (2 * OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h *
      (pairedMellinTranslationCharacter observation.coordinate h -
        pairedMellinTranslationCharacter (star observation.coordinate) h)) •
      burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) +
    OriginalCommonInverseForcing.SourceJoint.upperSourceWaveAmbient
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nonnegative bounded := by
  let coordinate := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  have whole := OriginalCommonInverseForcing.SourceJoint.FullStock.actual_whole_boundary_source
    coordinate observation.mathlibZero h nonnegative bounded
  rw [← OriginalKPairedResponseGramAction.BoundarySource.generated_boundary_realizes_original
    coordinate observation.mathlibZero h nonnegative bounded,
    OriginalKCombCofinalTwoDirection.coordinate_value] at whole
  rw [OriginalKFullSourceRResponse.actual_source_physical_restriction]
  linear_combination (norm := module) -whole

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholeWardSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
