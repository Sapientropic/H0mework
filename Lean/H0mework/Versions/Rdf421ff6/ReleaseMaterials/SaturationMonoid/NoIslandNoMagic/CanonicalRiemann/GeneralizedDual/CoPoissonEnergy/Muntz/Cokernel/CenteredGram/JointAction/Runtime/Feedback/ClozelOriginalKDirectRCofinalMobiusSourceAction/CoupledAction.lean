import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Source
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKDirectRCofinalMobiusSourceAction"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open BurnolPhysicalState.OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
namespace Reentry
export OriginalKDirectRCofinalReentrySourceAction
 (sourceReentryVector sourceReentryAction actual_reentry_generated full_pa_reentry_action)
end Reentry
namespace PA
export OriginalKCombCofinalPaAction (Q)
end PA
namespace D
export OriginalKCombFirstFullSourceDynamics (input)
end D
local instance coupledComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem reentry_action_apply (coordinate : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
 Reentry.sourceReentryAction coordinate input=
 inner ℂ (fourierL2 (burnolUnitTailResponse (OriginalPrimitiveRankBalance.conjugateCoordinate coordinate) 4)) input •
 (Reentry.sourceReentryVector coordinate : BurnolPaAmbientCarrier) := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def actualReentryVector : BurnolPaAmbientCarrier :=
 (Reentry.sourceReentryVector (burnolDivisionZeroCompletedMellinCoordinate observation half.down) : BurnolPaAmbientCarrier)

def actualReentryPairing : ℂ :=
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.invisible (D.raw observation nontrivial half depth ordinal))

theorem actual_reentry_vector_memPa : actualReentryVector observation half ∈ burnolCompactCoPoissonClosedRange :=
 (Reentry.sourceReentryVector (burnolDivisionZeroCompletedMellinCoordinate observation half.down)).property

/-- The entire original invisible input is retained in the generated unit pairing. -/
theorem actual_reentry_pairing :
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))=
 actualReentryPairing observation nontrivial half depth ordinal • actualReentryVector observation half :=
 (Reentry.actual_reentry_generated observation nontrivial half depth ordinal).trans (reentry_action_apply _ _)

/-- The actual next pairing contains both physical Q and the original outside-P inventory. -/
theorem actual_reentry_pairing_next_inventory :
 actualReentryPairing observation nontrivial half depth (ordinal+1)=
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (D.raw observation nontrivial half depth (ordinal+1)) : BurnolL2)+
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (D.input observation nontrivial half depth (ordinal+1)).2 := by
 have generated:=congrArg (fun input : BurnolL2=>inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4)) input)
  (OriginalKDirectRCofinalResidual.actual_residual_inventory observation nontrivial half depth ordinal)
 simpa only [actualReentryPairing,inner_add_right] using generated

theorem actual_query_Pa_coupled :
 PA.actualPa observation nontrivial half depth (ordinal+1)=
 actualQueryCorrection observation nontrivial half depth ordinal+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 actualReentryPairing observation nontrivial half depth ordinal • actualReentryVector observation half :=
 (actual_Pa_successor_from_face observation nontrivial half depth ordinal).trans
  (congrArg (fun returning : BurnolPaAmbientCarrier=>actualQueryCorrection observation nontrivial half depth ordinal+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+returning)
   (actual_reentry_pairing observation nontrivial half depth ordinal))

/-- Both complete Pa source feet are now generated explicitly beside the actual query Volterra action. -/
theorem actual_query_source_coupled :
 actualQuerySource observation nontrivial half depth (ordinal+1)=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 actualReentryPairing observation nontrivial half depth ordinal • burnolMobiusSourceL2 (actualReentryVector observation half) := by
 have returning:=congrArg (fun returning : BurnolPaAmbientCarrier=>
  burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
   (actualQueryTate observation nontrivial half depth ordinal))+
  Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
  burnolMobiusSourceL2 returning)
  (actual_reentry_pairing observation nontrivial half depth ordinal)
 exact (actual_query_source_successor observation nontrivial half depth ordinal).trans
  (by simpa only [map_smul] using returning)

theorem actual_query_Tate_coupled :
 actualQueryTate observation nontrivial half depth (ordinal+1)=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal)+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolTateReciprocalL2
  (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
 actualReentryPairing observation nontrivial half depth ordinal • burnolTateReciprocalL2
  (burnolMobiusSourceL2 (actualReentryVector observation half)) := by
 have generated:=congrArg burnolTateReciprocalL2 (actual_query_source_coupled observation nontrivial half depth ordinal)
 simpa only [actualQueryTate,map_add,map_smul,burnolTateReciprocalL2_involutive] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
