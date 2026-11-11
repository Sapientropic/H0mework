import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.CoupledConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalReentrySourceAction.Physical
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
namespace Physical
export OriginalKDirectRCofinalReentrySourceAction
 (conjugate_F_unit_physical actual_beta_Q actual_next_outside_pair_zero actual_next_outside_reentry_zero)
end Physical
local instance physicalActionComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def actualQReentryPairing : ℂ :=
 inner ℂ (fourierL2 (burnolUnitTailResponse
  (OriginalPrimitiveRankBalance.conjugateCoordinate (burnolDivisionZeroCompletedMellinCoordinate observation half.down)) 4))
  (PA.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2)

theorem actual_reentry_pairing_Q :
 actualReentryPairing observation nontrivial half depth ordinal=actualQReentryPairing observation nontrivial half depth ordinal :=
 Physical.actual_beta_Q observation nontrivial half depth ordinal

theorem actual_query_Pa_physical :
 PA.actualPa observation nontrivial half depth (ordinal+1)=
 actualQueryCorrection observation nontrivial half depth ordinal+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 actualQReentryPairing observation nontrivial half depth ordinal • actualReentryVector observation half :=
 (actual_query_Pa_coupled observation nontrivial half depth ordinal).trans
  (congrArg (fun coefficient : ℂ=>actualQueryCorrection observation nontrivial half depth ordinal+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
   coefficient • actualReentryVector observation half)
   (actual_reentry_pairing_Q observation nontrivial half depth ordinal))

theorem actual_query_source_physical :
 actualQuerySource observation nontrivial half depth (ordinal+1)=
 burnolTateReciprocalL2 (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 actualQReentryPairing observation nontrivial half depth ordinal • burnolMobiusSourceL2 (actualReentryVector observation half) :=
 (actual_query_source_coupled observation nontrivial half depth ordinal).trans
  (congrArg (fun coefficient : ℂ=>burnolTateReciprocalL2 (sourceVolterraWindow
   (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal))+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
   coefficient • burnolMobiusSourceL2 (actualReentryVector observation half))
   (actual_reentry_pairing_Q observation nontrivial half depth ordinal))

theorem actual_query_Tate_physical :
 actualQueryTate observation nontrivial half depth (ordinal+1)=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal)+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolTateReciprocalL2
  (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
 actualQReentryPairing observation nontrivial half depth ordinal • burnolTateReciprocalL2
  (burnolMobiusSourceL2 (actualReentryVector observation half)) :=
 (actual_query_Tate_coupled observation nontrivial half depth ordinal).trans
  (congrArg (fun coefficient : ℂ=>sourceVolterraWindow
   (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (actualQueryTate observation nontrivial half depth ordinal)+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • burnolTateReciprocalL2
    (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
   coefficient • burnolTateReciprocalL2 (burnolMobiusSourceL2 (actualReentryVector observation half)))
   (actual_reentry_pairing_Q observation nontrivial half depth ordinal))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
