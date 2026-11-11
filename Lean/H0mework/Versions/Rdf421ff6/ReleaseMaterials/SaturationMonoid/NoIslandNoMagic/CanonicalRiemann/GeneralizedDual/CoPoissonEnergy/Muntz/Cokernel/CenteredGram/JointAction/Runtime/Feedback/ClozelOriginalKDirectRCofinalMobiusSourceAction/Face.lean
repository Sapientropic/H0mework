import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMobiusSourceAction.Action
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalSourceAction.Consumer
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKDirectRCofinalMobiusSourceAction"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState CategoryTheory
open BurnolPhysicalState.OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
namespace Face
export OriginalKDirectRCofinalSourceAction
 (actualMaterial actualSourceHistory actualCofinalFace actualCofinalValue actualFaceImage
  actual_source_root actual_source_trace actual_whole_paid_trace actual_source_input
  actual_face_image_value actual_face_inverse_decoder actual_face_decoder
  actual_cofinal_window_read actual_cofinal_completion_source actual_source_point_from_packet)
namespace Window
export OriginalKDirectRCofinalSourceAction.Window (sourceDecoder inverseSourceDecoder)
end Window
end Face
local instance faceComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The input is decoded from this query n's actual cofinal value and generated image. -/
def actualQuerySource : BurnolL2 :=
 Face.Window.inverseSourceDecoder (Face.actualFaceImage observation nontrivial half depth ordinal)

def actualQueryTate : BurnolL2 := burnolTateReciprocalL2 (actualQuerySource observation nontrivial half depth ordinal)

def actualQueryCorrection : BurnolPaAmbientCarrier :=
 sourceVolterraPhysical (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal)

theorem actual_query_source :
 actualQuerySource observation nontrivial half depth ordinal=
 burnolMobiusSourceL2 (PA.actualPa observation nontrivial half depth ordinal) :=
 Face.actual_face_inverse_decoder observation nontrivial half depth ordinal

theorem actual_query_correction_native :
 actualQueryCorrection observation nontrivial half depth ordinal=generatedCorrection observation nontrivial half depth ordinal :=
 congrArg (fun input : BurnolL2=>sourceVolterraPhysical
  (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (burnolTateReciprocalL2 input))
  (actual_query_source observation nontrivial half depth ordinal)

theorem actual_query_correction_integral :
 actualQueryCorrection observation nontrivial half depth ordinal=
 ∫ u : ℝ in Icc (1/4:ℝ) 4,
  volterraSourceDensity (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
   (actualQueryTate observation nontrivial half depth ordinal) u •
  volterraPhysicalShell (burnolDivisionZeroCompletedMellinCoordinate observation half.down) u := rfl

theorem actual_query_correction_memPa :
 actualQueryCorrection observation nontrivial half depth ordinal ∈ burnolCompactCoPoissonClosedRange :=
 sourceVolterraPhysical_mem _ _

theorem actual_query_correction_Tate_source :
 burnolTateReciprocalL2 (burnolMobiusSourceL2 (actualQueryCorrection observation nontrivial half depth ordinal))=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal) := by
 have material:=congrArg (fun correction : BurnolPaAmbientCarrier=>burnolTateReciprocalL2 (burnolMobiusSourceL2 correction))
  (actual_query_correction_native observation nontrivial half depth ordinal)
 have source:=congrArg (fun input : BurnolL2=>sourceVolterraWindow
  (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (burnolTateReciprocalL2 input))
  (actual_query_source observation nontrivial half depth ordinal)
 exact (material.trans (generated_correction_Tate_source observation nontrivial half depth ordinal)).trans source.symm

theorem actual_query_correction_original :
 actualQueryCorrection observation nontrivial half depth ordinal=Prior.sourceCorrection observation nontrivial half depth ordinal :=
 (actual_query_correction_native observation nontrivial half depth ordinal).trans
  (generated_correction_original observation nontrivial half depth ordinal)

theorem actual_whole_successor_from_face :
 D.raw observation nontrivial half depth (ordinal+1)=
 (actualQueryCorrection observation nontrivial half depth ordinal : BurnolL2)+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)) :=
 (actual_whole_successor_from_source observation nontrivial half depth ordinal).trans
  (congrArg (fun correction : BurnolPaAmbientCarrier=>(correction : BurnolL2)+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
   P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))
   (actual_query_correction_native observation nontrivial half depth ordinal).symm)

theorem actual_Pa_successor_from_face :
 PA.actualPa observation nontrivial half depth (ordinal+1)=
 actualQueryCorrection observation nontrivial half depth ordinal+
 Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
 PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))) :=
 (actual_Pa_successor_from_source observation nontrivial half depth ordinal).trans
  (congrArg (fun correction : BurnolPaAmbientCarrier=>correction+
   Prior.sourceCoefficient observation nontrivial half depth ordinal • PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)+
   PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))))
   (actual_query_correction_native observation nontrivial half depth ordinal).symm)

/-- This is the decoded source at the actual next face; both E feet remain complete. -/
theorem actual_query_source_successor :
 actualQuerySource observation nontrivial half depth (ordinal+1)=
 burnolTateReciprocalL2
  (sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
   (actualQueryTate observation nontrivial half depth ordinal))+
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
 burnolMobiusSourceL2
  (PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))) := by
 have source:=congrArg (fun input : BurnolL2=>
  burnolTateReciprocalL2 (sourceVolterraWindow
   (burnolDivisionZeroCompletedMellinCoordinate observation half.down) (burnolTateReciprocalL2 input))+
  Prior.sourceCoefficient observation nontrivial half depth ordinal •
   burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2))+
  burnolMobiusSourceL2
   (PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal)))))
  (actual_query_source observation nontrivial half depth ordinal)
 exact ((actual_query_source observation nontrivial half depth (ordinal+1)).trans
  (actual_Mobius_source_successor_Volterra observation nontrivial half depth ordinal)).trans source.symm

theorem actual_query_Tate_successor :
 actualQueryTate observation nontrivial half depth (ordinal+1)=
 sourceVolterraWindow (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
  (actualQueryTate observation nontrivial half depth ordinal)+
 Prior.sourceCoefficient observation nontrivial half depth ordinal •
  burnolTateReciprocalL2 (burnolMobiusSourceL2 (PA.E (Prior.sourceWholeUnit observation nontrivial half : BurnolL2)))+
 burnolTateReciprocalL2 (burnolMobiusSourceL2
  (PA.E (P.R observation nontrivial half (PA.invisible (D.raw observation nontrivial half depth ordinal))))) := by
 have generated:=congrArg burnolTateReciprocalL2 (actual_query_source_successor observation nontrivial half depth ordinal)
 simpa only [actualQueryTate,map_add,map_smul,burnolTateReciprocalL2_involutive] using generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalMobiusSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
