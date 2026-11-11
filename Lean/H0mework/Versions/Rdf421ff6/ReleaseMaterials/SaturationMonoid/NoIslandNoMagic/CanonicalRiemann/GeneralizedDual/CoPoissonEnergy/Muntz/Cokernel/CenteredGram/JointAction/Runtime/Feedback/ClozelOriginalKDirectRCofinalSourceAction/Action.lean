import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalSourceAction.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open CategoryTheory
open scoped InnerProductSpace Topology
namespace Window
export OriginalKPaWindowCofinalSourceCompletion (source_window_transition)
end Window
namespace Division
export OriginalKDirectRCofinalDivision (sourceCoefficient)
end Division

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- ordinal is original R time; stage is window radius. Window refinement generates no runtime tick. -/
theorem actual_window_source_successor (stage : Nat) :
 Window.windowRead stage (actualPaSource observation nontrivial half depth (ordinal+1))=
 Window.windowRead stage (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  Window.windowRead stage (wholeUnitSource observation nontrivial half)+
 Window.windowRead stage (reentrySource observation nontrivial half depth ordinal) := by
 have generated:=congrArg (Window.windowRead stage)
  (actual_source_successor observation nontrivial half depth ordinal)
 simpa only [map_add,map_smul] using generated

theorem actual_source_nu_successor :
 Window.sourceNu (actualPaSource observation nontrivial half depth (ordinal+1))=
 Window.sourceNu (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  Window.sourceNu (wholeUnitSource observation nontrivial half)+
 Window.sourceNu (reentrySource observation nontrivial half depth ordinal) := by
 have generated:=congrArg Window.sourceNu
  (actual_source_successor observation nontrivial half depth ordinal)
 simpa only [map_add,map_smul] using generated

theorem actual_window_transition_successor (stage : Nat) :
 Window.windowTransition stage
  (Window.windowRead (stage+1) (actualPaSource observation nontrivial half depth (ordinal+1)))=
 Window.windowRead stage (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  Window.windowRead stage (wholeUnitSource observation nontrivial half)+
 Window.windowRead stage (reentrySource observation nontrivial half depth ordinal) :=
 (Window.source_window_transition stage
  (actualPaSource observation nontrivial half depth (ordinal+1))).trans
  (actual_window_source_successor observation nontrivial half depth ordinal stage)

/-- All three generated Pa terms are acted on by the same original successor's cofinal face. -/
theorem actual_cofinal_source_successor :
 actualCofinalValue observation nontrivial half depth (ordinal+1)=
 (actualCofinalFace observation nontrivial half depth (ordinal+1)).completionMap
  (actualCofinalCalculation observation nontrivial half depth (ordinal+1))
  (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  (actualCofinalFace observation nontrivial half depth (ordinal+1)).completionMap
   (actualCofinalCalculation observation nontrivial half depth (ordinal+1))
   (wholeUnitSource observation nontrivial half)+
 (actualCofinalFace observation nontrivial half depth (ordinal+1)).completionMap
  (actualCofinalCalculation observation nontrivial half depth (ordinal+1))
  (reentrySource observation nontrivial half depth ordinal) := by
 have generated:=congrArg
  ((actualCofinalFace observation nontrivial half depth (ordinal+1)).completionMap
   (actualCofinalCalculation observation nontrivial half depth (ordinal+1)))
  (actual_source_successor observation nontrivial half depth ordinal)
 simpa only [actualCofinalValue,map_add,map_smul] using generated

theorem actual_completed_source_successor :
 actualCompletedSource observation nontrivial half depth (ordinal+1)=
 Window.completedSource (correctionSource observation nontrivial half depth ordinal)+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  Window.completedSource (wholeUnitSource observation nontrivial half)+
 Window.completedSource (reentrySource observation nontrivial half depth ordinal) := by
 have generated:=congrArg Window.sourceCompletionEquiv
  (actual_source_successor observation nontrivial half depth ordinal)
 simpa only [actualCompletedSource,Window.completedSource,map_add,map_smul] using generated

theorem actual_decoded_source_successor :
 Window.sourceDecoder (actualCompletedSource observation nontrivial half depth (ordinal+1))=
 correctionSource observation nontrivial half depth ordinal+
 Division.sourceCoefficient observation nontrivial half depth ordinal •
  wholeUnitSource observation nontrivial half+
 reentrySource observation nontrivial half depth ordinal :=
 (actual_completed_decoder observation nontrivial half depth (ordinal+1)).trans
  (actual_source_successor observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
