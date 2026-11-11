import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalRawWindowSourceAction.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedCompleteWindowSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance effectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
open OriginalKWholePaSourceRankAction OriginalKQBSourceWindowAction OriginalKExpandedCompleteWindowSourceAction
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualPairRawSourceWindow (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    BurnolRadiusIntervalL2 (radius t) :=
  actualPhysicalPairRawWindow observation nontrivial half h nonnegative bounded t -
    paSourceWindowProgramme (actualFullPairPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) • actualUnitPairWindowProgramme observation nontrivial half t

def actualSiblingRawSourceWindow (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    BurnolRadiusIntervalL2 (radius t) :=
  actualPhysicalSiblingRawWindow observation nontrivial half h nonnegative bounded t -
    paSourceWindowProgramme (actualFullSiblingPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) • actualUnitSiblingWindowProgramme observation nontrivial half t

theorem actual_raw_source_complete_window_programmes (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    actualNonPaPairWindowProgramme observation nontrivial half h t = actualPairRawSourceWindow observation nontrivial half h nonnegative bounded t ∧
    actualNonPaSiblingWindowProgramme observation nontrivial half h t = actualSiblingRawSourceWindow observation nontrivial half h nonnegative bounded t := by
  have source := actual_physical_source_raw_window_vectors observation nontrivial half h nonnegative bounded t
  unfold actualNonPaPairWindowProgramme actualNonPaSiblingWindowProgramme actualPairRawSourceWindow actualSiblingRawSourceWindow
  rw [source.1,source.2]
  exact ⟨rfl,rfl⟩

def actualPairRawSourceCotest (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  inner ℂ (actualPairRawSourceWindow observation nontrivial half h nonnegative bounded t) (actualExpandedQuarterWeight source t)
def actualSiblingRawSourceCotest (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  inner ℂ (actualSiblingRawSourceWindow observation nontrivial half h nonnegative bounded t) (actualExpandedQuarterWeight source t)

theorem actual_raw_source_window_weighted_effect (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (source : BurnolQuarterIntervalL2) (t : ℝ) :
    actualPairWindowSourceCotest observation nontrivial half h source t = actualPairRawSourceCotest observation nontrivial half h nonnegative bounded source t ∧
    actualSiblingWindowSourceCotest observation nontrivial half h source t = actualSiblingRawSourceCotest observation nontrivial half h nonnegative bounded source t := by
  have source := actual_raw_source_complete_window_programmes observation nontrivial half h nonnegative bounded t
  unfold actualPairWindowSourceCotest actualSiblingWindowSourceCotest actualPairRawSourceCotest actualSiblingRawSourceCotest
  rw [source.1,source.2]
  exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
