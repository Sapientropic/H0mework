import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set Filter
open BurnolPhysicalState
open scoped InnerProductSpace Topology
local notation "S" => burnolMeanZeroTruncatedFourier
local instance actionPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance quarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- Only the original interval mean-zero observation is used here, independently of physical P and Pa Q. -/
def quarterCotest (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto (burnolQuarterRestriction value)

def outsideCotest (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  quarterCotest (fourierL2.symm value)-(S).adjoint (quarterCotest value)

private theorem quarter_pair (test : BurnolL2) (state : BurnolQuarterMeanZeroCarrier) :
    inner ℂ test (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))=inner ℂ (quarterCotest test) state := by
  have actual := ContinuousLinearMap.adjoint_inner_right burnolQuarterRestriction test (state : BurnolQuarterIntervalL2)
  change inner ℂ test (burnolQuarterZeroExtension (state : BurnolQuarterIntervalL2))=
    inner ℂ (burnolQuarterRestriction test) (state : BurnolQuarterIntervalL2) at actual
  exact actual.trans (burnolQuarterMeanZeroClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right state _).symm

/-- Full-L2 inverse Fourier and the actual S-adjoint compute the complete outside source price. -/
theorem source_outside_pairing (coordinate : BurnolCompletedMellinCoordinate) (value test : BurnolL2) :
    inner ℂ test (sourceOutsideField coordinate value)=
      inner ℂ (outsideCotest test) (sourceOutsideColumn coordinate value) := by
  have Fourier := fourierL2.inner_map_map (fourierL2.symm test)
    (burnolQuarterZeroExtension (sourceOutsideColumn coordinate value : BurnolQuarterIntervalL2))
  rw [fourierL2.apply_symm_apply] at Fourier
  unfold sourceOutsideField outsideCotest
  rw [inner_sub_right,Fourier,quarter_pair,quarter_pair,inner_sub_left,ContinuousLinearMap.adjoint_inner_left]

namespace PA
export OriginalKCombCofinalPaAction (Q E invisible)
end PA
namespace P
export OriginalKCombPhysicalAction (R)
end P
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => OriginalKFullAdjointSource.sourceAdjointField c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "g" => sourceOutsideColumn c raw

/-- The actual born second inventory is tested by the previously generated whole H field. -/
theorem actual_born_outside_H_read :
    inner ℂ H (D.input observation nontrivial half depth (ordinal+1)).2=inner ℂ (outsideCotest H) g := by
  rw [actual_born_outside_source,source_outside_pairing]

private theorem actual_outside_slot :
    rawNext-(burnolEvenAmbientProjection rawNext : BurnolL2)=(D.input observation nontrivial half depth (ordinal+1)).2 := by
  have split := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal rawNext
  have native := congrArg (fun pair:BurnolL2×BurnolL2 => pair.2) (D.next_pair observation nontrivial half depth ordinal)
  rw [←D.raw_successor] at native
  change (D.input observation nontrivial half depth (ordinal+1)).2=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonal.starProjection rawNext at native
  rw [native]
  change rawNext-(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection rawNext=_
  linear_combination (norm:=module) -split

/-- The complete original invisible channel at n+1 consumes the new n-generated outside vector. -/
theorem actual_invisible_source_action :
    inner ℂ K (P.R observation nontrivial half (PA.invisible rawNext))=
      inner ℂ H (PA.Q rawNext : BurnolL2)+inner ℂ (outsideCotest H) g := by
  have actual := OriginalKFullAdjointSource.actual_invisible_source_read observation nontrivial half depth (ordinal+1)
  rw [actual_outside_slot,actual_born_outside_H_read] at actual
  exact actual

private theorem original_Q_normal
    (orthogonal : burnolCompletedMellinRieszVector c∈burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal)
    (value : BurnolL2) :
    inner ℂ K (PA.Q value : BurnolL2)=inner ℂ K value := by
  have pa := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.inner_orthogonalProjectionOnto_eq_of_mem_left
    ⟨burnolCompletedMellinRieszVector c,orthogonal⟩ (burnolEvenAmbientProjection value)
  have physical := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (burnolCompletedMellinRieszVector c) value
  exact pa.trans physical

/-- Division at the next original current consumes its complete Q return and the new outside vector price. -/
theorem actual_nextQ_source_action :
    inner ℂ K (PA.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2)=
      OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)*
        inner ℂ K (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)+
      inner ℂ H (PA.Q rawNext : BurnolL2)+inner ℂ (outsideCotest H) g := by
  have paid := OriginalKDirectRCofinalDivision.actual_original_K_read observation nontrivial half depth (ordinal+1)
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal c observation.mathlibZero
  have returned := original_Q_normal observation nontrivial half orthogonal
    (P.R observation nontrivial half (PA.invisible rawNext))
  change inner ℂ K (OriginalKDirectRCofinalDivision.sourceReturn observation nontrivial half depth (ordinal+1) : BurnolL2)=_ at returned
  change inner ℂ K (PA.Q (D.raw observation nontrivial half depth ((ordinal+1)+1)) : BurnolL2)=
    OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)*
      inner ℂ K (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)+
    inner ℂ K (OriginalKDirectRCofinalDivision.sourceReturn observation nontrivial half depth (ordinal+1) : BurnolL2) at paid
  rw [returned,actual_invisible_source_action] at paid
  simpa only [add_assoc] using paid

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
