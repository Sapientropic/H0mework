import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKOutsideQuarterSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance outsideQuarterSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction
local notation "O" => OriginalKPairedResponseGramAction.originalOutside

def actualOutsideQuarterSource (value : BurnolL2) :
    BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier :=
  burnolAmbientMeanZeroBlockRhs value

def actualOutsideQuarterProgramme (source : BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) : BurnolL2 :=
  burnolAmbientEvenPart
    (burnolQuarterZeroExtension (burnolMeanZeroBlockFirst source : BurnolQuarterIntervalL2) +
      fourierL2 (burnolQuarterZeroExtension (burnolMeanZeroBlockSecond source : BurnolQuarterIntervalL2)))

/-- The paid block inverse generates both correction feet from the complete source pair, before any Outside flux read. -/
theorem actual_quarter_source_block_equations (value : BurnolL2) :
    burnolMeanZeroBlockFirst (actualOutsideQuarterSource value) +
      burnolMeanZeroTruncatedFourier (burnolMeanZeroBlockSecond (actualOutsideQuarterSource value)) =
        (actualOutsideQuarterSource value).1 ∧
    burnolMeanZeroTruncatedFourier (burnolMeanZeroBlockFirst (actualOutsideQuarterSource value)) +
      burnolMeanZeroBlockSecond (actualOutsideQuarterSource value) =
        (actualOutsideQuarterSource value).2 :=
  ⟨burnolMeanZeroBlock_first_equation _,burnolMeanZeroBlock_second_equation _⟩

theorem original_even_outside_from_source (value : BurnolL2) (even : reflectL2 value = value) :
    O value = actualOutsideQuarterProgramme (actualOutsideQuarterSource value) := by
  have whole := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal value
  change (P value : BurnolL2) + O value = value at whole
  have physical := burnolEvenOrthogonalProjectionOnto_eq_resolventFormula value
  change (P value : BurnolL2) = _ at physical
  rw [physical] at whole
  unfold burnolAmbientExtendedSonineProjectionFormula burnolAmbientEvenPart at whole
  rw [even] at whole
  have fullEven : (1/2:ℂ) • (value+value) = value := by module
  rw [fullEven] at whole
  change value - actualOutsideQuarterProgramme (actualOutsideQuarterSource value) + O value = value at whole
  linear_combination (norm := module) whole

/-- The original actual full R profile pays the even source qualification; no qualification is transferred to an unrelated nonPa field. -/
theorem actual_original_R_outside_programme (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    O (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) =
      actualOutsideQuarterProgramme (actualOutsideQuarterSource
        (OriginalKFullSourceRResponse.Op.R observation nontrivial half
          (OriginalKFullSourceRResponse.completeSource observation nontrivial half h))) :=
  original_even_outside_from_source _
    (OriginalKPhysicalWindowSourceAction.actual_original_R_material_even observation nontrivial half h nonnegative bounded)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKOutsideQuarterSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
