import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideQuarterSourceAction.Gram
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
local instance outsideQuarterEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
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

def actualOutsideResponseSources (h : ℝ) :
    (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) ×
      (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) :=
  (actualOutsideQuarterSource (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h),
    actualOutsideQuarterSource (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))

def actualOutsideVelocitySources (h : ℝ) :
    (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) ×
      (BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier) :=
  (actualOutsideQuarterSource (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h),
    actualOutsideQuarterSource (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h))

/-- The original R strong action generates both velocities before their correction sources or Gram read. -/
theorem actual_original_R_quarter_source_actions (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
      (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2)
      (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
      (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h) 0 :=
  OriginalKFullSourceRResponse.actual_source_paired_response observation nontrivial half h

private theorem actual_full_R_four_source_even (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    reflectL2 (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) =
      OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h ∧
    reflectL2 (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) =
      OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h ∧
    reflectL2 (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h) =
      OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h ∧
    reflectL2 (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h) =
      OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h := by
  have evenR := OriginalKPhysicalWindowSourceAction.actual_original_R_material_even observation nontrivial half h nonnegative bounded
  have evenS := OriginalKPhysicalWindowSourceAction.actual_original_source_even observation nontrivial half h nonnegative bounded
  unfold OriginalKPhysicalWindowSourceAction.actualSourceMaterial at evenR evenS
  have evenFR : reflectL2 (fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
      (OriginalKFullSourceRResponse.completeSource observation nontrivial half h))) =
      fourierL2 (OriginalKFullSourceRResponse.Op.R observation nontrivial half
        (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) := by
    rw [←fourierL2_reflectL2_commute,evenR]
  have evenFS : reflectL2 (fourierL2 (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) =
      fourierL2 (OriginalKFullSourceRResponse.completeSource observation nontrivial half h) := by
    rw [←fourierL2_reflectL2_commute,evenS]
  have pair : reflectL2 (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) =
      OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.pairedResponse OriginalKCombCofinalPaAction.paired
    rw [map_smul,map_add,evenR,evenFR]
  have sibling : reflectL2 (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) =
      OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.siblingResponse OriginalKCombCofinalPaAction.sibling
    rw [map_smul,map_sub,evenR,evenFR]
  refine ⟨pair,sibling,?_,?_⟩
  · unfold OriginalKPairedResponseGramAction.pairedVelocity
    rw [map_add,map_smul,map_smul,map_sub,sibling,evenS,evenFS]
  · unfold OriginalKPairedResponseGramAction.siblingVelocity
    rw [map_add,map_smul,map_smul,map_add,pair,evenS,evenFS]

/-- The complete quartet of correction-source programmes is generated from the actual source fields after their strong action. -/
theorem actual_four_outside_source_programmes (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    O (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) =
      actualOutsideQuarterProgramme (actualOutsideResponseSources observation nontrivial half h).1 ∧
    O (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) =
      actualOutsideQuarterProgramme (actualOutsideResponseSources observation nontrivial half h).2 ∧
    O (OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h) =
      actualOutsideQuarterProgramme (actualOutsideVelocitySources observation nontrivial half h).1 ∧
    O (OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h) =
      actualOutsideQuarterProgramme (actualOutsideVelocitySources observation nontrivial half h).2 := by
  have qualifier := actual_full_R_four_source_even observation nontrivial half h nonnegative bounded
  exact ⟨original_even_outside_from_source _ qualifier.1,
    original_even_outside_from_source _ qualifier.2.1,
    original_even_outside_from_source _ qualifier.2.2.1,
    original_even_outside_from_source _ qualifier.2.2.2⟩

def actualOutsideQuarterFlux (h : ℝ) : ℂ :=
  actualQuarterSourceGram (actualOutsideResponseSources observation nontrivial half h).1
    (actualOutsideVelocitySources observation nontrivial half h).2 +
  actualQuarterSourceGram (actualOutsideVelocitySources observation nontrivial half h).1
    (actualOutsideResponseSources observation nontrivial half h).2

/-- The literal original Outside flux is generated by the source block quartet and its complete interval Gram. -/
theorem actual_original_outside_flux_from_quarter_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h =
      actualOutsideQuarterFlux observation nontrivial half h := by
  have source := actual_four_outside_source_programmes observation nontrivial half h nonnegative bounded
  unfold OriginalKPairedResponseGramAction.actualOutsideFlux actualOutsideQuarterFlux
  rw [source.1,source.2.1,source.2.2.1,source.2.2.2,
    actual_outside_quarter_source_Gram,actual_outside_quarter_source_Gram]

/-- Whole-Pa Division has already killed its own four Outside legs; this exact source quartet is the remaining nonPa flux. -/
theorem actual_nonPa_outside_flux_from_quarter_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualNonPaOutsideFlux observation nontrivial half h =
      actualOutsideQuarterFlux observation nontrivial half h := by
  rw [←actual_outside_flux_consumes_whole_Pa_source,
    actual_original_outside_flux_from_quarter_source observation nontrivial half h nonnegative bounded]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKOutsideQuarterSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
