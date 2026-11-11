import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Projection
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance qbEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
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
/-- Both cotests are dependent projections of the original full R source; every Pa field remains in the exact split. -/
theorem actual_nonPa_Q_source_split (h : ℝ) :
    Q (actualNonPaPairedR observation nontrivial half h) =
      P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) -
      E (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) -
      (actualWholePaSourceCoefficient observation nontrivial half h/2) •
        actualOriginalUnitPaPair observation nontrivial half ∧
    Q (actualNonPaSiblingR observation nontrivial half h) =
      P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) -
      E (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) -
      (actualWholePaSourceCoefficient observation nontrivial half h/2) •
        actualOriginalUnitPaSibling observation nontrivial half := by
  have fields : OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h =
      actualWholePaPairedR observation nontrivial half h + actualNonPaPairedR observation nontrivial half h ∧
    OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h =
      actualWholePaSiblingR observation nontrivial half h + actualNonPaSiblingR observation nontrivial half h := by
    unfold OriginalKFullSourceRResponse.pairedResponse OriginalKFullSourceRResponse.siblingResponse
    rw [actual_whole_R_Pa_nonPa]
    unfold actualWholePaPairedR actualNonPaPairedR actualWholePaSiblingR actualNonPaSiblingR
      OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
    simp only [map_add]
    constructor <;> module
  have Qsplit (value : BurnolL2) : Q value = P value - E value := by
    have all := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P value)
    change E value + Q value = P value at all
    exact eq_sub_of_add_eq' all
  constructor
  · have projected := congrArg Q fields.1
    rw [map_add,actual_whole_Pa_paired_source_rank] at projected
    rw [←Qsplit]
    exact eq_sub_of_add_eq' projected.symm
  · have projected := congrArg Q fields.2
    rw [map_add,actual_whole_Pa_sibling_source_rank] at projected
    rw [←Qsplit]
    exact eq_sub_of_add_eq' projected.symm

/-- The positive moving means consume the actual full-source differential programme, the recovered Pa inventory and the original complete unit source programme. -/
theorem actual_nonPa_positive_mean_programmes (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 ≤ t) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2)) =
      actualNonPaPairMeanProgramme observation nontrivial half h t ∧
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2)) =
      actualNonPaSiblingMeanProgramme observation nontrivial half h t := by
  have full := OriginalKPhysicalWindowSourceAction.actual_physical_moving_window_read
    observation nontrivial half h nonnegative bounded t
  have action := OriginalKPhysicalWindowSourceAction.actual_physical_moving_window_finite_action
    observation nontrivial half h nonnegative bounded t positive
  rw [action.1,action.2] at full
  have unit := actual_unit_Pa_mean_programmes observation nontrivial half t
  have fields := actual_nonPa_Q_source_split observation nontrivial half h
  have pairPa := pa_source_window_read
    (E (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
    (Submodule.starProjection_apply_mem _ _) t
  have siblingPa := pa_source_window_read
    (E (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
    (Submodule.starProjection_apply_mem _ _) t
  constructor
  · rw [fields.1]
    change FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      ((P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2) -
      (E (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2) -
      (actualWholePaSourceCoefficient observation nontrivial half h/2) •
        (actualOriginalUnitPaPair observation nontrivial half : BurnolL2))) = _
    rw [map_sub,map_smul,map_sub,map_sub,map_smul,map_sub,full.1,
      pairPa,unit.2.1]
    rfl
  · rw [fields.2]
    change FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      ((P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2) -
      (E (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2) -
      (actualWholePaSourceCoefficient observation nontrivial half h/2) •
        (actualOriginalUnitPaSibling observation nontrivial half : BurnolL2))) = _
    rw [map_sub,map_smul,map_sub,map_sub,map_smul,map_sub,full.2,
      siblingPa,unit.2.2]
    rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
