import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Price
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideQuarterSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance characterComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
open OriginalKWholePaSourceRankAction

def actualCvelSourceStockCharacter (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKNonPaSourceWardAction.actualWholePaUnitCrossPrice observation nontrivial half h +
    actualCvelBoundaryStockPrice observation nontrivial half h N +
    2*(observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaPairedR observation nontrivial half h)) (P (actualNonPaPairedR observation nontrivial half h)) +
    2*star (observation.coordinate/2-1/4)*inner ℂ
      (P (actualNonPaSiblingR observation nontrivial half h)) (P (actualNonPaSiblingR observation nontrivial half h)) +
    2*OriginalKOutsideQuarterSourceAction.actualOutsideQuarterFlux observation nontrivial half h

/-- The original Cross reads the finite endpoint-action stock and the complete source residual in the actual Ward body. -/
theorem actual_original_cross_consumes_Cvel_source_stock (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (N : ℕ) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualCvelSourceStockCharacter observation nontrivial half h N + actualCvelBoundaryTailPrice observation nontrivial half h N := by
  rw [OriginalKOutsideQuarterSourceAction.actual_original_cross_consumes_outside_quarter_source observation nontrivial half h nonnegative bounded]
  unfold OriginalKOutsideQuarterSourceAction.actualOutsideQuarterSourceCharacter actualCvelSourceStockCharacter
  rw [actual_QB_boundary_consumes_Cvel_stock]
  ring

theorem actual_current_consumes_Cvel_source_stock (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n N : ℕ) :
    OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n =
      actualCvelSourceStockCharacter observation nontrivial half h N + actualCvelBoundaryTailPrice observation nontrivial half h N := by
  rw [← actual_original_cross_consumes_Cvel_source_stock observation nontrivial half h nonnegative bounded N]
  exact (OriginalKWaveSourceAction.actual_original_cross_consumes_generated_wave_action
    observation nontrivial half h nonnegative bounded n).symm

theorem actual_current_Cvel_source_error_bound (h : ℝ) (nonnegative : 0 ≤ h)
    (bounded : h ≤ Real.log 2) (n N : ℕ) :
    ‖(OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative bounded n) -
        actualCvelSourceStockCharacter observation nontrivial half h N‖ ≤
      actualCvelTailBudget observation nontrivial half h * (1/4:ℝ)^N := by
  rw [actual_current_consumes_Cvel_source_stock observation nontrivial half h nonnegative bounded n N,add_sub_cancel_left]
  exact actual_Cvel_boundary_tail_bound observation nontrivial half h N

/-- The finite source stock itself generates the original Cross limit. -/
theorem actual_Cvel_source_stock_character_closure (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    Tendsto (actualCvelSourceStockCharacter observation nontrivial half h) atTop
      (𝓝 (OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h)) := by
  rw [OriginalKOutsideQuarterSourceAction.actual_original_cross_consumes_outside_quarter_source observation nontrivial half h nonnegative bounded]
  unfold actualCvelSourceStockCharacter OriginalKOutsideQuarterSourceAction.actualOutsideQuarterSourceCharacter
  exact ((((tendsto_const_nhds.add (actual_Cvel_boundary_stock_closure observation nontrivial half h)).add
    tendsto_const_nhds).add tendsto_const_nhds).add tendsto_const_nhds)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
