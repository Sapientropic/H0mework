import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedCompleteWindowSourceAction.Effect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
open OriginalKWholePaSourceRankAction OriginalRieszSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualCoupledQuarterPlus : BurnolQuarterIntervalL2 := (Response.u : BurnolQuarterIntervalL2) + Response.v
def actualCoupledQuarterMinus : BurnolQuarterIntervalL2 := (Response.u : BurnolQuarterIntervalL2) - Response.v

def actualPairCompleteWindowSourcePrice (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualPairWindowSourceCotest observation nontrivial half h actualCoupledQuarterPlus t

def actualSiblingCompleteWindowSourcePrice (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualSiblingWindowSourceCotest observation nontrivial half h actualCoupledQuarterMinus t

/-- The complete field programmes pay the weighted U+V/U-V expansion integrals; scalar moving means are never substituted for these vectors. -/
theorem actual_complete_source_window_expanded_prices (h : ℝ) :
    OriginalKCvelCompressedSourceAction.actualExpandedSourceRead (Q (actualNonPaPairedR observation nontrivial half h))
      OriginalKCvelCompressedSourceAction.actualCoupledSourcePlus h = actualPairCompleteWindowSourcePrice observation nontrivial half h ∧
    OriginalKCvelCompressedSourceAction.actualExpandedSourceRead (Q (actualNonPaSiblingR observation nontrivial half h))
      OriginalKCvelCompressedSourceAction.actualCoupledSourceMinus h = actualSiblingCompleteWindowSourcePrice observation nontrivial half h := by
  have plus : burnolQuarterZeroExtension actualCoupledQuarterPlus = OriginalKCvelCompressedSourceAction.actualCoupledSourcePlus := by
    simp only [actualCoupledQuarterPlus,map_add,OriginalKCvelCompressedSourceAction.actualCoupledSourcePlus]
    rfl
  have minus : burnolQuarterZeroExtension actualCoupledQuarterMinus = OriginalKCvelCompressedSourceAction.actualCoupledSourceMinus := by
    simp only [actualCoupledQuarterMinus,map_sub,OriginalKCvelCompressedSourceAction.actualCoupledSourceMinus]
    rfl
  constructor
  · unfold OriginalKCvelCompressedSourceAction.actualExpandedSourceRead actualPairCompleteWindowSourcePrice
    rw [←plus]
    apply intervalIntegral.integral_congr
    intro t _
    exact actual_expanded_complete_window_source_prices observation nontrivial half h actualCoupledQuarterPlus t |>.1
  · unfold OriginalKCvelCompressedSourceAction.actualExpandedSourceRead actualSiblingCompleteWindowSourcePrice
    rw [←minus]
    apply intervalIntegral.integral_congr
    intro t _
    exact actual_expanded_complete_window_source_prices observation nontrivial half h actualCoupledQuarterMinus t |>.2

def actualPairWindowCvelPrice (h : ℝ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h +
    (Kernel.A c-Kernel.beta c)*actualPairCompleteWindowSourcePrice observation nontrivial half h

def actualSiblingWindowCvelPrice (h : ℝ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h -
    (Kernel.A c+Kernel.beta c)*actualSiblingCompleteWindowSourcePrice observation nontrivial half h

theorem actual_Cvel_consumes_complete_window_fields (h : ℝ) (nonnegative : 0 ≤ h) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h =
      actualPairWindowCvelPrice observation nontrivial half h ∧
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h =
      actualSiblingWindowCvelPrice observation nontrivial half h := by
  have source := OriginalKCvelCompressedSourceAction.actual_pair_sibling_Cvel_source_prices observation nontrivial half h h nonnegative
  have window := actual_complete_source_window_expanded_prices observation nontrivial half h
  constructor
  · rw [source.1]
    unfold OriginalKCvelCompressedSourceAction.actualPairCvelSourcePrice actualPairWindowCvelPrice
    dsimp only
    rw [window.1]
  · rw [source.2]
    unfold OriginalKCvelCompressedSourceAction.actualSiblingCvelSourcePrice actualSiblingWindowCvelPrice
    dsimp only
    rw [window.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
