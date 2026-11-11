import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalRawWindowSourceAction.Price
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
local instance cvelComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
open OriginalKWholePaSourceRankAction OriginalKExpandedCompleteWindowSourceAction OriginalRieszSource
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualPairRawSourceIntegralFee (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualPairRawSourceWeightedFee observation nontrivial half h actualCoupledQuarterPlus t

def actualSiblingRawSourceIntegralFee (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualSiblingRawSourceWeightedFee observation nontrivial half h actualCoupledQuarterMinus t

theorem actual_original_source_expanded_raw_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    actualPairCompleteWindowSourcePrice observation nontrivial half h = actualPairRawSourceIntegralFee observation nontrivial half h ∧
    actualSiblingCompleteWindowSourcePrice observation nontrivial half h = actualSiblingRawSourceIntegralFee observation nontrivial half h := by
  constructor
  · unfold actualPairCompleteWindowSourcePrice actualPairRawSourceIntegralFee
    apply intervalIntegral.integral_congr
    intro t _
    exact actual_raw_source_weighted_complete_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterPlus t |>.1
  · unfold actualSiblingCompleteWindowSourcePrice actualSiblingRawSourceIntegralFee
    apply intervalIntegral.integral_congr
    intro t _
    exact actual_raw_source_weighted_complete_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterMinus t |>.2

def actualPairRawCvelSourcePrice (h : ℝ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h +
    (Kernel.A c-Kernel.beta c)*actualPairRawSourceIntegralFee observation nontrivial half h

def actualSiblingRawCvelSourcePrice (h : ℝ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h -
    (Kernel.A c+Kernel.beta c)*actualSiblingRawSourceIntegralFee observation nontrivial half h

theorem actual_Cvel_consumes_original_raw_source_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h =
      actualPairRawCvelSourcePrice observation nontrivial half h ∧
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h =
      actualSiblingRawCvelSourcePrice observation nontrivial half h := by
  have source := actual_Cvel_consumes_complete_window_fields observation nontrivial half h nonnegative
  have raw := actual_original_source_expanded_raw_fees observation nontrivial half h nonnegative bounded
  constructor
  · rw [source.1]
    unfold actualPairWindowCvelPrice actualPairRawCvelSourcePrice
    rw [raw.1]
  · rw [source.2]
    unfold actualSiblingWindowCvelPrice actualSiblingRawCvelSourcePrice
    rw [raw.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
