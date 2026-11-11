import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Price
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalKPhysicalRawWindowSourceAction OriginalKExpandedCompleteWindowSourceAction OriginalKWholePaSourceRankAction OriginalRieszSource
local instance cvelComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q

def actualPairCorrectionStockIntegralFee (h : ℝ) (N : ℕ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualPairCorrectionStockWeightedFee observation nontrivial half h actualCoupledQuarterPlus t N

def actualSiblingCorrectionStockIntegralFee (h : ℝ) (N : ℕ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualSiblingCorrectionStockWeightedFee observation nontrivial half h actualCoupledQuarterMinus t N

def actualPairCorrectionTailIntegralFee (h : ℝ) (N : ℕ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualPairCorrectionTailWeightedFee observation nontrivial half h actualCoupledQuarterPlus t N

def actualSiblingCorrectionTailIntegralFee (h : ℝ) (N : ℕ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, actualSiblingCorrectionTailWeightedFee observation nontrivial half h actualCoupledQuarterMinus t N

private theorem correction_tail_integrable (value : BurnolL2) (source : BurnolQuarterIntervalL2) (h : ℝ) (N : ℕ) :
    IntervalIntegrable (fun t : ℝ => inner ℂ (burnolRadiusRestriction ((1/4:ℝ)*Real.exp t) (actualPhysicalCorrectionTail value N))
      (actualExpandedQuarterWeight source t)) volume 0 h := by
  have sourceAction := (burnolMultiplicativeDilation_stronglyContinuous (burnolQuarterZeroExtension source)).comp continuous_neg
  have price := (continuous_const : Continuous (fun _ : ℝ => actualPhysicalCorrectionTail value N)).inner (𝕜 := ℂ) sourceAction
  have actual := price.intervalIntegrable (μ := volume) 0 h
  have equation := fun t : ℝ => actual_complete_window_weighted_cotest (actualPhysicalCorrectionTail value N) source t
  simpa only [Function.comp_apply,equation] using actual

private theorem correction_stock_integrable (value : BurnolL2) (source : BurnolQuarterIntervalL2) (h : ℝ) (N : ℕ) :
    IntervalIntegrable (fun t : ℝ => inner ℂ (burnolRadiusRestriction ((1/4:ℝ)*Real.exp t) (actualPhysicalProjectionStock value N))
      (actualExpandedQuarterWeight source t)) volume 0 h := by
  have sourceAction := (burnolMultiplicativeDilation_stronglyContinuous (burnolQuarterZeroExtension source)).comp continuous_neg
  have price := (continuous_const : Continuous (fun _ : ℝ => actualPhysicalProjectionStock value N)).inner (𝕜 := ℂ) sourceAction
  have actual := price.intervalIntegrable (μ := volume) 0 h
  have equation := fun t : ℝ => actual_complete_window_weighted_cotest (actualPhysicalProjectionStock value N) source t
  simpa only [Function.comp_apply,equation] using actual

private theorem raw_source_weighted_integrable (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (source : BurnolQuarterIntervalL2) :
    IntervalIntegrable (actualPairRawSourceWeightedFee observation nontrivial half h source) volume 0 h ∧
    IntervalIntegrable (actualSiblingRawSourceWeightedFee observation nontrivial half h source) volume 0 h := by
  have sourceAction := (burnolMultiplicativeDilation_stronglyContinuous (burnolQuarterZeroExtension source)).comp continuous_neg
  constructor
  · have price := (continuous_const : Continuous (fun _ : ℝ => (Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2))).inner (𝕜 := ℂ) sourceAction
    have generated := fun t : ℝ => (actual_expanded_complete_window_source_prices observation nontrivial half h source t).1.trans
      (actual_raw_source_weighted_complete_fees observation nontrivial half h nonnegative bounded source t).1
    simpa only [Function.comp_apply,generated] using price.intervalIntegrable (μ := volume) 0 h
  · have price := (continuous_const : Continuous (fun _ : ℝ => (Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2))).inner (𝕜 := ℂ) sourceAction
    have generated := fun t : ℝ => (actual_expanded_complete_window_source_prices observation nontrivial half h source t).2.trans
      (actual_raw_source_weighted_complete_fees observation nontrivial half h nonnegative bounded source t).2
    simpa only [Function.comp_apply,generated] using price.intervalIntegrable (μ := volume) 0 h

/-- The actual raw field integral consumes the finite source inverse stock and retains the full same-source tail fee. -/
theorem actual_original_correction_stock_integral_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (N : ℕ) :
    actualPairRawSourceIntegralFee observation nontrivial half h =
      actualPairCorrectionStockIntegralFee observation nontrivial half h N - actualPairCorrectionTailIntegralFee observation nontrivial half h N ∧
    actualSiblingRawSourceIntegralFee observation nontrivial half h =
      actualSiblingCorrectionStockIntegralFee observation nontrivial half h N - actualSiblingCorrectionTailIntegralFee observation nontrivial half h N := by
  have pairTail := correction_tail_integrable (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) actualCoupledQuarterPlus h N
  have siblingTail := correction_tail_integrable (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) actualCoupledQuarterMinus h N
  change IntervalIntegrable (fun t : ℝ => actualPairCorrectionTailWeightedFee observation nontrivial half h actualCoupledQuarterPlus t N) volume 0 h at pairTail
  change IntervalIntegrable (fun t : ℝ => actualSiblingCorrectionTailWeightedFee observation nontrivial half h actualCoupledQuarterMinus t N) volume 0 h at siblingTail
  have rawPair := (raw_source_weighted_integrable observation nontrivial half h nonnegative bounded actualCoupledQuarterPlus).1
  have rawSibling := (raw_source_weighted_integrable observation nontrivial half h nonnegative bounded actualCoupledQuarterMinus).2
  have pairStock : IntervalIntegrable (fun t : ℝ => actualPairCorrectionStockWeightedFee observation nontrivial half h actualCoupledQuarterPlus t N) volume 0 h := by
    have complete := rawPair.add pairTail
    have equation := fun t : ℝ => (actual_original_correction_stock_weighted_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterPlus t N).1
    convert complete using 1
    funext t
    rw [equation]
    ring
  have siblingStock : IntervalIntegrable (fun t : ℝ => actualSiblingCorrectionStockWeightedFee observation nontrivial half h actualCoupledQuarterMinus t N) volume 0 h := by
    have complete := rawSibling.add siblingTail
    have equation := fun t : ℝ => (actual_original_correction_stock_weighted_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterMinus t N).2
    convert complete using 1
    funext t
    rw [equation]
    ring
  constructor
  · unfold actualPairRawSourceIntegralFee actualPairCorrectionStockIntegralFee actualPairCorrectionTailIntegralFee
    rw [←intervalIntegral.integral_sub pairStock pairTail]
    apply intervalIntegral.integral_congr
    intro t _
    exact (actual_original_correction_stock_weighted_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterPlus t N).1
  · unfold actualSiblingRawSourceIntegralFee actualSiblingCorrectionStockIntegralFee actualSiblingCorrectionTailIntegralFee
    rw [←intervalIntegral.integral_sub siblingStock siblingTail]
    apply intervalIntegral.integral_congr
    intro t _
    exact (actual_original_correction_stock_weighted_fees observation nontrivial half h nonnegative bounded actualCoupledQuarterMinus t N).2

def actualPairCorrectionStockCvelPrice (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h +
    (Kernel.A c-Kernel.beta c) *
      (actualPairCorrectionStockIntegralFee observation nontrivial half h N - actualPairCorrectionTailIntegralFee observation nontrivial half h N)

def actualSiblingCorrectionStockCvelPrice (h : ℝ) (N : ℕ) : ℂ :=
  OriginalKCvelCompressedSourceAction.actualContactVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h -
    (Kernel.A c+Kernel.beta c) *
      (actualSiblingCorrectionStockIntegralFee observation nontrivial half h N - actualSiblingCorrectionTailIntegralFee observation nontrivial half h N)

theorem actual_Cvel_consumes_correction_stock_source (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (N : ℕ) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaPairedR observation nontrivial half h)) h =
      actualPairCorrectionStockCvelPrice observation nontrivial half h N ∧
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice c (Q (actualNonPaSiblingR observation nontrivial half h)) h =
      actualSiblingCorrectionStockCvelPrice observation nontrivial half h N := by
  have raw := actual_Cvel_consumes_original_raw_source_fees observation nontrivial half h nonnegative bounded
  have source := actual_original_correction_stock_integral_fees observation nontrivial half h nonnegative bounded N
  constructor
  · rw [raw.1]
    unfold actualPairRawCvelSourcePrice actualPairCorrectionStockCvelPrice
    rw [source.1]
  · rw [raw.2]
    unfold actualSiblingRawCvelSourcePrice actualSiblingCorrectionStockCvelPrice
    rw [source.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
