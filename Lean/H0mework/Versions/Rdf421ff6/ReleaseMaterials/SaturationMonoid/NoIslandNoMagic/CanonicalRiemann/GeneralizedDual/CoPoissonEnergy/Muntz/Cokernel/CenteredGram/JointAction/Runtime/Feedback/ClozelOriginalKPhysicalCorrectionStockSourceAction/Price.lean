import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Bound
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
local notation "P" => burnolEvenAmbientProjection
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
open OriginalKPhysicalRawWindowSourceAction OriginalKExpandedCompleteWindowSourceAction OriginalKQBSourceWindowAction OriginalKWholePaSourceRankAction
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The same complete source-window inventory is read after the finite actual correction action. -/
def actualPairCorrectionStockWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (burnolRadiusRestriction (radius t)
    (actualPhysicalProjectionStock (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) N))
    (actualExpandedQuarterWeight source t) -
  inner ℂ (paSourceWindowProgramme (actualFullPairPaSource observation nontrivial half h) t) (actualExpandedQuarterWeight source t) -
  star (actualWholePaSourceCoefficient observation nontrivial half h/2) *
    inner ℂ (actualUnitPairWindowProgramme observation nontrivial half t) (actualExpandedQuarterWeight source t)

def actualSiblingCorrectionStockWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (burnolRadiusRestriction (radius t)
    (actualPhysicalProjectionStock (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) N))
    (actualExpandedQuarterWeight source t) -
  inner ℂ (paSourceWindowProgramme (actualFullSiblingPaSource observation nontrivial half h) t) (actualExpandedQuarterWeight source t) -
  star (actualWholePaSourceCoefficient observation nontrivial half h/2) *
    inner ℂ (actualUnitSiblingWindowProgramme observation nontrivial half t) (actualExpandedQuarterWeight source t)

def actualPairCorrectionTailWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (burnolRadiusRestriction (radius t)
    (actualPhysicalCorrectionTail (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) N))
    (actualExpandedQuarterWeight source t)

def actualSiblingCorrectionTailWeightedFee (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) : ℂ :=
  inner ℂ (burnolRadiusRestriction (radius t)
    (actualPhysicalCorrectionTail (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) N))
    (actualExpandedQuarterWeight source t)

theorem actual_original_correction_stock_weighted_fees (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (source : BurnolQuarterIntervalL2) (t : ℝ) (N : ℕ) :
    actualPairRawSourceWeightedFee observation nontrivial half h source t =
      actualPairCorrectionStockWeightedFee observation nontrivial half h source t N - actualPairCorrectionTailWeightedFee observation nontrivial half h source t N ∧
    actualSiblingRawSourceWeightedFee observation nontrivial half h source t =
      actualSiblingCorrectionStockWeightedFee observation nontrivial half h source t N - actualSiblingCorrectionTailWeightedFee observation nontrivial half h source t N := by
  have raw := actual_raw_source_weighted_complete_fees observation nontrivial half h nonnegative bounded source t
  rw [←raw.1,←raw.2]
  unfold actualPairWindowSourceCotest actualSiblingWindowSourceCotest actualNonPaPairWindowProgramme actualNonPaSiblingWindowProgramme
    actualPairCorrectionStockWeightedFee actualSiblingCorrectionStockWeightedFee actualPairCorrectionTailWeightedFee actualSiblingCorrectionTailWeightedFee
  rw [actual_physical_projection_stock_complete (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) N,
    actual_physical_projection_stock_complete (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) N]
  simp only [map_sub,inner_sub_left,inner_smul_left]
  constructor <;> simp only [starRingEnd_apply] <;> ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
