import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedCompleteWindowSourceAction.Source
import H0mework.Versions.R7e4da746.Arithmetic.RieszColumns.Window
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
local instance effectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
open OriginalKWholePaSourceRankAction
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The same quarter source is moved into the actual full radius carrier before any price is read. -/
def actualExpandedQuarterWeight (source : BurnolQuarterIntervalL2) (t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  burnolRadiusRestriction (radius t) (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension source))

theorem actual_quarter_weight_source_window (source : BurnolQuarterIntervalL2) (t : ℝ) :
    burnolRadiusZeroExtension (radius t) (actualExpandedQuarterWeight source t) =
      burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension source) := by
  have generated := OriginalRieszFiniteColumns.intervalDilation_cutoff_self source (-t) (radius t)
    (by simp only [neg_neg]; exact le_refl _)
  exact generated

theorem actual_complete_window_weighted_cotest (test : BurnolL2) (source : BurnolQuarterIntervalL2) (t : ℝ) :
    inner ℂ test (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension source)) =
      inner ℂ (burnolRadiusRestriction (radius t) test) (actualExpandedQuarterWeight source t) := by
  rw [←actual_quarter_weight_source_window source t]
  exact ContinuousLinearMap.adjoint_inner_right (burnolRadiusRestriction (radius t)) _ _

def actualPairWindowSourceCotest (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  inner ℂ (actualNonPaPairWindowProgramme observation nontrivial half h t) (actualExpandedQuarterWeight source t)

def actualSiblingWindowSourceCotest (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) : ℂ :=
  inner ℂ (actualNonPaSiblingWindowProgramme observation nontrivial half h t) (actualExpandedQuarterWeight source t)

/-- Complete finite Pa source vectors and pole, rather than their scalar means, pay both expanded physical cotests. -/
theorem actual_expanded_complete_window_source_prices (h : ℝ) (source : BurnolQuarterIntervalL2) (t : ℝ) :
    inner ℂ (Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2)
      (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension source)) =
        actualPairWindowSourceCotest observation nontrivial half h source t ∧
    inner ℂ (Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2)
      (burnolMultiplicativeDilation (-t) (burnolQuarterZeroExtension source)) =
        actualSiblingWindowSourceCotest observation nontrivial half h source t := by
  have generated := actual_nonPa_complete_window_programmes observation nontrivial half h t
  constructor
  · rw [actual_complete_window_weighted_cotest,generated.1]
    rfl
  · rw [actual_complete_window_weighted_cotest,generated.2]
    rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
