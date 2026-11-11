import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalRawWindowSourceAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelSourceAction.Residual
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
local instance correctionComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "T2" => burnolMeanZeroTruncatedFourierSquare

def actualCorrectionSourceRhs (value : BurnolL2) : BurnolQuarterMeanZeroCarrier :=
  (burnolAmbientMeanZeroBlockRhs value).1 - T (burnolAmbientMeanZeroBlockRhs value).2

def actualFirstCorrectionStock (value : BurnolL2) (N : ℕ) : BurnolQuarterMeanZeroCarrier :=
  (∑ n ∈ Finset.range N, T2^n) (actualCorrectionSourceRhs value)

def actualSecondCorrectionStock (value : BurnolL2) (N : ℕ) : BurnolQuarterMeanZeroCarrier :=
  (burnolAmbientMeanZeroBlockRhs value).2 - T (actualFirstCorrectionStock value N)

def actualFirstCorrectionTail (value : BurnolL2) (N : ℕ) : BurnolQuarterMeanZeroCarrier :=
  (T2^N) (burnolAmbientMeanZeroFirstCorrection value)

def actualSecondCorrectionTail (value : BurnolL2) (N : ℕ) : BurnolQuarterMeanZeroCarrier :=
  -T (actualFirstCorrectionTail value N)

/-- Both corrections are generated from the actual source two-block RHS; eta from another source is never substituted. -/
theorem actual_correction_source_stock_complete (value : BurnolL2) (N : ℕ) :
    burnolAmbientMeanZeroFirstCorrection value = actualFirstCorrectionStock value N + actualFirstCorrectionTail value N ∧
    burnolAmbientMeanZeroSecondCorrection value = actualSecondCorrectionStock value N + actualSecondCorrectionTail value N := by
  have inverse := @NormedRing.inverse_one_sub_nth_order' (BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier)
    ContinuousLinearMap.toNormedRing inferInstance N T2 burnolMeanZeroTruncatedFourierSquare_opNorm_lt_one
  have first := congrArg (fun action : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier =>
    action (actualCorrectionSourceRhs value)) inverse
  change burnolAmbientMeanZeroFirstCorrection value = actualFirstCorrectionStock value N + actualFirstCorrectionTail value N at first
  refine ⟨first,?_⟩
  unfold burnolAmbientMeanZeroSecondCorrection burnolMeanZeroBlockSecond
  change (burnolAmbientMeanZeroBlockRhs value).2 - T (burnolAmbientMeanZeroFirstCorrection value) = _
  rw [first,map_add]
  unfold actualSecondCorrectionStock actualSecondCorrectionTail
  module

theorem actual_correction_source_stock_action (value : BurnolL2) (N : ℕ) :
    actualFirstCorrectionStock value (N+1) = actualFirstCorrectionStock value N + (T2^N) (actualCorrectionSourceRhs value) ∧
    actualFirstCorrectionTail value (N+1) = T2 (actualFirstCorrectionTail value N) := by
  constructor
  · simp only [actualFirstCorrectionStock,Finset.sum_range_succ,add_apply]
  · simp only [actualFirstCorrectionTail,pow_succ',mul_apply_eq_comp]

theorem actual_correction_source_stock_closure (value : BurnolL2) :
    Tendsto (actualFirstCorrectionStock value) atTop (𝓝 (burnolAmbientMeanZeroFirstCorrection value)) ∧
    Tendsto (actualSecondCorrectionStock value) atTop (𝓝 (burnolAmbientMeanZeroSecondCorrection value)) := by
  have inverse := OriginalKCvelSourceAction.actual_source_operator_sum.tendsto_sum_nat
  have first := ((ContinuousLinearMap.apply ℂ BurnolQuarterMeanZeroCarrier (actualCorrectionSourceRhs value)).continuous.tendsto _).comp inverse
  refine ⟨first,?_⟩
  exact tendsto_const_nhds.sub ((T).continuous.tendsto _ |>.comp first)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalCorrectionStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
