import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedInverseSourceAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.PhysicalEffect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKPhysicalCorrectionStockSourceAction
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance quarterComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def sourceExpandedPhysicalAction (t : ℝ) :
 BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolPaAmbientCarrier :=
 burnolEvenAmbientProjection.comp
  ((burnolMultiplicativeDilation (-t)).toLinearIsometry.toContinuousLinearMap.comp
   (burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)))

def sourceExpandedPhysicalPlus (t : ℝ) : BurnolPaAmbientCarrier :=
 sourceExpandedPhysicalAction t (sourcePlusAction Response.eta)

def sourceExpandedPhysicalMinus (t : ℝ) : BurnolPaAmbientCarrier :=
 sourceExpandedPhysicalAction t (sourceMinusAction Response.eta)

/-- Both quarter inverse corrections belong to the actual expanded source, rather than a borrowed Pa qualification. -/
theorem source_expanded_physical_fields (t : ℝ) :
 sourceExpandedPhysicalPlus t = burnolEvenAmbientProjection
  (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV)) ∧
 sourceExpandedPhysicalMinus t = burnolEvenAmbientProjection
  (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV)) := by
 constructor
 · change burnolEvenAmbientProjection (burnolMultiplicativeDilation (-t)
    (burnolQuarterZeroExtension ((sourcePlusAction Response.eta) : BurnolQuarterIntervalL2))) = _
   rw [source_coupled_fields.1]
   simp only [Submodule.coe_add,map_add,Response.wholeU,Response.wholeV]
 · change burnolEvenAmbientProjection (burnolMultiplicativeDilation (-t)
    (burnolQuarterZeroExtension ((sourceMinusAction Response.eta) : BurnolQuarterIntervalL2))) = _
   rw [source_coupled_fields.2]
   simp only [Submodule.coe_sub,map_sub,Response.wholeU,Response.wholeV]

/-- The existing physical field consumes its own dependent projection of the complete expanded source. -/
theorem source_physical_field_consumes_expanded_projection (test : BurnolPaAmbientCarrier) (t : ℝ) :
 inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV)) =
  inner ℂ test (sourceExpandedPhysicalPlus t) ∧
 inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV)) =
  inner ℂ test (sourceExpandedPhysicalMinus t) := by
 rw [(source_expanded_physical_fields t).1,(source_expanded_physical_fields t).2]
 constructor <;> symm <;>
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- Actual finite stock is read against the generated physical weight. Its same two-foot tail is eliminated by the source law, for every stock depth. -/
theorem source_expanded_inverse_stock_price (value : BurnolL2) (test : BurnolPaAmbientCarrier) (N : ℕ) :
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2) (test : BurnolL2) =
  inner ℂ (actualPhysicalProjectionStock value N) (test : BurnolL2) := by
 rw [actual_physical_projection_stock_complete,inner_sub_left,
  OriginalKMaterialPhysicalStockSourceAction.actual_source_correction_tail_physical_read,sub_zero]

theorem source_expanded_full_stock_prices (value : BurnolL2) (t : ℝ) (N : ℕ) :
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
   (burnolMultiplicativeDilation (-t) (Response.wholeU+Response.wholeV)) =
  inner ℂ (actualPhysicalProjectionStock value N) (sourceExpandedPhysicalPlus t : BurnolL2) ∧
 inner ℂ (burnolEvenAmbientProjection value : BurnolL2)
   (burnolMultiplicativeDilation (-t) (Response.wholeU-Response.wholeV)) =
  inner ℂ (actualPhysicalProjectionStock value N) (sourceExpandedPhysicalMinus t : BurnolL2) := by
 have projection := source_physical_field_consumes_expanded_projection (burnolEvenAmbientProjection value) t
 constructor
 · rw [projection.1]
   change inner ℂ (burnolEvenAmbientProjection value : BurnolL2) (sourceExpandedPhysicalPlus t : BurnolL2) = _
   exact source_expanded_inverse_stock_price value _ N
 · rw [projection.2]
   change inner ℂ (burnolEvenAmbientProjection value : BurnolL2) (sourceExpandedPhysicalMinus t : BurnolL2) = _
   exact source_expanded_inverse_stock_price value _ N
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
