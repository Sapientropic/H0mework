import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalCorrectionStockSourceAction.Consumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPaWindowSourceAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKPhysicalCorrectionStockSourceAction
local instance meanZeroComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
  IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "T" => burnolMeanZeroTruncatedFourier
local notation "T2" => burnolMeanZeroTruncatedFourierSquare
local notation "F" => fourierL2.toLinearIsometry.toContinuousLinearMap

def sourceEvenAction : BurnolL2 →L[ℂ] BurnolL2 :=
  (1/2:ℂ) • (ContinuousLinearMap.id ℂ BurnolL2 + reflectL2.toContinuousLinearMap)

def sourcePositionRhs : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
    (burnolQuarterRestriction.comp sourceEvenAction)

def sourceFourierRhs : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolQuarterMeanZeroClosedFace.toSubmodule.orthogonalProjectionOnto.comp
    (burnolQuarterRestriction.comp ((F).comp sourceEvenAction))

def sourceCorrectionRhs : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  sourcePositionRhs - (T).comp sourceFourierRhs

def sourceFirstCorrectionStockAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  (∑ n ∈ Finset.range N, T2^n).comp sourceCorrectionRhs

def sourceSecondCorrectionStockAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  sourceFourierRhs - (T).comp (sourceFirstCorrectionStockAction N)

/-- These actual material operators read both native position/Fourier block RHS, before any field effect or price. -/
theorem source_correction_stock_actions_read (value : BurnolL2) (N : ℕ) :
    sourceFirstCorrectionStockAction N value = actualFirstCorrectionStock value N ∧
    sourceSecondCorrectionStockAction N value = actualSecondCorrectionStock value N := by
  constructor <;> rfl

def sourcePhysicalStockAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 :=
  sourceEvenAction - sourceEvenAction.comp
    (OriginalKCvelSourceAction.actualStockExtension.comp (sourceFirstCorrectionStockAction N) +
      (F).comp (OriginalKCvelSourceAction.actualStockExtension.comp (sourceSecondCorrectionStockAction N)))

def sourceFirstCorrectionAction : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  burnolMeanZeroBlockInverse.comp sourceCorrectionRhs

def sourceFirstCorrectionTailAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  (T2^N).comp sourceFirstCorrectionAction

def sourceSecondCorrectionTailAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
  -((T).comp (sourceFirstCorrectionTailAction N))

def sourcePhysicalTailAction (N : ℕ) : BurnolL2 →L[ℂ] BurnolL2 :=
  sourceEvenAction.comp
    (OriginalKCvelSourceAction.actualStockExtension.comp (sourceFirstCorrectionTailAction N) +
      (F).comp (OriginalKCvelSourceAction.actualStockExtension.comp (sourceSecondCorrectionTailAction N)))

theorem source_physical_stock_actions_read (value : BurnolL2) (N : ℕ) :
    sourcePhysicalStockAction N value = actualPhysicalProjectionStock value N ∧
    sourcePhysicalTailAction N value = actualPhysicalCorrectionTail value N := by
  constructor <;> rfl

namespace D
export OriginalKMaterialPaWindowSourceAction.D (SourceBranches SourceVar actualMaterialREffect actualMaterialInheritedREffect actual_material_R_effect_partition)
end D
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C

def sourceMaterialPhysicalStockAction (N : ℕ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
  OriginalKBoundaryNativeSourceAction.sourceFields.comp ((sourcePhysicalStockAction N).comp OriginalKFullSourceRAction.originalField)

def sourceMaterialPhysicalTailAction (N : ℕ) : D.SourceBranches →L[ℂ] D.SourceBranches :=
  OriginalKBoundaryNativeSourceAction.sourceFields.comp ((sourcePhysicalTailAction N).comp OriginalKFullSourceRAction.originalField)

def sourceMaterialPhysicalProjection : D.SourceBranches →L[ℂ] D.SourceBranches :=
  OriginalKBoundaryNativeSourceAction.sourceFields.comp
    (burnolEvenAmbientProjectionEndomorphism.comp OriginalKFullSourceRAction.originalField)

/-- The existing actual R material slot is transformed through its own source field, retaining its full paired action roles. -/
theorem source_material_physical_stock_complete (value : D.SourceBranches) (N : ℕ) :
    sourceMaterialPhysicalProjection value = sourceMaterialPhysicalStockAction N value - sourceMaterialPhysicalTailAction N value := by
  have generated := actual_physical_projection_stock_complete (OriginalKFullSourceRAction.originalField value) N
  change OriginalKBoundaryNativeSourceAction.sourceFields (burnolEvenAmbientProjectionEndomorphism (OriginalKFullSourceRAction.originalField value)) = _
  rw [show burnolEvenAmbientProjectionEndomorphism (OriginalKFullSourceRAction.originalField value) =
    (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField value) : BurnolL2) by rfl,generated,map_sub]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
