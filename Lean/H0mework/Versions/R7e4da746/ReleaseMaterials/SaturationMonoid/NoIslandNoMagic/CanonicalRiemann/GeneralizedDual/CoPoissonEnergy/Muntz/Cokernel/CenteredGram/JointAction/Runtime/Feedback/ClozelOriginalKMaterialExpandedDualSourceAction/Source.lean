import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedInverseSourceAction.Programme
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKExpandedInverseSourceAction
open OriginalKMaterialPhysicalStockSourceAction
local instance sourceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local instance sourcePhysicalComplete : CompleteSpace BurnolPaAmbientCarrier :=
 IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "Z" => OriginalKCvelSourceAction.actualStockExtension
local notation "F" => fourierL2.toLinearIsometry.toContinuousLinearMap

/-- The physical input is projected from the actual full material field, then its own quarter face is read. -/
def sourceExpandedQuarterReader (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 Constructor.zeroMean.comp (burnolQuarterRestriction.comp
  ((burnolMultiplicativeDilation t).toLinearIsometry.toContinuousLinearMap.comp
   burnolEvenAmbientProjectionEndomorphism))

def sourceDualPlusRaw (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourcePlusAction.adjoint.comp (sourceExpandedQuarterReader t)

def sourceDualMinusRaw (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceMinusAction.adjoint.comp (sourceExpandedQuarterReader t)

/-- The existing even/mean-zero source operation supplies the two own-foot qualifications before encoding a field. -/
def sourceDualEvenQuarter : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourcePositionRhs.comp Z

def sourceDualPlus (t : ℝ) := sourceDualEvenQuarter.comp (sourceDualPlusRaw t)
def sourceDualMinus (t : ℝ) := sourceDualEvenQuarter.comp (sourceDualMinusRaw t)

def sourceDualCompleteField (t : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 (Z).comp (sourceDualPlus t) + (F).comp ((Z).comp (sourceDualMinus t))

/-- Every field is generated from the same two profiles; neither profile is replaced by a scalar price. -/
theorem source_dual_complete_field (value : BurnolL2) (t : ℝ) :
 sourceDualCompleteField t value =
 burnolQuarterZeroExtension (sourceDualPlus t value : BurnolQuarterIntervalL2) +
 fourierL2 (burnolQuarterZeroExtension (sourceDualMinus t value : BurnolQuarterIntervalL2)) := rfl

theorem source_dual_own_qualifications (value : BurnolL2) (t : ℝ) :
 burnolQuarterMeanCoefficient (sourceDualPlus t value : BurnolQuarterIntervalL2)=0 ∧
 burnolQuarterMeanCoefficient (sourceDualMinus t value : BurnolQuarterIntervalL2)=0 ∧
 reflectRestricted (1/4:ℝ) (sourceDualPlus t value : BurnolQuarterIntervalL2)=sourceDualPlus t value ∧
 reflectRestricted (1/4:ℝ) (sourceDualMinus t value : BurnolQuarterIntervalL2)=sourceDualMinus t value := by
 exact ⟨Constructor.mean_zero _,Constructor.mean_zero _,
  burnolAmbientMeanZeroPosition_reflection_fixed _,burnolAmbientMeanZeroPosition_reflection_fixed _⟩

/-- The actual two-foot source field keeps evenness before any native action or quarter inverse recovery. -/
theorem source_dual_complete_even (value : BurnolL2) (t : ℝ) :
 reflectL2 (sourceDualCompleteField t value)=sourceDualCompleteField t value := by
 rw [source_dual_complete_field,map_add,←fourierL2_reflectL2_commute]
 rw [burnolQuarterZeroExtension,burnolRadiusZeroExtension_reflect,
  (source_dual_own_qualifications value t).2.2.1,
  burnolRadiusZeroExtension_reflect,(source_dual_own_qualifications value t).2.2.2]
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialExpandedDualSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
