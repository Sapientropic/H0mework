import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedInverseSourceAction.Physical
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource OriginalKMaterialPhysicalStockSourceAction
local instance programmeComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def sourceExpandedAmbientAction (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolL2 :=
 (burnolMultiplicativeDilation (-t)).toLinearIsometry.toContinuousLinearMap.comp
  (burnolQuarterZeroExtension.comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule))

/-- The two actual expanded block RHS are retained before applying their source inverse. -/
def sourceExpandedPositionRhs (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := sourcePositionRhs.comp (sourceExpandedAmbientAction t)
def sourceExpandedFourierRhs (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := sourceFourierRhs.comp (sourceExpandedAmbientAction t)
def sourceExpandedFirstCorrection (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier := sourceFirstCorrectionAction.comp (sourceExpandedAmbientAction t)
def sourceExpandedSecondCorrection (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 sourceExpandedFourierRhs t - burnolMeanZeroTruncatedFourier.comp (sourceExpandedFirstCorrection t)

def sourceExpandedPhysicalProgramme (t : ℝ) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolL2 :=
 sourceEvenAction.comp (sourceExpandedAmbientAction t) - sourceEvenAction.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp (sourceExpandedFirstCorrection t) +
   fourierL2.toLinearIsometry.toContinuousLinearMap.comp
    (OriginalKCvelSourceAction.actualStockExtension.comp (sourceExpandedSecondCorrection t)))

/-- The actual source equation exposes the complete first and Fourier-second corrections; no mean slot is discarded. -/
theorem source_expanded_two_block_equations (t : ℝ) (source : BurnolQuarterMeanZeroCarrier) :
 sourceExpandedFirstCorrection t source +
  burnolMeanZeroTruncatedFourier (sourceExpandedSecondCorrection t source) =
  sourceExpandedPositionRhs t source ∧
 burnolMeanZeroTruncatedFourier (sourceExpandedFirstCorrection t source) +
  sourceExpandedSecondCorrection t source = sourceExpandedFourierRhs t source := by
 let rhs : BurnolQuarterMeanZeroCarrier × BurnolQuarterMeanZeroCarrier :=
  (sourceExpandedPositionRhs t source,sourceExpandedFourierRhs t source)
 have first := burnolMeanZeroBlock_first_equation rhs
 have second := burnolMeanZeroBlock_second_equation rhs
 have actualFirst : sourceExpandedFirstCorrection t source = burnolMeanZeroBlockFirst rhs := by rfl
 have actualSecond : sourceExpandedSecondCorrection t source = burnolMeanZeroBlockSecond rhs := by rfl
 rw [actualFirst,actualSecond]
 exact ⟨first,second⟩

/-- Projection is a consumer of the generated source programme, rather than a supplied qualifier. -/
theorem source_expanded_physical_programme (t : ℝ) (source : BurnolQuarterMeanZeroCarrier) :
 sourceExpandedPhysicalProgramme t source =
  (sourceExpandedPhysicalAction t source : BurnolL2) := by
 change _ = (burnolEvenAmbientProjection (sourceExpandedAmbientAction t source) : BurnolL2)
 change _ = ((evenBurnolClosedFace (1/4:ℝ)).toSubmodule.orthogonalProjectionOnto
  (sourceExpandedAmbientAction t source) : BurnolL2)
 rw [burnolEvenOrthogonalProjectionOnto_eq_resolventFormula]
 rfl

/-- The complete two endpoint forcing faces pay the actual expanded physical weights. -/
theorem source_expanded_endpoint_programmes (t : ℝ) :
 sourceExpandedPhysicalProgramme t (sourcePlusAction Response.eta) =
  (sourceExpandedPhysicalPlus t : BurnolL2) ∧
 sourceExpandedPhysicalProgramme t (sourceMinusAction Response.eta) =
  (sourceExpandedPhysicalMinus t : BurnolL2) := by
 exact ⟨source_expanded_physical_programme t _,source_expanded_physical_programme t _⟩
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedInverseSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
