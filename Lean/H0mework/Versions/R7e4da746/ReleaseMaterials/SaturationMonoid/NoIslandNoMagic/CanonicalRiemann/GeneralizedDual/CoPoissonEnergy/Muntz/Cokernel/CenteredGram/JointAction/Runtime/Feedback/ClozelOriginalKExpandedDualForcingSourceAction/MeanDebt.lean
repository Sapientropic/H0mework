import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction
open OriginalKMaterialExpandedDualSourceAction OriginalRieszSource
open scoped InnerProductSpace
local instance meanComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete
local notation "q" => (1/4:ℝ)

/-- The actual full quarter input is read before subtracting its own constant mean. -/
def sourceFullQuarterAction (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
 burnolQuarterRestriction.comp ((burnolMultiplicativeDilation t).toLinearIsometry.toContinuousLinearMap.comp
  burnolEvenAmbientProjectionEndomorphism)

def sourceQuarterMeanDebtAction (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
 sourceFullQuarterAction t -
 (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp (sourceExpandedQuarterReader t)

/-- The debt is the actual source mean and actual interval constant, not an inferred zero or a target margin. -/
theorem source_quarter_mean_debt (value : BurnolL2) (t : ℝ) :
 sourceQuarterMeanDebtAction t value=
 burnolQuarterMeanCoefficient (sourceFullQuarterAction t value) • intervalConstant q := by
 change sourceFullQuarterAction t value - (Constructor.zeroMean (sourceFullQuarterAction t value) : BurnolQuarterIntervalL2)=_
 rw [Constructor.zeroMean_read,sub_sub_cancel]

/-- Literal source forcing plus the original mean debt regenerate the entire quarter field. -/
def sourceFullPlusForcingProgramme (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
 (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp
  (sourceDualPlusForcing.comp (sourceDualPlusRaw t)) + sourceQuarterMeanDebtAction t

def sourceFullMinusForcingProgramme (t : ℝ) : BurnolL2 →L[ℂ] BurnolQuarterIntervalL2 :=
 (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule).comp
  (sourceDualMinusForcing.comp (sourceDualMinusRaw t)) + sourceQuarterMeanDebtAction t

theorem source_full_forcing_programme (value : BurnolL2) (t : ℝ) :
 sourceFullPlusForcingProgramme t value=sourceFullQuarterAction t value ∧
 sourceFullMinusForcingProgramme t value=sourceFullQuarterAction t value := by
 have actual := actual_raw_profiles_generate_forcing value t
 constructor
 · change (sourceDualPlusForcing (sourceDualPlusRaw t value) : BurnolQuarterIntervalL2)+sourceQuarterMeanDebtAction t value=_
   rw [actual.1]
   change (sourceExpandedQuarterReader t value : BurnolQuarterIntervalL2)+
    (sourceFullQuarterAction t value-(sourceExpandedQuarterReader t value : BurnolQuarterIntervalL2))=_
   rw [←add_sub_assoc,add_sub_cancel_left]
 · change (sourceDualMinusForcing (sourceDualMinusRaw t value) : BurnolQuarterIntervalL2)+sourceQuarterMeanDebtAction t value=_
   rw [actual.2]
   change (sourceExpandedQuarterReader t value : BurnolQuarterIntervalL2)+
    (sourceFullQuarterAction t value-(sourceExpandedQuarterReader t value : BurnolQuarterIntervalL2))=_
   rw [←add_sub_assoc,add_sub_cancel_left]

/-- The full arbitrary quarter observer is paid from actual forcing and the complete mean debt after the source programme. -/
theorem source_full_quarter_fee (value : BurnolL2) (t : ℝ) (test : BurnolQuarterIntervalL2) :
 inner ℂ (sourceFullPlusForcingProgramme t value) test=
 inner ℂ (sourceFullQuarterAction t value) test ∧
 inner ℂ (sourceFullMinusForcingProgramme t value) test=
 inner ℂ (sourceFullQuarterAction t value) test := by
 rw [(source_full_forcing_programme value t).1,(source_full_forcing_programme value t).2]
 exact ⟨rfl,rfl⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedDualForcingSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
