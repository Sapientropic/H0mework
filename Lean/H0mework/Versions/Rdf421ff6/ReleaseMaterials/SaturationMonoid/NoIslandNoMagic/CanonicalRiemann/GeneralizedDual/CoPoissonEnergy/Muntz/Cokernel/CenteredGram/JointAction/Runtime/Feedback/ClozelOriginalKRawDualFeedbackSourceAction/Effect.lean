import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Reader
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction OriginalKExpandedDualForcingSourceAction
open OriginalKMaterialExpandedDualSourceAction
open scoped InnerProductSpace
local instance effectComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

def plusSourceStock (N : Nat) := feedbackStock plusFeedback N
def minusSourceStock (N : Nat) := feedbackStock minusFeedback N

def plusSourceRemainder (N : Nat) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 (plusFeedback^N).comp sourcePlusAction.adjoint

def minusSourceRemainder (N : Nat) : BurnolQuarterMeanZeroCarrier →L[ℂ] BurnolQuarterMeanZeroCarrier :=
 (minusFeedback^N).comp sourceMinusAction.adjoint

/-- The complete raw profiles split by their actual source update, retaining the same-power inverse remainder. -/
theorem source_raw_profiles_complete (source : BurnolQuarterMeanZeroCarrier) (N : Nat) :
 sourcePlusAction.adjoint source=plusSourceStock N source+plusSourceRemainder N source ∧
 sourceMinusAction.adjoint source=minusSourceStock N source+minusSourceRemainder N source :=
 ⟨source_feedback_finite_and_remainder _ _ _ (source_signed_feedback source).1 N,
  source_feedback_finite_and_remainder _ _ _ (source_signed_feedback source).2 N⟩

def sourceFiniteDualPlus (t : ℝ) (N : Nat) := sourceDualEvenQuarter.comp ((plusSourceStock N).comp (sourceExpandedQuarterReader t))
def sourceFiniteDualMinus (t : ℝ) (N : Nat) := sourceDualEvenQuarter.comp ((minusSourceStock N).comp (sourceExpandedQuarterReader t))
def sourceRemainderDualPlus (t : ℝ) (N : Nat) := sourceDualEvenQuarter.comp ((plusSourceRemainder N).comp (sourceExpandedQuarterReader t))
def sourceRemainderDualMinus (t : ℝ) (N : Nat) := sourceDualEvenQuarter.comp ((minusSourceRemainder N).comp (sourceExpandedQuarterReader t))

def sourceFiniteDualField (t : ℝ) (N : Nat) : BurnolL2 →L[ℂ] BurnolL2 :=
 OriginalKCvelSourceAction.actualStockExtension.comp (sourceFiniteDualPlus t N)+
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp (sourceFiniteDualMinus t N))

def sourceRemainderDualField (t : ℝ) (N : Nat) : BurnolL2 →L[ℂ] BurnolL2 :=
 OriginalKCvelSourceAction.actualStockExtension.comp (sourceRemainderDualPlus t N)+
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp (sourceRemainderDualMinus t N))

theorem source_actual_profiles_finite_and_remainder (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceDualPlus t value=sourceFiniteDualPlus t N value+sourceRemainderDualPlus t N value ∧
 sourceDualMinus t value=sourceFiniteDualMinus t N value+sourceRemainderDualMinus t N value := by
 have raw := source_raw_profiles_complete (sourceExpandedQuarterReader t value) N
 constructor
 · change sourceDualEvenQuarter (sourcePlusAction.adjoint (sourceExpandedQuarterReader t value))=_
   rw [raw.1,map_add]
   rfl
 · change sourceDualEvenQuarter (sourceMinusAction.adjoint (sourceExpandedQuarterReader t value))=_
   rw [raw.2,map_add]
   rfl

/-- The whole source field is the emitted finite vector plus its complete same-source inverse tail; neither raw odd source nor tail is zero by declaration. -/
theorem source_actual_field_finite_and_remainder (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceDualCompleteField t value=sourceFiniteDualField t N value+sourceRemainderDualField t N value := by
 have actual := source_actual_profiles_finite_and_remainder value t N
 rw [source_dual_complete_field,actual.1,actual.2]
 change burnolQuarterZeroExtension
  ((sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)+(sourceRemainderDualPlus t N value : BurnolQuarterIntervalL2))+
  fourierL2 (burnolQuarterZeroExtension
   ((sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)+(sourceRemainderDualMinus t N value : BurnolQuarterIntervalL2)))=
  (burnolQuarterZeroExtension (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)+
   fourierL2 (burnolQuarterZeroExtension (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)))+
  (burnolQuarterZeroExtension (sourceRemainderDualPlus t N value : BurnolQuarterIntervalL2)+
   fourierL2 (burnolQuarterZeroExtension (sourceRemainderDualMinus t N value : BurnolQuarterIntervalL2)))
 simp only [map_add]
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
