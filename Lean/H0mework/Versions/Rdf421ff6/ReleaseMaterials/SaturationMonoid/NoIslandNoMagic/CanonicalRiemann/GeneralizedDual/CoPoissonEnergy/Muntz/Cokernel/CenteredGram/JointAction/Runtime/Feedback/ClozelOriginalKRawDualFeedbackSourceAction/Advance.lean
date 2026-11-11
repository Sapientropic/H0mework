import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKExpandedInverseSourceAction OriginalKMaterialExpandedDualSourceAction
open scoped InnerProductSpace
local instance advanceComplete : CompleteSpace BurnolQuarterMeanZeroCarrier :=
 IsComplete.completeSpace_coe burnolQuarterMeanZeroClosedFace.isClosed.isComplete

/-- The finite actor's next source update is the actual signed feedback power, generated before the next field. -/
def sourcePlusStockAdvance (t : ℝ) (N : Nat) :=
 sourceDualEvenQuarter.comp ((plusFeedback^N).comp (sourceExpandedQuarterReader t))

def sourceMinusStockAdvance (t : ℝ) (N : Nat) :=
 sourceDualEvenQuarter.comp ((minusFeedback^N).comp (sourceExpandedQuarterReader t))

def sourceFieldAdvance (t : ℝ) (N : Nat) : BurnolL2 →L[ℂ] BurnolL2 :=
 OriginalKCvelSourceAction.actualStockExtension.comp (sourcePlusStockAdvance t N)+
 fourierL2.toLinearIsometry.toContinuousLinearMap.comp
  (OriginalKCvelSourceAction.actualStockExtension.comp (sourceMinusStockAdvance t N))

theorem source_actual_stock_advance (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceFiniteDualPlus t (N+1) value=sourceFiniteDualPlus t N value+sourcePlusStockAdvance t N value ∧
 sourceFiniteDualMinus t (N+1) value=sourceFiniteDualMinus t N value+sourceMinusStockAdvance t N value := by
 constructor
 · change sourceDualEvenQuarter ((∑ k ∈ Finset.range (N+1),plusFeedback^k) (sourceExpandedQuarterReader t value))=_
   rw [Finset.sum_range_succ,add_apply,map_add]
   rfl
 · change sourceDualEvenQuarter ((∑ k ∈ Finset.range (N+1),minusFeedback^k) (sourceExpandedQuarterReader t value))=_
   rw [Finset.sum_range_succ,add_apply,map_add]
   rfl

theorem source_actual_field_advance (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceFiniteDualField t (N+1) value=sourceFiniteDualField t N value+sourceFieldAdvance t N value := by
 have actual := source_actual_stock_advance value t N
 change burnolQuarterZeroExtension (sourceFiniteDualPlus t (N+1) value : BurnolQuarterIntervalL2)+
  fourierL2 (burnolQuarterZeroExtension (sourceFiniteDualMinus t (N+1) value : BurnolQuarterIntervalL2))=_
 rw [actual.1,actual.2]
 change burnolQuarterZeroExtension
  ((sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)+(sourcePlusStockAdvance t N value : BurnolQuarterIntervalL2))+
  fourierL2 (burnolQuarterZeroExtension
   ((sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)+(sourceMinusStockAdvance t N value : BurnolQuarterIntervalL2)))=
  (burnolQuarterZeroExtension (sourceFiniteDualPlus t N value : BurnolQuarterIntervalL2)+
   fourierL2 (burnolQuarterZeroExtension (sourceFiniteDualMinus t N value : BurnolQuarterIntervalL2)))+
  (burnolQuarterZeroExtension (sourcePlusStockAdvance t N value : BurnolQuarterIntervalL2)+
   fourierL2 (burnolQuarterZeroExtension (sourceMinusStockAdvance t N value : BurnolQuarterIntervalL2)))
 simp only [map_add]
 module

/-- The same actual update moves source responsibility from tail to generated finite field without dropping either. -/
theorem source_actual_tail_pays_advance (value : BurnolL2) (t : ℝ) (N : Nat) :
 sourceRemainderDualField t N value=sourceFieldAdvance t N value+sourceRemainderDualField t (N+1) value := by
 have before := source_actual_field_finite_and_remainder value t N
 have after := source_actual_field_finite_and_remainder value t (N+1)
 rw [source_actual_field_advance] at after
 have same := before.symm.trans after
 exact add_left_cancel (same.trans (add_assoc _ _ _))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
