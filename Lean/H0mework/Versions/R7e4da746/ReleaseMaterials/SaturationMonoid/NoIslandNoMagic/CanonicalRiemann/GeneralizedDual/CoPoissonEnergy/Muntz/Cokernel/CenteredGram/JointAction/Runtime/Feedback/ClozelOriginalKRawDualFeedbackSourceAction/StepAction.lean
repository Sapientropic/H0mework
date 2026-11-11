import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Advance
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
open Complex BurnolPhysicalState OriginalKMaterialExpandedDualSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open scoped InnerProductSpace

def sourceStepMaterialAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp ((sourceFieldAdvance t N).comp OriginalKFullSourceRAction.originalField)

def sourceRawPowerPlusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((plusFeedback^N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

def sourceRawPowerMinusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((minusFeedback^N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

def sourceStepCode (t : ℝ) (N : Nat) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawPowerPlusAction t N).toLinearMap.toAddMonoidHom (.var ())))
  (.linear (s:=()) (t:=()) sourceDualFourierAction.toLinearMap.toAddMonoidHom
   (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawPowerMinusAction t N).toLinearMap.toAddMonoidHom (.var ()))))

private theorem source_step_own_compact_read (source : BurnolQuarterMeanZeroCarrier) :
 OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction (OriginalKCvelSourceAction.actualStockExtension source))=source := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=(source : BurnolQuarterIntervalL2)
 rw [burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]

private theorem source_step_even_code_read
 (raw : Expr (PairValue (PairValue C.Value)) C.Var ())
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceOwnEvenCode raw).eval environment=sourceOwnEvenAction (raw.eval environment) := by
 change raw.eval environment+sourceDualNegativeAction (sourceRawOwnOddAction (raw.eval environment))=_
 simp only [sourceDualNegativeAction,sourceRawOwnOddAction,sub_apply,neg_apply,ContinuousLinearMap.id_apply,←sub_eq_add_neg,sub_sub_cancel]

theorem source_step_code_read (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceStepCode t N).eval environment=sourceStepMaterialAction t N (environment () ()) := by
 change (sourceOwnEvenCode _).eval environment+sourceDualFourierAction ((sourceOwnEvenCode _).eval environment)=_
 rw [source_step_even_code_read,source_step_even_code_read]
 change sourceOwnEvenAction (sourceRawPowerPlusAction t N (environment () ()))+
  sourceDualFourierAction (sourceOwnEvenAction (sourceRawPowerMinusAction t N (environment () ())))=_
 unfold sourceOwnEvenAction sourceRawPowerPlusAction sourceRawPowerMinusAction
 simp only [ContinuousLinearMap.comp_apply]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
   (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
    (OriginalKCvelSourceAction.actualStockExtension ((plusFeedback^N) (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ())))))))))+
  OriginalKBoundaryNativeSourceAction.sourceFields (fourierL2
   (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
    (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
     (OriginalKCvelSourceAction.actualStockExtension ((minusFeedback^N) (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ()))))))))))=_
 rw [source_step_own_compact_read,source_step_own_compact_read,←map_add]
 rfl

/-- The next actual calculation is the old finite source stock plus its generated signed-power update, not the full finite+tail value. -/
def sourceNextFiniteCode (t : ℝ) (N : Nat) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (sourceFiniteCode t N) (sourceStepCode t N)

theorem source_next_finite_code_read (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceNextFiniteCode t N).eval environment=sourceFiniteMaterialAction t (N+1) (environment () ()) := by
 change (sourceFiniteCode t N).eval environment+(sourceStepCode t N).eval environment=_
 rw [source_finite_code_read,source_step_code_read]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (sourceFiniteDualField t N (OriginalKFullSourceRAction.originalField (environment () ())))+
  OriginalKBoundaryNativeSourceAction.sourceFields
  (sourceFieldAdvance t N (OriginalKFullSourceRAction.originalField (environment () ())))=_
 rw [←map_add,←source_actual_field_advance]
 rfl

/-- The generated native update's exact source delta is the signed power, and the separate next tail retains all remaining source responsibility. -/
theorem source_next_finite_code_actual_delta (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceNextFiniteCode t N).eval environment-(sourceFiniteCode t N).eval environment=
 sourceStepMaterialAction t N (environment () ()) := by
 change (sourceFiniteCode t N).eval environment+(sourceStepCode t N).eval environment-
  (sourceFiniteCode t N).eval environment=_
 rw [source_step_code_read]
 exact add_sub_cancel_left _ _

theorem source_next_finite_code_effect (t : ℝ) (N : Nat)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceNextFiniteCode t N).effect environment increment=sourceFiniteMaterialAction t (N+1) (increment () ()) := by
 have generated := Expr.eval_update (sourceNextFiniteCode t N) environment increment
 rw [source_next_finite_code_read,source_next_finite_code_read] at generated
 change sourceFiniteMaterialAction t (N+1) (environment () ()+increment () ())=_ at generated
 rw [map_add] at generated
 exact add_left_cancel generated.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
