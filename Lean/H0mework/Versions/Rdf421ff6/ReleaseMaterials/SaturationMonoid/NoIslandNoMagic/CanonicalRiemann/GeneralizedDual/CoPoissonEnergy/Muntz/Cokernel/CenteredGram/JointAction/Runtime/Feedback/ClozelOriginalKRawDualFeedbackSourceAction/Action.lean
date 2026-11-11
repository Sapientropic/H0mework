import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRawDualFeedbackSourceAction.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialExpandedDualSourceAction.Action
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

def sourceFiniteMaterialAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp ((sourceFiniteDualField t N).comp OriginalKFullSourceRAction.originalField)

def sourceRemainderMaterialAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp ((sourceRemainderDualField t N).comp OriginalKFullSourceRAction.originalField)

def sourceRawStockPlusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((plusSourceStock N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

def sourceRawStockMinusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((minusSourceStock N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

def sourceRawTailPlusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((plusSourceRemainder N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

def sourceRawTailMinusAction (t : ℝ) (N : Nat) : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  ((minusSourceRemainder N).comp ((sourceExpandedQuarterReader t).comp OriginalKFullSourceRAction.originalField)))

/-- The literal raw compact foot is evenized after its actual source operation; its odd field is retained as a node. -/
def sourceOwnEvenAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 OriginalKBoundaryNativeSourceAction.sourceFields.comp (OriginalKCvelSourceAction.actualStockExtension.comp
  (sourceDualEvenQuarter.comp (OriginalRieszSource.Constructor.zeroMean.comp
   (burnolQuarterRestriction.comp OriginalKFullSourceRAction.originalField))))

def sourceRawOwnOddAction : D.SourceBranches →L[ℂ] D.SourceBranches :=
 ContinuousLinearMap.id ℂ D.SourceBranches-sourceOwnEvenAction

def sourceOwnEvenCode (raw : Expr (PairValue (PairValue C.Value)) C.Var ()) :
 Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add raw (.linear (s:=()) (t:=()) sourceDualNegativeAction.toLinearMap.toAddMonoidHom
  (.linear (s:=()) (t:=()) sourceRawOwnOddAction.toLinearMap.toAddMonoidHom raw))

def sourceFiniteCode (t : ℝ) (N : Nat) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawStockPlusAction t N).toLinearMap.toAddMonoidHom (.var ())))
  (.linear (s:=()) (t:=()) sourceDualFourierAction.toLinearMap.toAddMonoidHom
   (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawStockMinusAction t N).toLinearMap.toAddMonoidHom (.var ()))))

def sourceRemainderCode (t : ℝ) (N : Nat) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add
  (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawTailPlusAction t N).toLinearMap.toAddMonoidHom (.var ())))
  (.linear (s:=()) (t:=()) sourceDualFourierAction.toLinearMap.toAddMonoidHom
   (sourceOwnEvenCode (.linear (s:=()) (t:=()) (sourceRawTailMinusAction t N).toLinearMap.toAddMonoidHom (.var ()))))

def sourceFeedbackCode (t : ℝ) (N : Nat) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .add (sourceFiniteCode t N) (sourceRemainderCode t N)

private theorem source_compact_own_read (source : BurnolQuarterMeanZeroCarrier) :
 OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction (OriginalKCvelSourceAction.actualStockExtension source))=source := by
 apply Subtype.ext
 change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (burnolQuarterZeroExtension (source : BurnolQuarterIntervalL2)))=(source : BurnolQuarterIntervalL2)
 rw [burnolQuarterRestriction_zeroExtension,burnolQuarterMeanZeroProjection_coe]

private theorem source_own_even_code_read
 (raw : Expr (PairValue (PairValue C.Value)) C.Var ())
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceOwnEvenCode raw).eval environment=sourceOwnEvenAction (raw.eval environment) := by
 change raw.eval environment+sourceDualNegativeAction (sourceRawOwnOddAction (raw.eval environment))=_
 simp only [sourceDualNegativeAction,sourceRawOwnOddAction,sub_apply,neg_apply,ContinuousLinearMap.id_apply,←sub_eq_add_neg,sub_sub_cancel]

/-- A finite source actor is emitted before its observer, with both raw/odd feet explicitly in the source AST. -/
theorem source_finite_code_read (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceFiniteCode t N).eval environment=sourceFiniteMaterialAction t N (environment () ()) := by
 change (sourceOwnEvenCode _).eval environment+sourceDualFourierAction ((sourceOwnEvenCode _).eval environment)=_
 rw [source_own_even_code_read,source_own_even_code_read]
 change sourceOwnEvenAction (sourceRawStockPlusAction t N (environment () ()))+
  sourceDualFourierAction (sourceOwnEvenAction (sourceRawStockMinusAction t N (environment () ())))=_
 unfold sourceOwnEvenAction sourceRawStockPlusAction sourceRawStockMinusAction
 simp only [ContinuousLinearMap.comp_apply]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
   (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
    (OriginalKCvelSourceAction.actualStockExtension (plusSourceStock N (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ())))))))))+
  OriginalKBoundaryNativeSourceAction.sourceFields (fourierL2
   (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
    (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
     (OriginalKCvelSourceAction.actualStockExtension (minusSourceStock N (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ()))))))))))=_
 rw [source_compact_own_read,source_compact_own_read,←map_add]
 rfl

/-- The same source inverse remainder is exposed separately and never reconstructed by a target scalar subtraction. -/
theorem source_remainder_code_read (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceRemainderCode t N).eval environment=sourceRemainderMaterialAction t N (environment () ()) := by
 change (sourceOwnEvenCode _).eval environment+sourceDualFourierAction ((sourceOwnEvenCode _).eval environment)=_
 rw [source_own_even_code_read,source_own_even_code_read]
 change sourceOwnEvenAction (sourceRawTailPlusAction t N (environment () ()))+
  sourceDualFourierAction (sourceOwnEvenAction (sourceRawTailMinusAction t N (environment () ())))=_
 unfold sourceOwnEvenAction sourceRawTailPlusAction sourceRawTailMinusAction
 simp only [ContinuousLinearMap.comp_apply]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
   (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
    (OriginalKCvelSourceAction.actualStockExtension (plusSourceRemainder N (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ())))))))))+
  OriginalKBoundaryNativeSourceAction.sourceFields (fourierL2
   (OriginalKCvelSourceAction.actualStockExtension (sourceDualEvenQuarter
    (OriginalRieszSource.Constructor.zeroMean (burnolQuarterRestriction
     (OriginalKCvelSourceAction.actualStockExtension (minusSourceRemainder N (sourceExpandedQuarterReader t (OriginalKFullSourceRAction.originalField (environment () ()))))))))))=_
 rw [source_compact_own_read,source_compact_own_read,←map_add]
 rfl

theorem source_feedback_code_read (t : ℝ) (N : Nat)
 (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceFeedbackCode t N).eval environment=sourceExpandedDualAction t (environment () ()) := by
 change (sourceFiniteCode t N).eval environment+(sourceRemainderCode t N).eval environment=_
 rw [source_finite_code_read,source_remainder_code_read]
 change OriginalKBoundaryNativeSourceAction.sourceFields _+OriginalKBoundaryNativeSourceAction.sourceFields _=_
 rw [←map_add]
 change OriginalKBoundaryNativeSourceAction.sourceFields
  (sourceFiniteDualField t N (OriginalKFullSourceRAction.originalField (environment () ()))+
   sourceRemainderDualField t N (OriginalKFullSourceRAction.originalField (environment () ())))=_
 rw [←source_actual_field_finite_and_remainder]
 rfl

theorem source_feedback_code_effect (t : ℝ) (N : Nat)
 (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceFeedbackCode t N).effect environment increment=sourceExpandedDualAction t (increment () ()) := by
 have generated := Expr.eval_update (sourceFeedbackCode t N) environment increment
 rw [source_feedback_code_read,source_feedback_code_read] at generated
 change sourceExpandedDualAction t (environment () ()+increment () ())=_ at generated
 rw [map_add] at generated
 exact add_left_cancel generated.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRawDualFeedbackSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
