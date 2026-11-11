import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialAction.Material
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
variable (oldRaw nextRaw : O.Raw (Value:=Value) (Var:=Var) (sort:=()))

/-- The actual generated syntax word pays the difference between the two source expressions at the same new environment. -/
theorem source_raw_syntax_value :
 (sourceRawDeltaTerm oldRaw nextRaw).eval nextRaw.environment=
 nextRaw.expression.eval nextRaw.environment-oldRaw.expression.eval nextRaw.environment := by
 change (SourceOperationInquiry.Context.Faces.Execution.expression (sourceRawDeltaWord oldRaw nextRaw)).eval nextRaw.environment=_
 rw [SourceOperationInquiry.Context.Faces.Execution.expression_eval]
 simp only [sourceRawDeltaWord,map_sub,evaluation,Finsupp.linearCombination_single,one_smul]

/-- Both old and effect feet of the same syntax word remain explicit. -/
theorem source_raw_syntax_pair :
 ((liftExpr (sourceRawDeltaTerm oldRaw nextRaw)).eval (sourceRawPairEnvironment oldRaw nextRaw)).1+
 ((liftExpr (sourceRawDeltaTerm oldRaw nextRaw)).eval (sourceRawPairEnvironment oldRaw nextRaw)).2=
 (sourceRawDeltaTerm oldRaw nextRaw).eval nextRaw.environment := by
 have pair:=eval_liftExpr (sourceRawDeltaTerm oldRaw nextRaw) oldRaw.environment (sourceRawIncrement oldRaw nextRaw)
 have total:=(Expr.eval_update (sourceRawDeltaTerm oldRaw nextRaw) oldRaw.environment (sourceRawIncrement oldRaw nextRaw)).symm
 have env : oldRaw.environment+sourceRawIncrement oldRaw nextRaw=nextRaw.environment := add_sub_cancel _ _
 exact (congrArg (fun value : PairValue Value ()=>value.1+value.2) pair).trans
  (total.trans (congrArg (sourceRawDeltaTerm oldRaw nextRaw).eval env))

/-- The source primitive action generates complete old/change roles before reading an output equation. -/
theorem source_raw_differential_faces :
 (sourceRawDifferentialCode oldRaw nextRaw).eval (sourceRawPairEnvironment oldRaw nextRaw)=
 (oldRaw.expression.eval oldRaw.environment,
  oldRaw.expression.effect oldRaw.environment (sourceRawIncrement oldRaw nextRaw)+
  (sourceRawDeltaTerm oldRaw nextRaw).eval nextRaw.environment) := by
 have pair:=eval_liftExpr oldRaw.expression oldRaw.environment (sourceRawIncrement oldRaw nextRaw)
 have first : (sourceRawDifferentialCode oldRaw nextRaw).eval (sourceRawPairEnvironment oldRaw nextRaw)=
  (oldRaw.expression.eval oldRaw.environment,oldRaw.expression.effect oldRaw.environment (sourceRawIncrement oldRaw nextRaw))+
  sourceRawSyntaxInjection ((liftExpr (sourceRawDeltaTerm oldRaw nextRaw)).eval (sourceRawPairEnvironment oldRaw nextRaw)) :=
  congrArg (fun value=>value+sourceRawSyntaxInjection ((liftExpr (sourceRawDeltaTerm oldRaw nextRaw)).eval
   (sourceRawPairEnvironment oldRaw nextRaw))) pair
 have syntaxRead : sourceRawSyntaxInjection ((liftExpr (sourceRawDeltaTerm oldRaw nextRaw)).eval
   (sourceRawPairEnvironment oldRaw nextRaw))=(0,(sourceRawDeltaTerm oldRaw nextRaw).eval nextRaw.environment) :=
  congrArg (fun value : Value ()=>((0:Value ()),value)) (source_raw_syntax_pair oldRaw nextRaw)
 exact first.trans ((congrArg (fun value=>(oldRaw.expression.eval oldRaw.environment,
  oldRaw.expression.effect oldRaw.environment (sourceRawIncrement oldRaw nextRaw))+value) syntaxRead).trans
  (by apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,add_zero]))

/-- Complete source environmental and syntax actions recover the next source total without erasing either fee. -/
theorem source_raw_differential_actual_change :
 (sourceRawDifferentialCode oldRaw nextRaw).eval (sourceRawPairEnvironment oldRaw nextRaw)=
 (oldRaw.expression.eval oldRaw.environment,nextRaw.expression.eval nextRaw.environment-oldRaw.expression.eval oldRaw.environment) := by
 rw [source_raw_differential_faces,source_raw_syntax_value]
 have effect:=Expr.eval_update oldRaw.expression oldRaw.environment (sourceRawIncrement oldRaw nextRaw)
 have env : oldRaw.environment+sourceRawIncrement oldRaw nextRaw=nextRaw.environment := add_sub_cancel _ _
 rw [env] at effect
 apply Prod.ext
 · rfl
 · dsimp only [Prod.snd]
   rw [effect]
   abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
