import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Outgoing.Source

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Outgoing
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
variable (configuration : A.Programme (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort))

theorem current_reader : currentRaw frame configuration =
 (Faces.Execution.Activation.Shared.datum frame configuration).reader (A.Shared.actualOccurrence frame) := rfl
theorem next_reader : nextRaw frame configuration =
 (Faces.Execution.Activation.Shared.datum (successor frame configuration) configuration).reader
  (A.Shared.actualOccurrence (successor frame configuration)) := rfl

theorem main_value : (mainResult frame configuration).2.2.1 =
 (currentRaw frame configuration).expression.eval (currentRaw frame configuration).environment :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _
theorem main_fee : (mainTrace frame configuration).length = remaining (currentRaw frame configuration).expression :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem main_occurrence : (mainResult frame configuration).2.2.2 =
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (Faces.Execution.Activation.Shared.baseRoot frame configuration).toAuthoritativeRoot (A.Shared.actualOccurrence frame) := rfl

theorem correction_value : scalarValue frame configuration=correction frame configuration :=
 Faces.Execution.expression_eval _ _
theorem correction_difference : correction frame configuration =
 (nextRaw frame configuration).expression.eval (nextRaw frame configuration).environment -
 (currentRaw frame configuration).expression.eval (nextRaw frame configuration).environment := by
 simp only [correction,deltaWord,currentWord,nextWord,map_sub,evaluation,Finsupp.linearCombination_single,one_smul]

theorem pair_old_effect : pairValue frame configuration =
 ((deltaTerm frame configuration).eval (currentRaw frame configuration).environment,
  (deltaTerm frame configuration).effect (currentRaw frame configuration).environment (increment frame configuration)) :=
 eval_liftExpr _ _ _
theorem pair_addition : (pairValue frame configuration).1+(pairValue frame configuration).2 =
 scalarValue frame configuration := by
 rw [pair_old_effect,←Expr.eval_update]
 exact congrArg (deltaTerm frame configuration).eval (add_sub_cancel _ _)

theorem moving_equation : (nextRaw frame configuration).expression.eval (nextRaw frame configuration).environment-
 (mainResult frame configuration).2.2.1 =
 (currentRaw frame configuration).expression.effect (currentRaw frame configuration).environment (increment frame configuration) +
 scalarValue frame configuration := by
 have effect := Expr.eval_update (currentRaw frame configuration).expression (currentRaw frame configuration).environment
  (increment frame configuration)
 have env : (currentRaw frame configuration).environment+increment frame configuration=(nextRaw frame configuration).environment :=
  add_sub_cancel _ _
 rw [env] at effect
 rw [main_value,correction_value,correction_difference,effect]
 abel

theorem scalar_fee : (deltaScalarTrace frame configuration).length=remaining (deltaTerm frame configuration) := execution_length _ _
theorem pair_fee : (deltaPairTrace frame configuration).length=remaining (pairTerm frame configuration) := execution_length _ _
theorem next_syntax_fee : (nextSyntaxTrace frame configuration).length=remaining (nextRaw frame configuration).expression := execution_length _ _

theorem scalar_boundary : relationMap (R:=ℤ) (nextRaw frame configuration).environment
 ((deltaScalarTrace frame configuration).relationWords (R:=ℤ)) =
 Finsupp.single (deltaTerm frame configuration) 1-Finsupp.single (.const (scalarValue frame configuration)) 1 :=
 (deltaScalarTrace frame configuration).relation_boundary

theorem pair_boundary : relationMap (R:=ℤ) (pairEnvironment frame configuration)
 ((deltaPairTrace frame configuration).relationWords (R:=ℤ)) =
 Finsupp.single (pairTerm frame configuration) 1-Finsupp.single (.const (pairValue frame configuration)) 1 :=
 (deltaPairTrace frame configuration).relation_boundary

theorem next_boundary : relationMap (R:=ℤ) (nextRaw frame configuration).environment
 ((nextSyntaxTrace frame configuration).relationWords (R:=ℤ)) =
 Finsupp.single (nextRaw frame configuration).expression 1-
 Finsupp.single (.const ((nextRaw frame configuration).expression.eval (nextRaw frame configuration).environment)) 1 :=
 (nextSyntaxTrace frame configuration).relation_boundary

theorem main_updated_residual : type_of% ((mainTrace frame configuration).updated_residual (R:=ℤ) (increment frame configuration)) :=
 (mainTrace frame configuration).updated_residual (R:=ℤ) (increment frame configuration)
theorem main_relation_cochain : type_of% ((mainTrace frame configuration).relation_cochain (R:=ℤ) (increment frame configuration)) :=
 (mainTrace frame configuration).relation_cochain (R:=ℤ) (increment frame configuration)

theorem scalar_steps_complete : (SourceOperationPaidRelations.words (deltaScalarTrace frame configuration)).length =
 (deltaScalarTrace frame configuration).length := SourceOperationPaidRelations.complete_steps _
theorem pair_steps_complete : (SourceOperationPaidRelations.words (deltaPairTrace frame configuration)).length =
 (deltaPairTrace frame configuration).length := SourceOperationPaidRelations.complete_steps _
theorem next_steps_complete : (SourceOperationPaidRelations.words (nextSyntaxTrace frame configuration)).length =
 (nextSyntaxTrace frame configuration).length := SourceOperationPaidRelations.complete_steps _

theorem scalar_preserved (event) (present : event ∈ (scalarExposure frame configuration).trace) :
 event ∈ (scalarStock frame configuration).trace := (SourceHistoryCommon.parallel_left _ _ _).1 event present
theorem next_preserved (event) (present : event ∈ (nextSyntaxExposure frame configuration).trace) :
 event ∈ (scalarStock frame configuration).trace := (SourceHistoryCommon.parallel_right _ _ _).1 event present
theorem pair_preserved (event) (present : event ∈ (pairExposure frame configuration).trace) :
 event ∈ (pairStock frame configuration).trace := present

theorem scalar_relation_sound (word) (present : PresentedRelationEventAt.relation word ∈ (scalarExposure frame configuration).trace) :
 evaluation (R:=ℤ) (nextRaw frame configuration).environment word=0 := SourceOperationPaidRelations.exposure_sound _ _ present
theorem next_relation_sound (word) (present : PresentedRelationEventAt.relation word ∈ (nextSyntaxExposure frame configuration).trace) :
 evaluation (R:=ℤ) (nextRaw frame configuration).environment word=0 := SourceOperationPaidRelations.exposure_sound _ _ present

theorem successor_generated : successor frame configuration = A.Shared.next frame configuration := rfl

variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=sort))
theorem next_raw_at (count : Nat) : nextRaw
 (Faces.Execution.Activation.Shared.frames initial configuration count) configuration =
 currentRaw (Faces.Execution.Activation.Shared.frames initial configuration (count+1)) configuration := rfl

end SourceOperationInquiry.Context.Outgoing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
