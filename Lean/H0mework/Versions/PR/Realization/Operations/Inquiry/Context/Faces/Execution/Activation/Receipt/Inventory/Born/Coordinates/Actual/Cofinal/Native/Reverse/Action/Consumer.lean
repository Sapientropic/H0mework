import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
attribute [local instance] Reverse.valueGroup
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
variable (sourceStage stage : Nat)
theorem original_boundary : type_of% ((trace frame configuration sourceStage stage).relation_boundary (R:=ℤ)) :=
 (trace frame configuration sourceStage stage).relation_boundary (R:=ℤ)
theorem original_zero : evaluation (R:=ℤ) (environment frame configuration sourceStage stage)
 (boundary frame configuration sourceStage stage)=0 := (trace frame configuration sourceStage stage).relation_old (R:=ℤ)
theorem complete_residual : type_of% ((trace frame configuration sourceStage stage).updated_residual (R:=ℤ)
 (increment frame configuration sourceStage stage)) := (trace frame configuration sourceStage stage).updated_residual (R:=ℤ) _
theorem generated_cochain : type_of% ((trace frame configuration sourceStage stage).relation_cochain (R:=ℤ)
 (increment frame configuration sourceStage stage)) := (trace frame configuration sourceStage stage).relation_cochain (R:=ℤ) _
theorem action_boundary_square : type_of% (SourceSubstitution.boundary_square (R:=ℤ) (s:=slot)
 O.binding (environment frame configuration sourceStage stage)) := SourceSubstitution.boundary_square O.binding _
def actionComplex := SourceSubstitution.complexMorphism (R:=ℤ) (s:=slot)
 O.binding (environment frame configuration sourceStage stage)
theorem actual_next_environment : SourceSubstitution.sourceEnvironment O.binding
 (environment frame configuration sourceStage stage)=P.environment (Reverse.runtime frame configuration sourceStage)
 (Reverse.source frame configuration sourceStage)
 (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState) :=
 P.binding_point _ _ _
theorem query_pair : (result frame configuration sourceStage stage).2.2.1=
 (evaluation (R:=ℤ) (P.environment (Reverse.runtime frame configuration sourceStage)
    (Reverse.source frame configuration sourceStage)
    (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState))
   (boundary frame configuration sourceStage stage),
 effectEvaluator (R:=ℤ) (P.environment (Reverse.runtime frame configuration sourceStage)
    (Reverse.source frame configuration sourceStage)
    (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState))
   (P.environment (Reverse.runtime frame configuration sourceStage) (Reverse.source frame configuration sourceStage)
    (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState.tick.nextState-
     SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState))
   (boundary frame configuration sourceStage stage)) := by
 have paid := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (baseRoot frame configuration sourceStage stage).toAuthoritativeRoot (reader frame configuration sourceStage stage)
  (Reverse.occurrence frame configuration sourceStage stage)
 have sourcePair := eval_liftExpr (nextExpression frame configuration sourceStage stage)
  (environment frame configuration sourceStage stage) (increment frame configuration sourceStage stage)
 apply paid.trans (sourcePair.trans _)
 change (((sourceExpression frame configuration sourceStage stage).subst O.binding).eval _,
  ((sourceExpression frame configuration sourceStage stage).subst O.binding).effect _ _)=_
 rw [Expr.eval_subst,Expr.effect_subst]
 change ((sourceExpression frame configuration sourceStage stage).eval
  (SourceSubstitution.sourceEnvironment O.binding (environment frame configuration sourceStage stage)),
  (sourceExpression frame configuration sourceStage stage).effect
  (SourceSubstitution.sourceEnvironment O.binding (environment frame configuration sourceStage stage))
  (fun sort name => (O.binding sort name).effect (environment frame configuration sourceStage stage)
    (increment frame configuration sourceStage stage)))=_
 rw [actual_next_environment]
 have changeEnv : (fun sort name => (O.binding sort name).effect (environment frame configuration sourceStage stage)
  (increment frame configuration sourceStage stage))=P.environment (Reverse.runtime frame configuration sourceStage)
  (Reverse.source frame configuration sourceStage)
  (SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState.tick.nextState-
   SourceOperationInquiry.point _ (state frame configuration sourceStage stage).tick.nextState) := P.binding_difference _ _ _
 rw [changeEnv]
 exact congrArg₂ Prod.mk (SourceOperationExecution.Coefficients.expression_eval _ _)
  (SourceOperationExecution.Coefficients.expression_effect _ _ _)
private theorem inverse_read_value {T : Type u} {A X : T → Type u} [∀ t,AddCommGroup (A t)]
 {t : T} (env : Env A X) (word : Formal ℤ A X t) :
 (residualEquivRange (evaluation (R:=ℤ) env)
  (canonicalResidual (evaluation (R:=ℤ) env) word)).val=evaluation (R:=ℤ) env word := rfl
theorem inverse_read : (result frame configuration sourceStage stage).2.2.1.1=
 (residualEquivRange (nextEvaluation frame configuration sourceStage stage)
  (inverse frame configuration sourceStage stage)).val := by
 exact (congrArg Prod.fst (query_pair frame configuration sourceStage stage)).trans
  (inverse_read_value _ _).symm
theorem inverse_installed : (sourceFace frame configuration sourceStage stage).rootRead.2.2.2.2.1=
 inverse frame configuration sourceStage stage := rfl
theorem actual_reader : reader frame configuration sourceStage stage (Reverse.occurrence frame configuration sourceStage stage)=
 (sourceFace frame configuration sourceStage stage).rootRead.2.2.2.2.2 := rfl
theorem installed_result : (queryFace frame configuration sourceStage stage).rootRead=result frame configuration sourceStage stage := rfl
theorem exact_cost : (result frame configuration sourceStage stage).2.1.2.length=
 remaining (raw frame configuration sourceStage stage).expression := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _
theorem source_ledger : (queryRoot frame configuration sourceStage stage).toAuthoritativeRoot.toLedgerRoot=
 (Reverse.original frame configuration sourceStage stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem whole_first : type_of% (SourceGeneratedInquiryReceiptAction.whole_first (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.whole_first _ _
theorem literal_next : type_of% (SourceGeneratedInquiryReceiptAction.literal_next (queryFrame frame configuration sourceStage stage)
 SourceOperationInquiry.Context.Faces.Execution.Activation.originalProgramme) := SourceGeneratedInquiryReceiptAction.literal_next _ _
theorem first_whole : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
 (queryRoot frame configuration sourceStage stage) (Reverse.original frame configuration sourceStage stage).visit
 (Reverse.original frame configuration sourceStage stage).U7 (Reverse.original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt _ _ _ _ _
theorem first_next : type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
 (queryRoot frame configuration sourceStage stage) (Reverse.original frame configuration sourceStage stage).visit
 (Reverse.original frame configuration sourceStage stage).U7 (Reverse.original frame configuration sourceStage stage).calculus
 (reader frame configuration sourceStage stage)) := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next _ _ _ _ _
abbrev nativeGenerated (nativeStage : Nat) := (Reverse.nativeGenerated frame configuration nativeStage,
 fun sourceStage stage => generated (Faces.Native.nativeFrame frame configuration nativeStage) Faces.Native.R.programme sourceStage stage)
end SourceGeneratedInquiryReceiptAction.Inventory.Born.Coordinates.Actual.Cofinal.Native.Reverse.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
