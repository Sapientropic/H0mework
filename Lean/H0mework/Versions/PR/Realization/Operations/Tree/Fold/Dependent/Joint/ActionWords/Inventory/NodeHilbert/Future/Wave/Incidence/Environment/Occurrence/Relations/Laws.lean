import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Occurrence.Relations.Source
import H0mework.Realization.Operations.Execution.Coefficients.Words
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedOccurrenceRelations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable {S : Type u} {A X : S → Type u} [∀ slot,AddCommGroup (A slot)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=A) (Var:=X) (sort:=slot))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem source_boundary : word frame occurrence=
 Finsupp.single (paid frame occurrence).raw 1-Finsupp.single (paid frame occurrence).state.1 1 :=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.relation_boundary (R:=ℤ) (paid frame occurrence)
theorem source_old_value : evaluation (R:=ℤ) (s:=slot) (before frame occurrence) (word frame occurrence)=0 :=
 (paid frame occurrence).state.2.relation_old (R:=ℤ)
theorem inverse_effect : (residualEquivRange
 (evaluation (R:=ℤ) (s:=slot) ((before frame occurrence)+(increment frame occurrence))) (inverse frame occurrence)).val=
 effectEvaluator (R:=ℤ) (s:=slot) (before frame occurrence) (increment frame occurrence) (word frame occurrence) :=
 (paid frame occurrence).state.2.updated_residual (R:=ℤ) (increment frame occurrence)
theorem pair_value : (raw frame occurrence).expression.eval (raw frame occurrence).environment=
 (0,effectEvaluator (R:=ℤ) (s:=slot) (before frame occurrence) (increment frame occurrence) (word frame occurrence)) := by
 rw [raw,eval_liftExpr,SourceOperationExecution.Coefficients.expression_eval,
  SourceOperationExecution.Coefficients.expression_effect,source_old_value]
end SourceGeneratedOccurrenceRelations
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
variable (frame : Frame.{u})
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
theorem source_boundary : type_of% (SourceGeneratedOccurrenceRelations.source_boundary frame occurrence) :=
 SourceGeneratedOccurrenceRelations.source_boundary frame occurrence
theorem source_old_value : type_of% (SourceGeneratedOccurrenceRelations.source_old_value frame occurrence) :=
 SourceGeneratedOccurrenceRelations.source_old_value frame occurrence
theorem inverse_effect : type_of% (SourceGeneratedOccurrenceRelations.inverse_effect frame occurrence) :=
 SourceGeneratedOccurrenceRelations.inverse_effect frame occurrence
theorem pair_value : type_of% (SourceGeneratedOccurrenceRelations.pair_value frame occurrence) :=
 SourceGeneratedOccurrenceRelations.pair_value frame occurrence
theorem source_value : (result frame occurrence).2.2.1=
 (0,(residualEquivRange (evaluation (R:=ℤ) (s:=Slot.orbit) ((before frame occurrence)+(increment frame occurrence)))
  (inverse frame occurrence)).val) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot (reader frame) occurrence).trans
 ((pair_value frame occurrence).trans (congrArg (fun effect : Value.{u} Slot.orbit => ((0:Value.{u} Slot.orbit),effect))
  (inverse_effect frame occurrence).symm))
theorem cost : (result frame occurrence).2.1.2.length=SourceOperationExecution.Coefficients.cost (word frame occurrence) :=
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_history _ _ _).trans
  (SourceOperationExecution.Coefficients.lifted_remaining _)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Occurrence.Relations
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
