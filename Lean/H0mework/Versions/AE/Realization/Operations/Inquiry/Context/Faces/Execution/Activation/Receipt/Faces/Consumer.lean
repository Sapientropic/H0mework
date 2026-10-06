import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Faces.Action
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Faces
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
theorem dual_equation (stage : Nat) : (generated frame configuration stage).embedding.comp
 (generated frame configuration stage).canonical=pairing frame configuration :=
 UnifiedFourFace.generated_dual_readback (input frame configuration stage)
theorem same_occurrence (stage : Nat) : (input frame configuration stage).occurrence.root.1=occurrence frame configuration stage := rfl
theorem original_raw (stage : Nat) : actualRaw frame configuration stage=(frameAt frame configuration stage).rawRead :=
 SourceOperationInquiry.Context.Installation.raw_actual (bornFrame frame configuration) stage
theorem actual_operation (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.actual_operation_receipt (runtime frame configuration) (source frame configuration)
  ((runtime frame configuration).stateAt stage)) := SourceOperationInquiry.Context.actual_operation_receipt _ _ _
theorem complete_word (stage : Nat)
 (word : SourceOperationScalarRelations.Formal ℤ (PairValue PhysicalValue) configuration.LowVar slot) :
 (logic frame configuration stage).symm (logic frame configuration stage word)=word :=
 (logic frame configuration stage).symm_apply_apply word
theorem cofinal_word (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback (runtime frame configuration)
  (source frame configuration) stage) := SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback _ _ stage
theorem cofinal_next (stage bound : Nat) (index : Fin (bound+1)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read (runtime frame configuration)
  (source frame configuration) stage bound index) := SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read _ _ stage bound index
theorem query_value (stage : Nat) :
 (query frame configuration stage).2.2.1=SourceOperationInquiry.Context.pairValue
  (runtime frame configuration) (source frame configuration) ((runtime frame configuration).stateAt stage) := by
 apply (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value _ _ _).trans
 unfold queryRaw
 rw [next_environment]
 rfl
theorem query_original_next (stage : Nat) :
 (actualRaw frame configuration stage).expression.eval
  (nextEnvironmentRead frame configuration ((runtime frame configuration).stateAt stage))=
 (query frame configuration stage).2.2.1.1+(query frame configuration stage).2.2.1.2 := by
 have value := query_value frame configuration stage
 have next := SourceOperationInquiry.Context.next_value (runtime frame configuration)
  (source frame configuration) ((runtime frame configuration).stateAt stage)
 exact (congrArg ((actualRaw frame configuration stage).expression.eval)
  (next_environment frame configuration ((runtime frame configuration).stateAt stage))).trans
   (next.trans (congrArg (fun pair : PairValue (PairValue PhysicalValue) slot => pair.1+pair.2) value).symm)
theorem installed_query (stage : Nat) : (queryFace frame configuration stage).rootRead=query frame configuration stage := rfl
theorem query_ledger (stage : Nat) : (queryRoot frame configuration stage).toAuthoritativeRoot.toLedgerRoot=
 (original frame configuration stage).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem installed_value (stage : Nat) : (queryFace frame configuration stage).rootRead.2.2.1=
 SourceOperationInquiry.Context.pairValue (runtime frame configuration) (source frame configuration)
  ((runtime frame configuration).stateAt stage) := query_value frame configuration stage
theorem query_first_whole (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_first_receipt
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage)
theorem query_first_next (stage : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage)) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.residual_frame_next
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage)
theorem query_runtime_next (stage offset : Nat) : type_of%
 (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage) offset) :=
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.activated_next
  (queryRoot frame configuration stage) (original frame configuration stage).visit
  (original frame configuration stage).U7 (original frame configuration stage).calculus
  (fun _ => queryRaw frame configuration stage) offset
abbrev actualGenerated := (SourceGeneratedInquiryReceiptAction.actualGenerated frame configuration,
 source frame configuration,fun stage => (queryFace frame configuration stage,queryRuntime frame configuration stage,
 (generated frame configuration stage).canonical,(generated frame configuration stage).embedding))
end SourceGeneratedInquiryReceiptAction.Faces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
