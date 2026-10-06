import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Installation
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable (initialFrame : Frame.{u})
theorem whole_word_recovery (stage : Nat) (word : Carrier initialFrame) :
 recover initialFrame ((generated initialFrame stage).canonical word)=word := recover_source initialFrame word
theorem faithful_pairing : Function.Injective (pairing initialFrame) := SourceGeneratedCompleteWordDual.injective
theorem actual_point_next (stage : Nat) :
 sourceAction initialFrame ((generated initialFrame stage).canonical
  (SourceOperationInquiry.point (runtime initialFrame) ((runtime initialFrame).stateAt stage)))=
 (generated initialFrame stage).canonical (SourceOperationInquiry.point (runtime initialFrame) ((runtime initialFrame).stateAt (stage+1))) :=
 (source_action initialFrame _).trans
  (congrArg (generated initialFrame stage).canonical (SourceOperationInquiry.actual_point_action (runtime initialFrame) stage))
theorem pair_keeps_typed (stage : Nat) (first second : (runtime initialFrame).State)
 (same : (generated initialFrame stage).canonical (SourceOperationInquiry.point (runtime initialFrame) first)=
   (generated initialFrame stage).canonical (SourceOperationInquiry.point (runtime initialFrame) second)) :
 HEq first.activation.query second.activation.query ∧ HEq first.activation.origin second.activation.origin ∧
 HEq first.tick.resolution second.tick.resolution ∧ HEq first.tick.receipt second.tick.receipt := by
 have points := congrArg (recover initialFrame) same
 rw [whole_word_recovery,whole_word_recovery] at points
 have states := Finsupp.single_left_injective (one_ne_zero : (1:ℤ)≠0) points
 cases states
 exact ⟨HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩
theorem canonical_next (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_next initialFrame programme stage
theorem actual_query (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_query initialFrame programme stage
theorem actual_answer (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initialFrame programme stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_answer initialFrame programme stage
theorem whole_current (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.macro_current programme initialFrame stage
theorem same_debt (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme (Shared.frames initialFrame programme stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.no_refill programme _
theorem noetherian (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme (Shared.frames initialFrame programme stage)) :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.Payment.Shared.wellFounded programme _
theorem installed_query (stage : Nat) :
 ((sourceFace (Shared.frames initialFrame programme stage)).rootRead.2.2.2).2.2.1=
 (PaidSourceMacroHistory.programme.{u}.eval (A.epoch (Shared.frames initialFrame programme stage)).rawRead.environment,
 PaidSourceMacroHistory.programme.{u}.effect (A.epoch (Shared.frames initialFrame programme stage)).rawRead.environment
  (localEnvironment (A.epoch (Shared.frames initialFrame programme stage))-(A.epoch (Shared.frames initialFrame programme stage)).rawRead.environment)) :=
 query_value (A.epoch (Shared.frames initialFrame programme stage))
abbrev actualGenerated := (installedGenerated initialFrame,
 fun stage => (sourceFace (Shared.frames initialFrame programme stage),
  ((generated (Shared.frames initialFrame programme stage) 0).canonical,
   (generated (Shared.frames initialFrame programme stage) 0).embedding)))
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
