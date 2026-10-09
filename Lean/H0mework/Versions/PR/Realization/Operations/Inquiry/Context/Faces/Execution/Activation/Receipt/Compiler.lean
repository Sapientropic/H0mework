import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Execution
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Target
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift DebtActivationWorld
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
def compilation (candidate : (old frame configuration).Query) : SourceNativeInquiryCompilationProgramAt
 (old frame configuration).root (old frame configuration).visit (old frame configuration).U7 (old frame configuration).calculus
 (old frame configuration).root.source.base.lawSurface candidate ((old frame configuration).emitInquiry candidate)
 ((old frame configuration).entryAt candidate) ((old frame configuration).authorityAt candidate) where
 compile := fun event => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame configuration candidate
  exact .debtAdmission ((birthProgram frame configuration).generate event)
def state : RootInquiryStateAt
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
 (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
 root := (old frame configuration).root
 visit := (old frame configuration).visit
 U7 := (old frame configuration).U7
 calculus := (old frame configuration).calculus
 Query := (old frame configuration).Query
 entryAt := (old frame configuration).entryAt
 authorityAt := (old frame configuration).authorityAt
 compilationProgramAt := compilation frame configuration
 compilationFaceAt := fun candidate => by
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame configuration candidate
  exact { projection := ((old frame configuration).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)).projection
          active := ((old frame configuration).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)).active
          classifier_eq := ((old frame configuration).compilationFaceAt (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)).classifier_eq
          project_heq := HEq.rfl }
 u7RootDisposition_commutes := by
  intro candidate _ _ impossible
  cases SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query_unique frame configuration candidate
  exact nomatch impossible
theorem same_root : (state frame configuration).root=(old frame configuration).root := rfl
theorem same_visit : (state frame configuration).visit=(old frame configuration).visit := rfl
theorem compiles : (state frame configuration).compileInquiry
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query frame configuration)=
 .debtAdmission (generatedAction frame configuration) := rfl
end SourceGeneratedInquiryReceiptAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
