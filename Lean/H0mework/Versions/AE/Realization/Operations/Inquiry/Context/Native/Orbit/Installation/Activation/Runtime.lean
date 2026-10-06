import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Source
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Runtime

/-! The occurrence-owned orbit programme activates the existing inquiry
engine. Its complete material face is retained through the query families. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
open RootInquiryCompletion SourceOperationEffects
namespace A
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (frames runtime state presentation query visit root base baseRoot queryRoot resultRoot consumerRoot
   baseInstallation queryLaw resultLaw consumerLaw compilationLaw actual_node actual_next actual_query actual_answer)
end S
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (initial : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev frames := S.frames initial programme
abbrev runtime := S.runtime initial programme

theorem actual_node (count : Nat) : ((runtime initial).stateAt count).engine.node =
    .active (S.presentation (frames initial count) programme) := S.actual_node initial programme count

theorem actual_next (count : Nat) : ((runtime initial).tickAt count).next.node =
    .active (S.presentation (frames initial (count + 1)) programme) := S.actual_next initial programme count

theorem actual_query (count : Nat) : HEq ((runtime initial).stateAt count).activation.query
    (S.query (frames initial count) programme) := S.actual_query initial programme count

theorem actual_answer (count : Nat) : HEq ((runtime initial).tickAt count).answer
    ((S.state (frames initial count) programme).compileInquiry
      (S.query (frames initial count) programme)).answerReadout := S.actual_answer initial programme count

variable (frame : A.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def materialInstallation :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (S.base frame).root.source.base
    (component (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame))).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.baseRoot frame programme).source.base
    (S.queryLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.queryRoot frame programme).source.base
    (S.resultLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.resultRoot frame programme).source.base
    (S.consumerLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (S.consumerRoot frame programme).source.base
    (S.compilationLaw (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) programme))

def materialFace : SourceNativeRootSemanticFaceAt (S.root frame programme) (S.visit frame programme) where
  projection := (materialInstallation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem query_raw : (S.query frame programme).raw = (materialFace frame).rootRead.pairRaw := rfl

end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
