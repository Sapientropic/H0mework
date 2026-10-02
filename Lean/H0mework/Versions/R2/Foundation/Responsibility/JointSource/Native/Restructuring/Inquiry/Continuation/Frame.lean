import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Next
import H0mework.Foundation.Responsibility.JointSource.Native.ResidualRequest

/-! A frame owns an already-generated general request and the original
source environment reader. Its complete raw and paid state are root reads. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

structure Frame where
  N : WorldRelationNetwork.{u}
  V : Vocabulary.{u}
  old : RootInquiryStateAt N V
  program : Native.Program old.root.toAuthoritativeRoot.toLedgerRoot
  registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current
  environment : {current : V.Current} →
    old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var
  depth : Nat

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def currentState := Inquiry.mathState frame.old frame.program frame.registered frame.depth

def currentPresentation : RootInquiryStatePresentation where
  N := World frame.registered
  V := Native.JointV frame.program frame.registered
  state := .create frame.currentState

def event := (Inquiry.mathCurrent frame.old frame.program frame.registered frame.depth).2
def action := mathAction frame.event
abbrev Action := SourceOperationExecutionDebt.Settlement frame.event.state ⊕
  DebtActivationWorld.GeneratedStepAt
    (Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state

abbrev Occurrence := frame.currentState.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  frame.currentState.visit.current

def rawFace : SourceNativeRootSemanticFaceAt frame.currentState.root frame.currentState.visit where
  projection := (Inquiry.Assembly.rawInstallation frame.old frame.program frame.registered).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def rawRead : Native.Request.Registration.UniformRaw (Value := Value) (Var := Var) (sort := sort) :=
  frame.rawFace.rootRead

def paidRead := (Inquiry.mathAnswerFace frame.old frame.program frame.registered frame.depth).rootRead

def environmentAt (source : frame.Occurrence) :=
  frame.environment (Native.originalOccurrence frame.program frame.registered source)

def activeEnvironment := frame.environmentAt (frame.currentState.root.emitted frame.currentState.visit.current)

theorem raw_environment : frame.rawRead.environment = frame.registered.input.environment := rfl
theorem raw_expression : frame.rawRead.expression = frame.registered.input.expression := rfl
theorem paid_state : frame.paidRead.state = frame.event.state := rfl
theorem paid_action : frame.paidRead.action = frame.action := rfl

end Frame
end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
