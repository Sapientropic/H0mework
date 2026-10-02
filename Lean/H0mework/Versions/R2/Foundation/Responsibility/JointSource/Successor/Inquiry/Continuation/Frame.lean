import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Source

/-! An actual source frame retains its original inquiry, complete registered
request and occurrence environment reader. Its programme is source-generated. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
open SourceOperationEffects RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

structure Frame where
  N : WorldRelationNetwork.{u}
  V : Vocabulary.{u}
  old : RootInquiryStateAt N V
  registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current
  packetAt : (current : V.Current) → Packet old.root.toAuthoritativeRoot.toLedgerRoot current
  environment : {current : V.Current} →
    old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var
  depth : Nat

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def currentState := Inquiry.Source.currentState frame.old frame.registered frame.packetAt frame.depth

def currentPresentation : RootInquiryStatePresentation where
  N := CompilerFromPacketSourceLaw.World frame.registered
  V := CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
  state := .create frame.currentState

def event := (Inquiry.mathCurrent frame.old frame.registered frame.packetAt frame.depth).2
def action := mathAction frame.event
abbrev Action := SourceOperationExecutionDebt.Settlement frame.event.state ⊕
  DebtActivationWorld.GeneratedStepAt (Idle.law frame.registered.input.environment frame.registered.input.expression) frame.event.state

def rawRead := Inquiry.Source.rawRead frame.old frame.registered frame.packetAt frame.depth
def paidRead := Inquiry.Source.paidRead frame.old frame.registered frame.packetAt frame.depth
abbrev Occurrence := Inquiry.Source.Occurrence frame.old frame.registered frame.packetAt frame.depth

def environmentAt (source : frame.Occurrence) :=
  Inquiry.Source.environmentAt frame.old frame.registered frame.packetAt frame.environment frame.depth source

def activeEnvironment := frame.environmentAt (Inquiry.Source.actualOccurrence frame.old frame.registered frame.packetAt frame.depth)

theorem raw_environment : frame.rawRead.environment = frame.registered.input.environment := rfl
theorem raw_expression : frame.rawRead.expression = frame.registered.input.expression := rfl
theorem paid_state : frame.paidRead.state = frame.event.state := rfl
theorem paid_action : frame.paidRead.action = frame.action := rfl

end Frame
end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
