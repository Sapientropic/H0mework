import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Frame
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Successor.Inquiry.Consumer

/-! A residual birth consumes the installed current's generated request and
self programme. Ordinary actions continue the same source at its next visit. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
open SourceOperationEffects RootInquiryCompletion
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def material (source : frame.Occurrence) :=
  Inquiry.Source.material frame.old frame.registered frame.packetAt frame.environment frame.depth source

def request := Inquiry.Source.request frame.old frame.registered frame.packetAt frame.environment frame.depth

def born : Frame (Value := Value) (Var := Var) (sort := sort) where
  N := CompilerFromPacketSourceLaw.World frame.registered
  V := CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
  old := frame.currentState
  registered := frame.request
  packetAt := Inquiry.Source.programme frame.old frame.registered frame.packetAt frame.depth
  environment := fun {_current} source => frame.environment
    (CompilerFromPacketSourceLaw.originalOccurrence frame.registered frame.packetAt source)
  depth := 0
  pairInventory := frame.pairInventory

theorem born_current : frame.born.currentState =
    Inquiry.Consumer.targetState frame.old frame.registered frame.packetAt frame.environment frame.depth := rfl

def mathNext : Frame (Value := Value) (Var := Var) (sort := sort) := { frame with depth := frame.depth + 1 }

def nextFrom (selected : frame.Action) : Frame (Value := Value) (Var := Var) (sort := sort) :=
  match selected with
  | .inl _ => frame.born
  | .inr _ => frame.mathNext

def next := frame.nextFrom frame.action

def birthPresentation := Inquiry.Consumer.sourcePresentation frame.old frame.registered frame.packetAt frame.environment frame.depth

def presentationFrom (selected : frame.Action) : RootInquiryStatePresentation :=
  match selected with
  | .inl _ => frame.birthPresentation
  | .inr _ => frame.currentPresentation

def presentation := frame.presentationFrom frame.action

theorem presentation_erase : frame.presentation.erase = frame.currentPresentation.erase := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

theorem presentation_root : HEq frame.presentation.state.base.root frame.currentState.root := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

theorem presentation_query : frame.presentation.Query = PUnit := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

def query : frame.presentation.Query := Eq.mpr frame.presentation_query PUnit.unit

theorem query_unique (candidate : frame.presentation.Query) : candidate = frame.query := by
  let : Subsingleton frame.presentation.Query := Eq.mpr
    (congrArg (fun query : Type u => Subsingleton query) frame.presentation_query)
    (inferInstance : Subsingleton PUnit)
  exact Subsingleton.elim candidate frame.query

theorem request_budget : SourceOperationExecution.remaining frame.request.input.expression =
    SourceOperationExecution.remaining frame.rawRead.expression +
      SourceOperationExecution.remaining frame.paidRead.state.1 + 2 :=
  Inquiry.Source.request_budget frame.old frame.registered frame.packetAt frame.environment frame.depth

end Frame

def frames (initial : Frame (Value := Value) (Var := Var) (sort := sort)) : Nat → Frame (Value := Value) (Var := Var) (sort := sort)
  | 0 => initial
  | count + 1 => (frames initial count).next

end RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
