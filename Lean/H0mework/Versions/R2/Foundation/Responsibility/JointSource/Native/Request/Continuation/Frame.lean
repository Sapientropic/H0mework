import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Request.Residual.Runtime

/-! An inquiry frame stores only an already-generated request and its original
source environment reader. A later frame pulls that reader back through the
actual original occurrence; no future environment table enters the atom. -/

set_option autoImplicit false
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Request.Continuation

open SourceOperationEffects RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

structure Frame where
  N : WorldRelationNetwork.{u}
  V : Vocabulary.{u}
  old : RootInquiryStateAt N V
  program : Program old.root.toAuthoritativeRoot.toLedgerRoot
  registered : RegisteredAt (Value := Value) (Var := Var) (sort := sort)
    old.root.toAuthoritativeRoot.toLedgerRoot old.visit.current
  scope : IdentityScope program
  environment : {current : V.Current} →
    old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current → Env Value Var
  depth : Nat

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def currentState := mathState frame.old frame.program frame.registered frame.scope frame.depth
def currentPresentation := mathPresentation frame.old frame.program frame.registered frame.scope frame.depth
def event := (mathCurrent frame.old frame.program frame.registered frame.scope frame.depth).2
def action := mathAction frame.event

abbrev Action := SourceOperationExecutionDebt.Settlement frame.event.state ⊕
  DebtActivationWorld.GeneratedStepAt (law frame.registered) frame.event.state

def environmentAt
    (source : Residual.Occurrence frame.old frame.program frame.registered frame.scope frame.depth) :=
  frame.environment (Native.originalOccurrence frame.program frame.registered source)

def activeEnvironment := frame.environmentAt
  (frame.currentState.root.emitted frame.currentState.visit.current)

def request := Residual.nextRegistered frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt

def born : Frame (Value := Value) (Var := Var) (sort := sort) where
  N := NewN frame.old frame.registered
  V := NewV frame.old frame.program frame.registered
  old := frame.currentState
  program := nextProgram frame.old frame.program frame.registered frame.scope
  registered := frame.request
  scope := nextScope frame.old frame.program frame.registered frame.scope
  environment := fun {_current} source => frame.environment (Native.originalOccurrence frame.program frame.registered source)
  depth := 0

def mathNext : Frame (Value := Value) (Var := Var) (sort := sort) := { frame with depth := frame.depth + 1 }

def nextFrom (selected : frame.Action) : Frame (Value := Value) (Var := Var) (sort := sort) :=
  match selected with
  | .inl _ => frame.born
  | .inr _ => frame.mathNext

def next : Frame (Value := Value) (Var := Var) (sort := sort) := frame.nextFrom frame.action

/-- An actual birth preserves the same old native update as an ordinary
step; admitting the residual does not advance the original source twice. -/
theorem next_environment : frame.next.activeEnvironment = frame.mathNext.activeEnvironment := by
  unfold next nextFrom
  cases frame.action <;> rfl

def birthPresentation := Request.birthPresentation
  frame.currentState (nextProgram frame.old frame.program frame.registered frame.scope)
  (Residual.inputs frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt)
  (nextScope frame.old frame.program frame.registered frame.scope)
  (Residual.owners frame.old frame.program frame.registered frame.scope frame.depth frame.environmentAt)

/-- The actual source action determines the unique compiler at this current.
Birth and ordinary inquiry are never simultaneous registry entries. -/
def presentationFrom (selected : frame.Action) : RootInquiryStatePresentation.{u} :=
  match selected with
  | .inl _ => frame.birthPresentation
  | .inr _ => frame.currentPresentation

def presentation := frame.presentationFrom frame.action

theorem presentation_erase : frame.presentation.erase = frame.currentPresentation.erase := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

theorem presentation_query : frame.presentation.Query = PUnit := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

theorem presentation_root : HEq frame.presentation.state.base.root frame.currentState.root := by
  unfold presentation presentationFrom
  cases frame.action <;> rfl

def query : frame.presentation.Query := Eq.mpr frame.presentation_query PUnit.unit

theorem query_unique (candidate : frame.presentation.Query) : candidate = frame.query := by
  let : Subsingleton frame.presentation.Query :=
    Eq.mpr (congrArg (fun query : Type u => Subsingleton query) frame.presentation_query)
      (inferInstance : Subsingleton PUnit)
  exact Subsingleton.elim candidate frame.query

end Frame

def frames (initial : Frame (Value := Value) (Var := Var) (sort := sort)) : Nat → Frame (Value := Value) (Var := Var) (sort := sort)
  | 0 => initial
  | count + 1 => (frames initial count).next

end
end RootGeneratedDebtActivationJointSource.Native.Request.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
