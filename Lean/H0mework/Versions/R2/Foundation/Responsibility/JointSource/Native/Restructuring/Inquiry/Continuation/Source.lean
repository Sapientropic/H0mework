import H0mework.Versions.R2.Foundation.Responsibility.JointSource.Native.Restructuring.Inquiry.Continuation.Frame

/-! The complete paid state and the actual original environment reader
generate a residual request. Its strict action creates the next general birth. -/

set_option autoImplicit false
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion

noncomputable section
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}

namespace Frame
variable (frame : Frame (Value := Value) (Var := Var) (sort := sort))

def material (source : frame.Occurrence) :
    Native.ResidualRequest.MaterialAt (Value := Value) (Var := Var) (sort := sort) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := frame.rawRead.environment
          increment := frame.activeEnvironment - frame.rawRead.environment
          raw := frame.rawRead.expression
          state := frame.paidRead.state
          owner := frame.currentState.entryAt PUnit.unit }

def reader (source : frame.Occurrence) := Native.ResidualRequest.input (frame.material source)
def request := register frame.reader
def actualMaterial := frame.material (frame.currentState.root.emitted frame.currentState.visit.current)

theorem request_environment : frame.request.input.environment = frame.activeEnvironment := by
  change frame.rawRead.environment + (frame.activeEnvironment - frame.rawRead.environment) = _
  abel

theorem request_owner : frame.request.input.owner = frame.currentState.entryAt PUnit.unit := rfl

theorem request_budget : remaining frame.request.input.expression =
    remaining frame.rawRead.expression + remaining frame.paidRead.state.1 + 2 :=
  Native.ResidualRequest.budget frame.actualMaterial

def born : Frame (Value := Value) (Var := Var) (sort := sort) where
  N := World frame.registered
  V := Native.JointV frame.program frame.registered
  old := frame.currentState
  program := Inquiry.nextProgram frame.old frame.program frame.registered
  registered := frame.request
  environment := fun {_current} source =>
    frame.environment (Native.originalOccurrence frame.program frame.registered source)
  depth := 0

def mathNext : Frame (Value := Value) (Var := Var) (sort := sort) := { frame with depth := frame.depth + 1 }

def nextFrom (selected : frame.Action) : Frame (Value := Value) (Var := Var) (sort := sort) :=
  match selected with
  | .inl _ => frame.born
  | .inr _ => frame.mathNext

def next := frame.nextFrom frame.action

def inputs (_query : frame.currentState.Query) := frame.request

theorem owners (query : frame.currentState.Query) :
    (frame.inputs query).input.owner = frame.currentState.entryAt query := by
  cases query
  rfl

private theorem request_not_settled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent frame.request).state) : False := by
  have zero := (Idle.law frame.request.input.environment frame.request.input.expression).settlement_budget_zero settled
  change remaining frame.request.input.expression = 0 at zero
  have growth := frame.request_budget
  omega

def firstStep : DebtActivationWorld.GeneratedStepAt
    (Idle.law frame.request.input.environment frame.request.input.expression)
    (initialEvent frame.request).state :=
  match Inquiry.sourceAction frame.currentState (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request with
  | .inl settled => False.elim (frame.request_not_settled settled)
  | .inr paid => paid

theorem firstStep_generated :
    Inquiry.sourceAction frame.currentState (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request =
      .inr frame.firstStep := by
  cases selected : Inquiry.sourceAction frame.currentState
      (Inquiry.nextProgram frame.old frame.program frame.registered) frame.request with
  | inl settled => exact False.elim (frame.request_not_settled settled)
  | inr paid => simp only [firstStep, selected]

def birthGenerated := (Inquiry.birthProgramAt frame.currentState
    (Inquiry.nextProgram frame.old frame.program frame.registered) frame.inputs frame.owners
    PUnit.unit frame.firstStep frame.firstStep_generated).generate
  (frame.currentState.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt frame.currentState.visit)

theorem birth_compiles :
    (Inquiry.birthState frame.currentState (Inquiry.nextProgram frame.old frame.program frame.registered)
      frame.inputs frame.owners).compileInquiry PUnit.unit = .debtAdmission frame.birthGenerated :=
  Inquiry.birthState_compiles_paid frame.currentState
    (Inquiry.nextProgram frame.old frame.program frame.registered) frame.inputs frame.owners
    PUnit.unit frame.firstStep rfl frame.firstStep_generated

def birthPresentation : RootInquiryStatePresentation where
  N := World frame.registered
  V := Native.JointV frame.program frame.registered
  state := .create (Inquiry.birthState frame.currentState
    (Inquiry.nextProgram frame.old frame.program frame.registered) frame.inputs frame.owners)

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

end Frame

def frames (initial : Frame (Value := Value) (Var := Var) (sort := sort)) : Nat → Frame (Value := Value) (Var := Var) (sort := sort)
  | 0 => initial
  | count + 1 => (frames initial count).next

end
end RootGeneratedDebtActivationJointSource.Native.Restructuring.Inquiry.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
