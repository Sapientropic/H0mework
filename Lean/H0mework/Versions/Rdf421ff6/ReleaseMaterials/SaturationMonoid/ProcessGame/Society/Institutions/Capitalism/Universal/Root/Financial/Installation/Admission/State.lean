import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Registration

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

inductive EventAt : frame.V.Current → Type
  | pending : EventAt origin
  | registered {current : frame.V.Current}
      (native : Nonempty ((process input).Run (registered.admitted input frame).current
        (frame.cursor current).account.current)) : EventAt current

def state {current : frame.V.Current} : EventAt input frame registered current → (registered.law input frame).DebtState
  | .pending => .pending
  | .registered native => .registered (frame.cursor current).account native

def nextEvent {current : frame.V.Current} (event : EventAt input frame registered current) :
    EventAt input frame registered (frame.V.nativeTarget (frame.program.emit current).write) := by
  cases event with
  | pending =>
      apply EventAt.registered
      rw [registered.actual_base_next_account input frame]
      exact ⟨.nil⟩
  | registered prior =>
      exact .registered (prior.map (fun run =>
        run.concatRuns (process input) (Registration.native input frame current)))

def actionTarget {current : frame.V.Current} :
    EventAt input frame registered current → (registered.law input frame).DebtState
  | .pending => (registered.firstStep input frame).target
  | .registered prior =>
      .registered ((Cursor.action input (frame.cursor current)).next input (frame.cursor current).account)
        ((Cursor.action input (frame.cursor current)).append_original_run input (frame.cursor current).account prior)

def actionReceipt {current : frame.V.Current} (event : EventAt input frame registered current) :
    (registered.law input frame).StepAt (state input frame registered event) (actionTarget input frame registered event) ⊕
      (registered.law input frame).TransportAt (state input frame registered event) (actionTarget input frame registered event) := by
  cases event with
  | pending => exact .inl (registered.firstStep input frame).step
  | registered prior =>
      exact .inr ((Cursor.action input (frame.cursor current)).priorDebtTransport input
        (registered.before input frame) registered.claim (frame.cursor current).account prior)

theorem next_state {current : frame.V.Current} (event : EventAt input frame registered current) :
    state input frame registered (nextEvent input frame registered event) = actionTarget input frame registered event := by
  cases event with
  | pending =>
      apply Registration.registered_state_eq
      exact registered.actual_base_next_account input frame
  | registered prior =>
      apply Registration.registered_state_eq
      exact congrArg Cursor.State.account (frame.next_exact current)

abbrev Current := Sigma (EventAt input frame registered)

def initial : Current input frame registered := ⟨origin, .pending⟩

def next (current : Current input frame registered) : Current input frame registered :=
  ⟨frame.V.nativeTarget (frame.program.emit current.1).write, nextEvent input frame registered current.2⟩

abbrev N := ExtendedNetwork frame.N (registered.law input frame)

def supportAt (current : Current input frame registered) : (N input frame registered).Support :=
  ⟨frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.root.emitted current.1), some (state input frame registered current.2)⟩

theorem first_root_state_is_actual_admission :
    state input frame registered (next input frame registered (initial input frame registered)).2 =
      (registered.firstStep input frame).target :=
  next_state input frame registered .pending

theorem first_account_is_not_a_replayed_body :
    (frame.cursor (next input frame registered (initial input frame registered)).1).account =
      registered.admitted input frame :=
  registered.actual_base_next_account input frame

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
