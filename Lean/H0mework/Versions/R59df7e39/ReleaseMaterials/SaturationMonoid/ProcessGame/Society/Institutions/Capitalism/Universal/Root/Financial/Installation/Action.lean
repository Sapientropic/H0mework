import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Activation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive Action
  | issue (claim : IssuedClaim input)
  | movement (origin : InstructionOrigin input) (source : Movement input origin)
  | retain

namespace Action

def next (before : (process input).GeneratedState) : Action input → (process input).GeneratedState
  | .issue claim => admit input before claim
  | .movement origin source =>
      (allocate input origin before source.quantity (source.quantity_nonnegative input)).after
  | .retain => before

def native (before : (process input).GeneratedState) (action : Action input) :
    (process input).Run before.current (action.next input before).current := by
  cases action with
  | issue claim => exact .step .nil (.admit (P := process input) claim)
  | movement origin source =>
      exact (allocate input origin before source.quantity (source.quantity_nonnegative input)).transition
  | retain => exact .nil

theorem append_original_run {current : ResponsibilityState (vocabulary input)}
    (before : (process input).GeneratedState)
    (prior : Nonempty ((process input).Run current before.current)) (action : Action input) :
    Nonempty ((process input).Run current (action.next input before).current) :=
  prior.map (fun run => run.concatRuns (process input) (action.native input before))

def priorDebtTransport (admittedBefore : (process input).GeneratedState) (claim : IssuedClaim input)
    (before : (process input).GeneratedState)
    (prior : Nonempty ((process input).Run (admit input admittedBefore claim).current before.current))
    (action : Action input) :
    (Activation.law input admittedBefore claim).TransportAt
      (.registered before prior)
      (.registered (action.next input before) (action.append_original_run input before prior)) := by
  cases action with
  | issue newClaim => exact .anotherAdmission before prior newClaim
  | movement origin source => exact .movement before prior origin source
  | retain => exact .unchanged _

end Action

def sourceAction (origin : InstructionOrigin input) : Action input :=
  match readIssue input origin with
  | .issued claim _ => .issue claim
  | .nonfinancial =>
      match readMovement input origin with
      | some source => .movement origin source
      | none => .retain
  | .rejected .. | .missingBirth .. => .retain

theorem sourceAction_is_actual_consumer (origin : InstructionOrigin input)
    (before : (process input).GeneratedState) :
    (sourceAction input origin).next input before = (consume input origin before).next input := by
  unfold sourceAction consume
  cases readIssue input origin with
  | issued _ _ => rfl
  | rejected _ _ _ => rfl
  | missingBirth _ _ => rfl
  | nonfinancial => cases readMovement input origin <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation
