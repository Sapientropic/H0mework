import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual.Effect

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

/-- Raw finite code is an input, never a successful plan or a physical
target. Its source occurrence must be supplied by the registered input face. -/
structure Submission (Party Good Port Technology Instrument : Type) where
  requests : RawEvent Party Good Port Technology Instrument

def submissionTarget
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (submission : Submission Party Good Port Technology Instrument) :
    State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  ⟨current.raw, .seeking, submission.requests⟩

inductive SubmissionOutcome
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) : Type
  | received (originalObstruction : ExactObstruction input depth count prefixLimit renewalLimit current)
      (exhausted : decide input depth count prefixLimit renewalLimit current = .blocked originalObstruction)
  | receivedBoundary (word : RawEvent Party Good Port Technology Instrument)
      (phase : current.phase = .renewal word)
      (paid : Review.Guarded.Checks input (origin input depth count) current.raw (members input depth count) word)
      (produced : decide input depth count prefixLimit renewalLimit current = .action (.renewal word phase paid))
  | busy (operation : Operation input depth count prefixLimit renewalLimit current)
      (notBoundary : match operation with | .renewal .. => False | _ => True)
      (original : decide input depth count prefixLimit renewalLimit current = .action operation)

def receive
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) :
    SubmissionOutcome input depth count prefixLimit renewalLimit current :=
  match original : decide input depth count prefixLimit renewalLimit current with
  | .blocked issue => .received issue original
  | .action (.renewal word phase paid) => .receivedBoundary word phase paid original
  | .action (.migration plan selected) => .busy (.migration plan selected) trivial original
  | .action (.repair cause attempt) => .busy (.repair cause attempt) trivial original

def SubmissionOutcome.admissible
    {current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)} :
    SubmissionOutcome input depth count prefixLimit renewalLimit current → Prop
  | .received .. | .receivedBoundary .. => True
  | .busy .. => False

instance
    {current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)}
    (outcome : SubmissionOutcome input depth count prefixLimit renewalLimit current) :
    Decidable (outcome.admissible input depth count prefixLimit renewalLimit) := by
  cases outcome <;> unfold SubmissionOutcome.admissible <;> infer_instance

def receiveTarget
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (submission : Submission Party Good Port Technology Instrument) :=
  match receive input depth count prefixLimit renewalLimit current with
  | .received .. | .receivedBoundary .. => submissionTarget current submission
  | .busy .. => current

theorem received_code_cannot_refill_an_active_attempt
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (submission : Submission Party Good Port Technology Instrument)
    (operation : Operation input depth count prefixLimit renewalLimit current)
    (notBoundary : match operation with | .renewal .. => False | _ => True)
    (active : decide input depth count prefixLimit renewalLimit current = .action operation) :
    receiveTarget input depth count prefixLimit renewalLimit current submission = current := by
  unfold receiveTarget
  cases receive input depth count prefixLimit renewalLimit current with
  | received issue exhausted => cases exhausted.symm.trans active
  | receivedBoundary word phase paid produced =>
      have same := Outcome.action.inj (produced.symm.trans active)
      cases same
      cases notBoundary
  | busy original notBoundary produced => rfl

theorem submitted_code_never_changes_the_physical_current
    (current : State (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (submission : Submission Party Good Port Technology Instrument) :
    (receiveTarget input depth count prefixLimit renewalLimit current submission).raw = current.raw := by
  unfold receiveTarget
  cases receive input depth count prefixLimit renewalLimit current <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Actual
