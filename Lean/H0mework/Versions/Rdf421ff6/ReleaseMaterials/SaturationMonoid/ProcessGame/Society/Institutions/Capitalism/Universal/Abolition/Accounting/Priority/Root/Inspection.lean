import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root.Finite

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)

local notation "Frame" => Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim
local notation "Word" => RawEvent Party Good Port Technology Instrument

/-- The stopping point retains the exact submitted input and every preceding
actual admission. Its next is the same root action, including any real prefix. -/
structure StoppedAt (frame : Frame) (inputs : List Word) : Type where
  priorInputs : List Word
  proposal : Word
  suffix : List Word
  original : inputs = priorInputs ++ proposal :: suffix
  priorAdmitted : AllAdmitted claim frame priorInputs
  declined : ¬ Admitted claim (afterInputs claim frame priorInputs) proposal

namespace StoppedAt
variable {claim : Responsibility.Family.Claim mechanism past nature response}
  {frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim}
  {inputs : List (RawEvent Party Good Port Technology Instrument)} (stop : StoppedAt claim frame inputs)

def current : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim :=
  afterInputs claim frame stop.priorInputs

def verdict : type_of% (Gate.readRenewal claim (StoppedAt.current stop) stop.proposal) :=
  Gate.readRenewal claim (StoppedAt.current stop) stop.proposal

def next : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) claim :=
  Installation.successor claim stop.current stop.proposal

theorem the_stopped_actual_input_keeps_its_whole_ledger_and_generated_next :
    SourcePriorityAt claim stop.current stop.proposal :=
  the_original_row_executes_its_source_generated_priority_gate claim stop.current stop.proposal

theorem priorInputs_bounded : stop.priorInputs.length ≤
    Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) := by
  have bounded := the_original_current_bounds_every_actual_admitted_sequence claim frame
    stop.priorInputs stop.priorAdmitted
  omega

theorem verdict_exhaustion :
    (∃ paid needs declared noStop, stop.verdict = .settled paid needs declared noStop) ∨
      (∃ issue, stop.verdict = .gate issue) ∨
      (∃ issue, stop.verdict = .needs issue) ∨
      (∃ issue noProgress, stop.verdict = .residual issue noProgress) := by
  cases outcome : stop.verdict with
  | admitted permit =>
      apply False.elim
      apply stop.declined
      unfold Admitted
      dsimp only [verdict,current] at outcome
      rw [outcome]
      trivial
  | settled paid needs declared noStop => exact .inl ⟨paid,needs,declared,noStop,rfl⟩
  | gate issue => exact .inr (.inl ⟨issue,rfl⟩)
  | needs issue => exact .inr (.inr (.inl ⟨issue,rfl⟩))
  | residual issue noProgress => exact .inr (.inr (.inr ⟨issue,noProgress,rfl⟩))

end StoppedAt

inductive Inspection (frame : Frame) (inputs : List Word) : Type
  | admitted (whole : AllAdmitted claim frame inputs)
  | stopped (issue : StoppedAt claim frame inputs)

def inspectInputs (frame : Frame) : (inputs : List Word) → Inspection claim frame inputs
  | [] => .admitted trivial
  | proposal :: rest =>
      if admitted : Admitted claim frame proposal then
        match inspectInputs (Installation.successor claim frame proposal) rest with
        | .admitted whole => .admitted ⟨admitted,whole⟩
        | .stopped issue => .stopped {
            priorInputs := proposal :: issue.priorInputs
            proposal := issue.proposal
            suffix := issue.suffix
            original := congrArg (List.cons proposal) issue.original
            priorAdmitted := ⟨admitted,issue.priorAdmitted⟩
            declined := issue.declined }
      else .stopped ⟨[],proposal,rest,rfl,trivial,admitted⟩

/-- The bound is generated from the current finite unpaid matrix. Inspection
constructs its first settled or typed refusal occurrence; it accepts no future
successful state, schedule of answers, or externally chosen budget. -/
def finiteStop (frame : Frame) (inputs : List Word)
    (longer : Progress.budget claim (Abolition.Accounting.Root.Reentry.Frame.state claim frame) < inputs.length) :
    StoppedAt claim frame inputs :=
  match inspectInputs claim frame inputs with
  | .stopped issue => issue
  | .admitted whole => False.elim
      (a_longer_actual_input_sequence_must_settle_or_return_a_typed_blocker claim frame inputs longer whole)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Root
