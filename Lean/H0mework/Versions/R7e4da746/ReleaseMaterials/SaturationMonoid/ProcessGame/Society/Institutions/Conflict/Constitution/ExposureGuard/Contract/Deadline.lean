import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Independent
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.DueWindow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Civil.Persistence (Window)
open Quantities.Execution (endAt endAt_append)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (anchor history : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

/-- The original window is carried through the anchor, including its
already posted payments and its unchanged deadline. -/
def PaidAt : Prop :=
  Due.Checked (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length)

omit [DecidableEq Community] in
theorem at_the_anchor_the_original_window_is_retained : PaidAt seed anchor anchor := by
  unfold PaidAt
  rw [List.drop_length]
  trivial

omit [DecidableEq Community] in
theorem actual_window (original : anchor.IsPrefix history) :
    (((Window.at seed).run anchor).run (history.drop anchor.length)).current = endAt seed history := by
  obtain ⟨suffix, rfl⟩ := original
  rw [← Window.run_append, List.drop_left, Window.run_current]
  rfl

def DueFailure :=
  Due.FirstFailure (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length)

omit [DecidableEq Community] in
theorem an_unpaid_continuation_has_the_first_actual_failure (unpaid : ¬ PaidAt seed anchor history) :
    Nonempty (DueFailure seed anchor history) := by
  cases Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length) with
  | inl failed => exact ⟨failed⟩
  | inr paid => exact (unpaid paid.down).elim

variable (community : Party → Community) [DecidableEq Technology]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (control : RawCurrent Party Good (State Party Technology) Instrument → List Party)

def LiveCertificate (word : Word) : Prop :=
  Certificate base scope seed community anchor history control word ∧
    PaidAt seed anchor (history ++ word)

def LiveAvailable : Prop := ∃ word : Word, LiveCertificate seed anchor history community base scope control word

def ReadyAt : Prop :=
  PaidAt seed anchor history ∧ LiveAvailable seed anchor history community base scope control

inductive LiveFailure (word : Word)
  | exit (failed : Failure base scope seed community anchor history control word)
  | due (failed : DueFailure seed anchor (history ++ word))

def inspectLive (word : Word) :
    LiveFailure seed anchor history community base scope control word ⊕
      PLift (LiveCertificate seed anchor history community base scope control word) :=
  match inspect base scope seed community anchor history control word with
  | .inl failure => .inl (.exit failure)
  | .inr paid =>
    match Due.inspect (endAt seed anchor) ((Window.at seed).run anchor)
      ((history ++ word).drop anchor.length) with
    | .inl failure => .inl (.due failure)
    | .inr continuation => .inr ⟨paid.down, continuation.down⟩

theorem LiveFailure.refutes {word : Word} (failure : LiveFailure seed anchor history community base scope control word) :
    ¬ LiveCertificate seed anchor history community base scope control word := by
  intro live
  cases failure with
  | exit noExit => exact noExit.refutes _ _ _ _ _ _ _ _ live.1
  | due late => exact late.refutes _ live.2

theorem no_live_exit_iff_each_candidate_has_its_original_failure :
    ¬ LiveAvailable seed anchor history community base scope control ↔
      ∀ word : Word, ∃ failure, inspectLive seed anchor history community base scope control word = .inl failure := by
  constructor
  · intro lost word
    cases inspectLive seed anchor history community base scope control word with
    | inl failure => exact ⟨failure, rfl⟩
    | inr proof => exact (lost ⟨word, proof.down⟩).elim
  · rintro failures ⟨word, proof⟩
    obtain ⟨failure, _⟩ := failures word
    exact failure.refutes _ _ _ _ _ _ _ proof

inductive PlanFailure (word : Word)
  | spent (failed : DueFailure seed anchor history)
  | nominated (failed : LiveFailure seed anchor history community base scope control word)

def inspectPlan (word : Word) :
    PlanFailure seed anchor history community base scope control word ⊕
      PLift (ReadyAt seed anchor history community base scope control) :=
  match Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length) with
  | .inl problem => .inl (.spent problem)
  | .inr pastPaid =>
    match inspectLive seed anchor history community base scope control word with
    | .inl problem => .inl (.nominated problem)
    | .inr exits => .inr ⟨pastPaid.down, word, exits.down⟩

def finiteProbe (word : Word) : Option (PLift (ReadyAt seed anchor history community base scope control)) :=
  match inspectPlan seed anchor history community base scope control word with
  | .inl _ => none
  | .inr checked => some checked

theorem a_failed_plan_returns_the_exact_original_issue (word : Word)
    (failed : finiteProbe seed anchor history community base scope control word = none) :
    ∃ issue, inspectPlan seed anchor history community base scope control word = .inl issue := by
  unfold finiteProbe at failed
  cases inspected : inspectPlan seed anchor history community base scope control word with
  | inl issue => exact ⟨issue, rfl⟩
  | inr paid =>
    rw [inspected] at failed
    cases failed

theorem a_paid_nominated_word_supplies_the_checked_continuation (word : Word)
    (pastPaid : PaidAt seed anchor history) (actual : LiveCertificate seed anchor history community base scope control word) :
    ∃ checked, finiteProbe seed anchor history community base scope control word = some checked := by
  unfold finiteProbe inspectPlan
  cases Due.inspect (endAt seed anchor) ((Window.at seed).run anchor) (history.drop anchor.length) with
  | inl failed => exact (failed.refutes _ pastPaid).elim
  | inr paid =>
    cases inspectLive seed anchor history community base scope control word with
    | inl failed => exact (failed.refutes _ _ _ _ _ _ _ actual).elim
    | inr checked => exact ⟨_, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit
