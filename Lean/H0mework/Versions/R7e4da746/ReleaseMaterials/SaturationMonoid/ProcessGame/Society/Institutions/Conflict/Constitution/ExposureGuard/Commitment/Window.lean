import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Civil.Persistence (Window)
open PublicFunction.Mandate
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "W" => Window Party Good Port M Instrument

abbrev PaidVisit (seed : C) (community : Party → Community) (anchor : Word) :=
  Visit seed community anchor (MandateExit.PaidAt seed anchor)

omit [DecidableEq Community] in
private theorem checked_append (origin : C) (window : W) (front tail : Word) :
    Due.Checked origin window (front ++ tail) ↔
      Due.Checked origin window front ∧ Due.Checked origin (window.run front) tail := by
  induction front generalizing window with
  | nil => simp only [List.nil_append, Due.Checked, Window.run, true_and]
  | cons input rest prior =>
    simp only [List.cons_append, Due.Checked, Window.run, prior, and_assoc]

variable (seed : Root.Cut Party Good Port (State Party Technology) Instrument)
  (anchor past word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

omit [DecidableEq Community] in
theorem every_committed_prefix_keeps_the_original_due_window
    (original : anchor.IsPrefix past) (paid : MandateExit.PaidAt seed anchor (past ++ word))
    (front : Word) (earlier : front.IsPrefix word) : MandateExit.PaidAt seed anchor (past ++ front) := by
  obtain ⟨tail, rfl⟩ := earlier
  have enough : anchor.length ≤ (past ++ front).length := original.length_le.trans (by simp)
  unfold MandateExit.PaidAt at paid ⊢
  rw [← List.append_assoc, List.drop_append_of_le_length enough] at paid
  exact ((checked_append _ _ _ _).mp paid).1

omit [DecidableEq Community] in
theorem every_original_crossing_pays_before_its_unchanged_due_time
    (original : anchor.IsPrefix past) (paid : MandateExit.PaidAt seed anchor (past ++ word))
    (front : Word) (input : Input) (tail : Word) (split : word = front ++ input :: tail) :
    let before := (past ++ front).drop anchor.length
    let window := ((Window.at seed).run anchor).run before
    Due.Step (endAt seed anchor) window input := by
  have enough : anchor.length ≤ (past ++ front).length := original.length_le.trans (by simp)
  unfold MandateExit.PaidAt at paid
  rw [split, ← List.append_assoc, List.drop_append_of_le_length enough] at paid
  exact ((checked_append _ _ _ _).mp paid).2.1

variable {seed anchor} {community : Party → Community}

/-- A committed prefix uses the existing visit and the original receipt
allocator. The remaining word, when any, is a suffix of this same programme. -/
def advancePaid (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
    (suffix : Word) (paid : MandateExit.PaidAt seed anchor (prior.history ++ suffix)) :
    PaidVisit seed community anchor :=
  ⟨prior.history ++ suffix, prior.original.trans (List.prefix_append _ _),
    Receipts.writeAfter answers prior.state suffix,
    Receipts.writeAfter_origins answers prior.history suffix prior.state prior.origins, paid⟩

variable [DecidableEq Technology]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}

def paidView (current : GuardedVisit base scope seed community anchor control) :
    PaidVisit seed community anchor :=
  ⟨current.history, current.original, current.state, current.origins, current.continues.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
