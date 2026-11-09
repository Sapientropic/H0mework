import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.GuardedHistory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution
open Reparation.Actual (advance run publishAfter originalLosses)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Script" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {past : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}

/-- Pre-admission consumes only emitted inputs at the same original root. -/
def publishGuardedTick (prior : Reparation.Actual.State seed community past) (input : Input) :=
  let decision := dispatchAdmission (endAt seed past) input
  (decision, publishAfter prior decision.selected)

def publishGuardedHistory (prior : Reparation.Actual.State seed community past) (attempts : Script) :=
  publishAfter prior (guardedHistory (endAt seed past) attempts)

/-- An already submitted input is written exactly once, including any work
selected by a nonrecourse review. The admission verdict reports its authority
without replacing the physically executed history. -/
def auditOriginalTick (prior : Reparation.Actual.State seed community past) (input : Input) :=
  (inspectAdmission (endAt seed past) input, publishAfter prior [input])

theorem a_written_refusal_cannot_become_admitted_by_continuation {cut : C} {input : Input}
    (issue : Violation cut input) (future : Script) :
    ¬ AdmittedHistory cut (input :: future) :=
  fun admitted => issue.refutes (AdmittedHistory.restrict (past := [input]) (suffix := future) admitted).1

theorem the_refused_original_tick_keeps_its_real_write_and_losses
    (seed : C) (community : Party → Community) (past : Script) (input : Input)
    (issue : Violation (endAt seed past) input) :
    let written := auditOriginalTick (run seed community past) input
    (∃ refusal, written.1 = .refused refusal) ∧
    Quantities.Recorded seed (past ++ [input]) ∧
    written.2.next = advance (run seed community past) input ∧
    (∀ origin ∈ originalLosses seed community (past ++ [input]),
      ∃ balance, ∃ row, written.2.next.read row = .inr (origin, balance)) ∧
    ∀ future : Script, ¬ AdmittedHistory (endAt seed past) (input :: future) := by
  refine ⟨?_, (publishAfter (run seed community past) [input]).recorded, ?_,
    every_loss_is_readable_on_the_same_publication seed community past [input],
    a_written_refusal_cannot_become_admitted_by_continuation issue⟩
  · change ∃ refusal, inspectAdmission (endAt seed past) input = .refused refusal
    cases inspected : inspectAdmission (endAt seed past) input with
    | approved allowed => exact (issue.refutes allowed).elim
    | refused retained => exact ⟨retained, rfl⟩
  · change (publishAfter (run seed community past) [input]).next = _
    rw [Reparation.Actual.publication_consumes_the_retained_visit]
    exact Reparation.Actual.run_snoc seed community past input

variable [DecidableEq Technology] {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

theorem no_single_actor_can_restore_on_the_guarded_original_successor
    (seed : C) (community : Party → Community) (past attempts : Script)
    (installed : Emergency.Installed (endAt seed past) base scope)
    (released : Civil.Mandate.Released (endAt seed past).raw) :
    let cut := endAt seed past
    let suffix := guardedHistory cut attempts
    let written := publishGuardedHistory (run seed community past) attempts
    Quantities.Recorded seed (past ++ suffix) ∧
    (∀ origin ∈ originalLosses seed community (past ++ suffix),
      ∃ balance, ∃ row, written.next.read row = .inr (origin, balance)) ∧
    ∀ actor : Party, (∀ item ∈ inventory cut suffix, item.request.signer = actor) →
      (endAt seed (past ++ suffix)).raw.technology.holder = none := by
  let cut := endAt seed past
  let suffix := guardedHistory cut attempts
  refine ⟨(publishGuardedHistory (run seed community past) attempts).recorded,
    every_loss_is_readable_on_the_same_publication seed community past suffix, ?_⟩
  intro actor alone
  rw [endAt_append]
  exact one_signer_cannot_restore_after_any_admitted_history cut suffix installed released
    (every_guarded_history_has_source_authority cut attempts) actor alone

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal
