import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Dispatch
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Ledger

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)

private theorem step_writes_the_original_singleton (input : Input)
    (paid : MandateExit.PaidAt seed anchor (prior.history ++ [input]))
    (selected : (prior.verdict answers grantRule (paidProbe seed anchor) input).emitted = [input]) :
    prior.step answers grantRule (paidProbe seed anchor) input = advancePaid prior answers [input] paid := by
  apply same_paid_visit
  · exact congrArg (prior.history ++ ·) selected
  · change HEq
      (Receipts.writeAfter answers prior.state (prior.verdict answers grantRule (paidProbe seed anchor) input).emitted)
      (Receipts.writeAfter answers prior.state [input])
    rw [selected]

private theorem singleton_write_at_equal_visit (other : PaidVisit seed community anchor)
    (same : prior = other) (input : Input)
    (paid : MandateExit.PaidAt seed anchor (prior.history ++ [input]))
    (later : MandateExit.PaidAt seed anchor (other.history ++ [input])) :
    advancePaid prior answers [input] paid = advancePaid other answers [input] later := by
  subst other
  rfl

private theorem write_equal_suffix (first second : Word) (same : first = second)
    (left : MandateExit.PaidAt seed anchor (prior.history ++ first))
    (right : MandateExit.PaidAt seed anchor (prior.history ++ second)) :
    advancePaid prior answers first left = advancePaid prior answers second right := by
  subst second
  rfl

variable (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (rival : Scheduler Party Good Port (State Party Technology) Instrument) (person : Party)

local notation "run" =>
  Scheduler.run (reserve rival word) answers person grantRule (fun _ _ => paidProbe seed anchor) prior

private theorem prefix_due (approved : Certified prior answers word) (tick : Nat) :
    MandateExit.PaidAt seed anchor (prior.history ++ word.take tick) :=
  every_committed_prefix_keeps_the_original_due_window seed anchor prior.history word prior.original
    approved.due (word.take tick) (List.take_prefix _ _)

theorem every_reserved_prefix_has_its_exact_original_whole_account
    (approved : Certified prior answers word) (tick : Nat) (within : tick ≤ word.length) :
    run tick = advancePaid prior answers (word.take tick) (prefix_due prior answers word approved tick) := by
  induction tick with
  | zero => exact (advance_paid_empty answers prior _).symm
  | succ tick priorEq =>
    have inside : tick < word.length := within
    let current := run tick
    let scheduled := reserve rival word
    have original : current.history = prior.history ++ word.take tick :=
      the_original_dispatch_writes_each_reserved_prefix prior answers word rival person approved tick inside.le
    have selected := the_reserved_visit_is_forwarded_at_its_original_history prior answers word rival person
      approved tick inside original
    have reply := reserve_reads_the_original_owner_lanes rival answers person tick current.history inside
    have proposed := reserve_reads_the_literal_input rival tick current.history inside
    have exactChoice : (current.verdict answers grantRule (paidProbe seed anchor) word[tick]).emitted = [word[tick]] := by
      change (current.verdict (scheduled.replies answers person tick current.history) grantRule
        (paidProbe seed anchor) (scheduled.proposal tick current.history)).emitted = _ at selected
      rwa [reply, proposed] at selected
    have due := prefix_due prior answers word approved (tick + 1)
    rw [List.take_succ_eq_append_getElem inside, ← List.append_assoc] at due
    have paidCurrent : MandateExit.PaidAt seed anchor (current.history ++ [word[tick]]) := by
      rwa [original]
    have next : run (tick + 1) = advancePaid current answers [word[tick]] paidCurrent := by
      change current.step (scheduled.replies answers person tick current.history) grantRule
        (paidProbe seed anchor) (scheduled.proposal tick current.history) = _
      rw [reply, proposed]
      exact step_writes_the_original_singleton current answers _ paidCurrent exactChoice
    have retained := priorEq inside.le
    let front := advancePaid prior answers (word.take tick) (prefix_due prior answers word approved tick)
    rw [next, singleton_write_at_equal_visit current answers front retained _ paidCurrent due,
      advance_paid_snoc answers prior _ _ _ due (by rwa [← List.append_assoc])]
    exact write_equal_suffix prior answers _ _ (List.take_succ_eq_append_getElem inside).symm _ _

theorem the_priority_endpoint_is_the_same_original_write (approved : Certified prior answers word) :
    visitAt prior answers word rival person approved word.length = advancePaid prior answers word approved.due := by
  unfold visitAt
  rw [Nat.min_self, every_reserved_prefix_has_its_exact_original_whole_account prior answers word rival person
    approved word.length le_rfl]
  exact write_equal_suffix prior answers _ _ List.take_length _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
