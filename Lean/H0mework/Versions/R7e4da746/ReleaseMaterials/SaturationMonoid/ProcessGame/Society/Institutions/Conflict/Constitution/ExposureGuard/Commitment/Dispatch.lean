import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Plan
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment.Reservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "M" => State Party Technology
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community}
  {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  (prior : PaidVisit seed community anchor) (answers : OwnerAnswers seed)
  (word : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)

theorem the_original_gate_forwards_every_certified_reserved_input
    (approved : Certified prior answers word) (tick : Nat) (inside : tick < word.length) :
    let past := prior.history ++ word.take tick
    let roster := bearers seed community anchor ++ bearers seed community past
    (select roster answers grantRule (MandateExit.PaidAt seed anchor)
      (paidProbe seed anchor) past word[tick]).emitted = [word[tick]] := by
  have next : word.take (tick + 1) = word.take tick ++ [word[tick]] :=
    List.take_succ_eq_append_getElem inside
  have split : word = word.take tick ++ word[tick] :: word.drop (tick + 1) := by
    have original := (List.take_append_drop (tick + 1) word).symm
    rwa [next, List.append_assoc, List.singleton_append] at original
  obtain ⟨admitted, noGrant⟩ :=
    approved.admitted.at_visit (word.take tick) word[tick] (word.drop (tick + 1)) split
  have due := every_committed_prefix_keeps_the_original_due_window seed anchor prior.history word
    prior.original approved.due (word.take (tick + 1)) (List.take_prefix _ _)
  rw [next, ← List.append_assoc] at due
  obtain ⟨verified, checked⟩ := paid_probe_accepts_the_original_paid_prefix seed anchor _ due
  exact the_composed_gate_forwards_an_admitted_continuation _ answers grantRule _ _ _ _
    admitted (fun position => a_non_grant_needs_only_its_original_material_authors _ _ _ _ _ (noGrant position))
    (verified := verified) checked

variable (rival : Scheduler Party Good Port (State Party Technology) Instrument) (person : Party)

local notation "run" =>
  Scheduler.run (reserve rival word) answers person grantRule (fun _ _ => paidProbe seed anchor) prior

theorem the_reserved_visit_is_forwarded_at_its_original_history
    (approved : Certified prior answers word) (tick : Nat) (inside : tick < word.length)
    (original : (run tick).history = prior.history ++ word.take tick) :
    let current := run tick
    let schedule := reserve rival word
    (current.verdict (schedule.replies answers person tick current.history) grantRule
      (paidProbe seed anchor) (schedule.proposal tick current.history)).emitted = [word[tick]] := by
  let current := run tick
  let schedule := reserve rival word
  change (current.verdict (schedule.replies answers person tick current.history) grantRule
    (paidProbe seed anchor) (schedule.proposal tick current.history)).emitted = _
  rw [reserve_reads_the_original_owner_lanes rival answers person tick current.history inside,
    reserve_reads_the_literal_input rival tick current.history inside]
  change (select (bearers seed community anchor ++ bearers seed community current.history)
    answers grantRule (MandateExit.PaidAt seed anchor) (paidProbe seed anchor) current.history word[tick]).emitted = _
  rw [show current.history = prior.history ++ word.take tick from original]
  exact the_original_gate_forwards_every_certified_reserved_input prior answers word approved tick inside

theorem the_original_dispatch_writes_each_reserved_prefix
    (approved : Certified prior answers word) (tick : Nat) (within : tick ≤ word.length) :
    (run tick).history = prior.history ++ word.take tick := by
  induction tick with
  | zero => exact (List.append_nil prior.history).symm
  | succ tick earlier =>
    have inside : tick < word.length := within
    have original := earlier inside.le
    let current := run tick
    let schedule := reserve rival word
    change current.history ++ (current.verdict (schedule.replies answers person tick current.history) grantRule
      (paidProbe seed anchor) (schedule.proposal tick current.history)).emitted = _
    rw [the_reserved_visit_is_forwarded_at_its_original_history prior answers word rival person
      approved tick inside original, original, List.take_succ_eq_append_getElem inside, List.append_assoc]

/-- Run the existing dispatcher through the reserved part. Any following
input starts from this exact successor after the next plan is inspected. -/
def visitAt (_approved : Certified prior answers word) (tick : Nat) :
    PaidVisit seed community anchor :=
  run (min tick word.length)

theorem visitAt_history (approved : Certified prior answers word) (tick : Nat) :
    (visitAt prior answers word rival person approved tick).history = prior.history ++ word.take tick := by
  unfold visitAt
  rw [the_original_dispatch_writes_each_reserved_prefix prior answers word rival person approved _
    (Nat.min_le_right _ _)]
  rcases le_total tick word.length with within | past
  · rw [Nat.min_eq_left within]
  · rw [Nat.min_eq_right past, List.take_length, List.take_of_length_le past]

theorem a_commitment_completes_at_exactly_its_literal_dispatch_count
    (approved : Certified prior answers word) (tick : Nat) :
    (visitAt prior answers word rival person approved tick).history = prior.history ++ word ↔ word.length ≤ tick := by
  rw [visitAt_history]
  constructor
  · intro equal
    have lengths := congrArg List.length equal
    simp only [List.length_append, List.length_take] at lengths
    omega
  · intro complete
    rw [List.take_of_length_le complete]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Commitment
