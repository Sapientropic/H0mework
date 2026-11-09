import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Publication
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Opening

open Capitalism.Universal.Source.Program Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate
open PublicFunction PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {first second : Party} {unit : Good}
  {initial : RawCurrent Party Good (State Party Technology) Instrument}
  {original : RawEvent Party Good Port (State Party Technology) Instrument}
  {service : List (RawEvent Party Good Port (State Party Technology) Instrument)}
  (opening : Opening base scope first second unit initial original service)
  (actions : RawCurrent Party Good (State Party Technology) Instrument →
    List (Request Party Good Port (State Party Technology) Instrument))
  (budget : Nat)
  (positive : ∀ slot ∈ scope.task.slots, ∃ item ∈ slot.goods, 0 < item.2)

/-- Read the first authorization from the same signed original
execution used by the installed calendar and the successor. -/
def originalGrants :=
  let bound := opening.source actions budget positive
  let current := OutstandingSource.History.currentAt bound.source opening.inputs 1
  let word := (OutstandingSource.History.actualExecution bound.source opening.inputs 0).submitted
  (grantsAt base opening.installedScope current word).map (admitGrant base opening.installedScope current word)

theorem original_grant_is_signed_by_its_candidate
    (grant : AdmittedGrant base opening.installedScope
      (OutstandingSource.History.currentAt (opening.source actions budget positive).source opening.inputs 1)
      (OutstandingSource.History.actualExecution (opening.source actions budget positive).source opening.inputs 0).submitted) :
    grant.grant.acceptance.item.val.request.signer = grant.grant.candidate ∧
      grant.grant.acceptance.item.val.before.clock ≤ opening.term.band.lower := by
  have allowed := grant.grant.acceptance.authorization.2.2.2.2.2
  rw [grant.grant.accepted_kind] at allowed
  exact ⟨grant.grant.candidate_actually_signed, allowed.2⟩

theorem original_grant_uses_the_physical_issue_clock
    (grant : AdmittedGrant base opening.installedScope
      (OutstandingSource.History.currentAt (opening.source actions budget positive).source opening.inputs 1)
      (OutstandingSource.History.actualExecution (opening.source actions budget positive).source opening.inputs 0).submitted) :
    grant.grant.acceptance.item.val.before.clock = initial.clock + max 0 (base.duration (eraseCurrent initial)) := by
  let native := (opening.source actions budget positive).source
  have atVisit := original_item_clock base opening.installedScope _ _ 0
    grant.grant.acceptance.item.val grant.grant.acceptance.item.property
  rw [atVisit]
  change (OutstandingSource.History.currentAt native opening.inputs 1).clock = _
  rw [(OutstandingSource.History.actual_frame native opening.inputs 1).1]
  rfl

theorem the_two_original_review_positions_charge_their_own_material :
    ((opening.actual actions budget positive).interpreted.items.map fun item =>
      (law base opening.installedScope).actualDebit item.before item.request) =
      [locate first scope.revisionCost, locate second scope.revisionCost] := by
  let target := opening.term.cell.target
  let active := law base opening.installedScope
  let firstRequest := request opening.installedScope target first .review
  let middle := active.step target firstRequest
  let secondRequest := request opening.installedScope middle second .review
  have positions := opening.actual_reviews_are_the_registered_paid_word actions budget positive
  rw [(opening.actual actions budget positive).interpreted_exact, positions.1, positions.2]
  change [active.actualDebit target firstRequest, active.actualDebit middle secondRequest] = _
  rw [reviewer_debit base opening.installedScope target first opening.term.ready.firstPaid,
    reviewer_debit base opening.installedScope middle second opening.term.ready.secondPaid]
  rfl

theorem the_original_financial_rows_reach_the_generated_successor :
    let input := opening.input actions budget positive
    (Financial.accountAt input (service.length + 2)).current.history <+:
      (Financial.accountAt input (service.length + 3)).current.history :=
  Financial.whole_native_history_is_retained (opening.input actions budget positive) (service.length + 2)

/-- The first paid release fixes the native absolute cutoff for every
continued original submission, irrespective of its proposed authority. -/
theorem no_original_suffix_reopens_the_installed_horizon
    (suffix : List Word) (ordinal : Nat) (later : service.length + 2 ≤ ordinal) :
    let bound := opening.source actions budget positive
    let inputs := opening.inputs ++ suffix
    opening.installedScope.task.deadline < clockAt bound inputs ordinal ∧
      ∀ word : Word, ∀ command : ActualCommand base opening.installedScope
          (OutstandingSource.History.currentAt bound.source inputs ordinal) word,
        command.command ≠ .accept ∧ command.command ≠ .renew ∧ ∀ candidate, command.command ≠ .propose candidate := by
  dsimp only
  let bound := opening.source actions budget positive
  let appointment := service.length + 2
  have original :
      OutstandingSource.History.currentAt bound.source (opening.inputs ++ suffix) appointment =
        opening.term.cell.target := by
    have word := opening.actual_reviews_are_the_registered_paid_word actions budget positive
    have stable := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
      bound.source opening.inputs suffix appointment (by simp [appointment, inputs])
    rw [(OutstandingSource.History.actual_frame bound.source _ appointment).1, stable,
      ← (OutstandingSource.History.actual_frame bound.source _ appointment).1]
    exact word.1
  have ready : opening.installedScope.task.deadline < opening.term.cell.target.clock :=
    ((term_band_exact scope.task opening.term.cell opening.term.assigned _).mp
      opening.term.at_least_owns_its_review.2).2.1
  have first : opening.installedScope.task.deadline < clockAt bound (opening.inputs ++ suffix) appointment := by
    change _ < (OutstandingSource.History.currentAt bound.source (opening.inputs ++ suffix) appointment).clock
    rw [original]
    exact ready
  have expired := first.trans_le (real_clock_is_monotone bound (opening.inputs ++ suffix) later)
  exact ⟨expired, fun word command =>
    the_expired_original_root_cannot_propose_accept_or_renew bound (opening.inputs ++ suffix) ordinal
      expired word command⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation.Opening
