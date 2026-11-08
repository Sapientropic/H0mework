import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.PaidService
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Handoff

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Install

open Source.Program Institutions.Capitalism.Universal.Root PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

variable {epoch : Epoch}

abbrev Words := List (List Action)

noncomputable def submitAll (inventory : Inventory epoch) (words : Words) : Inventory epoch :=
  words.foldl World.submit inventory

theorem submit_all_inputs (inventory : Inventory epoch) (words : Words) :
    (submitAll inventory words).inputs = inventory.inputs ++ words := by
  induction words generalizing inventory with
  | nil => simp [submitAll]
  | cons word tail ih =>
    change (submitAll (World.submit inventory word) tail).inputs = _
    rw [ih]
    change (inventory.inputs ++ [word]) ++ tail = _
    exact List.append_assoc _ _ _

noncomputable def submitAllRun (inventory : Inventory epoch) (words : Words) :
    (Financial.Family.process sources).Run inventory.finance.current (submitAll inventory words).finance.current :=
  match words with
  | [] => .nil
  | word :: tail => (World.financialRun inventory word).concatRuns _ (submitAllRun (World.submit inventory word) tail)

def Registered (inventory : Inventory epoch) (cutoff : ℚ) : Prop :=
  ∃ fresh, Handoff.choose epoch.bound inventory.inputs = some fresh ∧ fresh.task.deadline = cutoff

/-- An alternative term must come from the original scope transition.
Each actual paid handoff cut emits a unique clock value. -/
theorem registered_cutoff_is_the_native_successor_clock (inventory : Inventory epoch) (cutoff : ℚ) :
    Registered inventory cutoff ↔
      (Handoff.choose epoch.bound inventory.inputs).isSome = true ∧
        cutoff = (World.current epoch inventory.inputs).clock + 3 := by
  constructor
  · rintro ⟨fresh, chosen, deadline⟩
    exact ⟨by rw [chosen]; rfl, deadline.symm⟩
  · rintro ⟨available, clock⟩
    exact ⟨(Handoff.choose epoch.bound inventory.inputs).get available, Option.some_get available |>.symm, clock.symm⟩

def originalOpening? (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (words : Words) :=
  let actual := OutstandingSource.History.actualExecution (Handoff.source fresh) words 1
  if words.isEmpty then none else Handoff.decodePaidOpening fresh actual.before actual.submitted

def DraftPaid (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (words : Words) : Prop :=
  Payable (Handoff.newBound fresh) [] words fresh.task.deadline ∧
    Term.PaidAt (Handoff.newBound fresh) [] words ∧
    (originalOpening? inventory fresh words).isSome = true ∧
    Handoff.ExitEnvelope (Term.target (Handoff.newBound fresh) [] words) ∧
    Handoff.MaterialHealthy (Handoff.start fresh)

inductive DraftFailure (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (words : Words) where
  | instruction (period : Fin words.length)
      (item : {item // item ∈ (Handoff.law fresh).rawItems
        (actualAt (Handoff.newBound fresh) [] words period).before
        (actualAt (Handoff.newBound fresh) [] words period).submitted})
      (refused : ¬ (Handoff.law fresh).Valid item.val.before item.val.request)
  | settlement (reason : Term.Issue (Handoff.newBound fresh) [] words)
  | opening (absent : originalOpening? inventory fresh words = none)
  | exit (short : ¬ Handoff.ExitEnvelope (Term.target (Handoff.newBound fresh) [] words))
  | stock (bearer : Bool) (good : Financed.Good) (missing : (Handoff.start fresh).stock bearer good < 0)

inductive DraftDecision (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (words : Words) where
  | paid (proof : DraftPaid inventory fresh words)
  | blocked (reason : DraftFailure inventory fresh words)

inductive Failure (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) where
  | review (absent : Handoff.choose epoch.bound inventory.inputs = none)
      (reason : Handoff.Blocked epoch.bound inventory.inputs)
  | differentClock (fresh : Handoff.Ready epoch.bound inventory.inputs)
      (chosen : Handoff.choose epoch.bound inventory.inputs = some fresh)
      (exact : fresh.task.deadline ≠ cutoff)
  | draft (fresh : Handoff.Ready epoch.bound inventory.inputs)
      (chosen : Handoff.choose epoch.bound inventory.inputs = some fresh)
      (reason : DraftFailure inventory fresh words)

structure Accepted (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) where
  fresh : Handoff.Ready epoch.bound inventory.inputs
  chosen : Handoff.choose epoch.bound inventory.inputs = some fresh
  exactCutoff : fresh.task.deadline = cutoff
  paid : DraftPaid inventory fresh words

inductive Decision (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) where
  | accept (checked : Accepted inventory cutoff words)
  | reject (blocked : Failure inventory cutoff words)

def Acceptance (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) : Prop :=
  Nonempty (Accepted inventory cutoff words)

private def stockAddresses : List (Bool × Financed.Good) :=
  [(false, .feedstock), (false, .service), (true, .feedstock), (true, .service)]

private theorem stock_address_is_listed (actor : Bool) (good : Financed.Good) :
    (actor, good) ∈ stockAddresses := by
  cases actor <;> cases good <;> decide

private inductive StockCheck (before : Financed.Current)
  | healthy (all : Handoff.MaterialHealthy before)
  | failed (actor : Bool) (good : Financed.Good) (short : before.stock actor good < 0)

private def inspectStock (before : Financed.Current) : StockCheck before :=
  match Material.inspectList (fun address : Bool × Financed.Good =>
      0 ≤ before.stock address.1 address.2) stockAddresses with
  | .failure address _ short => .failed address.1 address.2 (lt_of_not_ge short)
  | .clear all => .healthy fun actor good => all (actor, good) (stock_address_is_listed actor good)

def checkDraft (inventory : Inventory epoch)
    (fresh : Handoff.Ready epoch.bound inventory.inputs) (words : Words) : DraftDecision inventory fresh words := by
  let bound := Handoff.newBound fresh
  let scheduled := fun ordinal : Fin words.length => actualAt bound [] words ordinal
  let payable := fun ordinal : Fin words.length =>
    PaidItems base fresh.scope (scheduled ordinal).before 0 (scheduled ordinal).submitted
  letI (ordinal : Fin words.length) : Decidable (payable ordinal) :=
    inferInstanceAs (Decidable (PaidItems base fresh.scope
      (scheduled ordinal).before 0 (scheduled ordinal).submitted))
  match Material.inspectList payable (List.finRange words.length) with
  | .failure ordinal _ failed =>
    let actual := scheduled ordinal
    let items := ((Handoff.law fresh).rawItems actual.before actual.submitted).attach
    match Material.inspectList (fun item => (Handoff.law fresh).Valid item.val.before item.val.request) items with
    | .failure item _ refused => exact .blocked (.instruction ordinal item refused)
    | .clear accepted =>
      exact (failed fun item member => accepted ⟨item, member⟩ (List.mem_attach _ _)).elim
  | .clear accepted =>
    have wordsPaid : Payable bound [] words fresh.task.deadline :=
      fun ordinal => accepted ordinal (List.mem_finRange _)
    match scanPaidService bound [] words with
    | .blocked reason => exact .blocked (.settlement reason)
    | .paid settlement =>
      cases opening : originalOpening? inventory fresh words with
      | none => exact .blocked (.opening opening)
      | some real =>
        if exit : Handoff.ExitEnvelope (Term.target bound [] words) then
          match inspectStock (Handoff.start fresh) with
          | .healthy healthy =>
            exact .paid ⟨wordsPaid, settlement, by rw [opening]; rfl, exit, healthy⟩
          | .failed actor good short => exact .blocked (.stock actor good short)
        else exact .blocked (.exit exit)

theorem DraftFailure.refutes {inventory : Inventory epoch}
    {fresh : Handoff.Ready epoch.bound inventory.inputs} {words : Words}
    (failure : DraftFailure inventory fresh words) : ¬ DraftPaid inventory fresh words := by
  intro paid
  cases failure with
  | instruction period item refused => exact refused (paid.1 period item.val item.property)
  | settlement reason => exact reason.refutes paid.2.1
  | opening absent =>
    have opening := paid.2.2.1
    rw [absent] at opening
    cases opening
  | exit short => exact short paid.2.2.2.1
  | stock bearer good missing => exact (not_lt_of_ge (paid.2.2.2.2 bearer good)) missing

/-- Decide an arbitrary submitted draft before granting its authority.
The outgoing review must already be paid in the original history. -/
def inspect (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) :
    Decision inventory cutoff words :=
  match chosen : Handoff.choose epoch.bound inventory.inputs with
  | none => .reject (.review chosen (Handoff.every_failed_handoff_has_an_actual_reason _ _ chosen))
  | some fresh =>
    if same : fresh.task.deadline = cutoff then
      match checkDraft inventory fresh words with
      | .paid evidence => .accept ⟨fresh, chosen, same, evidence⟩
      | .blocked reason => .reject (.draft fresh chosen reason)
    else .reject (.differentClock fresh chosen same)

theorem Failure.rules_out {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (failure : Failure inventory cutoff words) : ¬ Acceptance inventory cutoff words := by
  rintro ⟨accepted⟩
  have chosen := accepted.chosen
  cases failure with
  | review absent _ =>
    rw [absent] at chosen
    cases chosen
  | differentClock fresh listed different =>
    rw [listed] at chosen
    cases Option.some.inj chosen
    exact different accepted.exactCutoff
  | draft fresh listed reason =>
    rw [listed] at chosen
    cases Option.some.inj chosen
    exact reason.refutes accepted.paid

def Decision.isAccepted {inventory : Inventory epoch} {cutoff : ℚ} {words : Words} :
    Decision inventory cutoff words → Bool
  | .accept .. => true
  | .reject .. => false

theorem inspect_exact (inventory : Inventory epoch) (cutoff : ℚ) (words : Words) :
    (inspect inventory cutoff words).isAccepted = true ↔ Acceptance inventory cutoff words := by
  cases inspect inventory cutoff words with
  | accept checked => exact ⟨fun _ => ⟨checked⟩, fun _ => rfl⟩
  | reject blocked => exact ⟨fun check => Bool.noConfusion check, fun accepted => (blocked.rules_out accepted).elim⟩

noncomputable def Accepted.next {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) : World.Packet :=
  ⟨Epoch.ofFresh accepted.fresh, World.handoffAt inventory accepted.fresh words⟩

theorem Accepted.next_uses_its_actual_words {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) : accepted.next.2.inputs = words := rfl

theorem Accepted.opening_is_in_its_native_successor {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) : accepted.next.2.actualOpening?.isSome = true :=
  accepted.paid.2.2.1

noncomputable def Accepted.financialRun {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) :
    (Financial.Family.process sources).Run inventory.finance.current accepted.next.2.finance.current :=
  World.handoffAtFinancialRun inventory accepted.fresh words

theorem Accepted.complete_claim_matrix {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) :
    Financial.Family.ledgerClaims sources accepted.next.2.finance.current =
      (World.current accepted.next.1 accepted.next.2.inputs).claims :=
  accepted.next.2.matrix

theorem Accepted.all_original_cohorts_continue {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) :
    inventory.pastGrants.map GrantCohort.origin <+: accepted.next.2.pastGrants.map GrantCohort.origin ∧
      inventory.pastChallenges.map ChallengeCohort.origin <+: accepted.next.2.pastChallenges.map ChallengeCohort.origin ∧
      inventory.pastServices.map ServiceCohort.origin <+: accepted.next.2.pastServices.map ServiceCohort.origin := by
  obtain ⟨grants, challenges, services⟩ := World.actual_handoff_keeps_all_old_and_current_origins inventory accepted.fresh words
  refine ⟨?_, ?_, ?_⟩
  · change _ <+: (World.handoffAt inventory accepted.fresh words).pastGrants.map GrantCohort.origin
    rw [grants]
    exact List.prefix_append _ _
  · change _ <+: (World.handoffAt inventory accepted.fresh words).pastChallenges.map ChallengeCohort.origin
    rw [challenges]
    exact List.prefix_append _ _
  · change _ <+: (World.handoffAt inventory accepted.fresh words).pastServices.map ServiceCohort.origin
    rw [services]
    exact List.prefix_append _ _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Install
