import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Runtime
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Iteration

/-! Current authority and real failed debits choose the next input. A blocked
trial actually repairs and repays before one fresh check at its new cut. -/
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
universe u
variable {epoch : Epoch} (inventory : Inventory epoch) (intent : Intent)

def retried : Bool := Input.Outcome.fold epoch (Result := Bool)
  (fun _ _ _ => false) (fun _ => false) (fun _ _ _ => true)
  (Input.outcome epoch intent (current epoch inventory.inputs))

def cut := if retried inventory intent then Input.advance inventory intent else inventory
def outcome := Input.outcome epoch intent (current epoch (cut inventory intent).inputs)
def after := Input.advance (cut inventory intent) intent

def financialRun : (Financial.Family.process sources).Run inventory.finance.current (after inventory intent).finance.current := by
  have first : (Financial.Family.process sources).Run inventory.finance.current (cut inventory intent).finance.current := by
    unfold cut
    split
    · exact Input.financialRun inventory intent
    · exact .nil
  exact first.concatRuns _ (Input.financialRun (cut inventory intent) intent)

theorem cut_inputs_extend_the_saved_history : inventory.inputs <+: (cut inventory intent).inputs := by
  unfold cut
  split
  · exact ⟨_, (Input.inputs_exact inventory intent).symm⟩
  · exact ⟨[], by simp⟩

theorem after_inputs_extend_the_trial : (cut inventory intent).inputs <+: (after inventory intent).inputs :=
  ⟨_, (Input.inputs_exact (cut inventory intent) intent).symm⟩

theorem all_past_cohorts_are_consumed :
    (after inventory intent).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ∧
    (after inventory intent).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ∧
    (after inventory intent).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := by
  have first : (cut inventory intent).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ∧
      (cut inventory intent).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ∧
      (cut inventory intent).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := by
    unfold cut
    split
    · exact Input.full_past_cohorts_are_preserved_before_the_next_epoch inventory intent
    · exact ⟨rfl,rfl,rfl⟩
  have second := Input.full_past_cohorts_are_preserved_before_the_next_epoch (cut inventory intent) intent
  exact ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2.trans first.2.2⟩

inductive Stop where
  | private unavailable (reason : ¬ Input.Eligible epoch intent (current epoch (cut inventory intent).inputs))
  | private refused (eligible : Input.Eligible epoch intent (current epoch (cut inventory intent).inputs))
      (absent : Input.choose epoch intent (current epoch (cut inventory intent).inputs) = none)
      (actual : ∃ item ∈ (Mandate.law base epoch.scope).rawItems (current epoch (cut inventory intent).inputs)
        (Input.emit (cut inventory intent) intent), ¬ (Mandate.law base epoch.scope).Valid item.before item.request)

inductive Phase where
  | revision | challenge | admission
  deriving DecidableEq

def firstPhase : Phase :=
  if Mandate.Response.Active (current epoch inventory.inputs) then .challenge
  else if Input.Eligible epoch .admission (current epoch inventory.inputs) then .admission
  else .revision

inductive Execution : Inventory epoch → Type where
  | private stopped (inventory : Inventory epoch) (intent : Intent) (reason : Stop inventory intent) : Execution inventory
  | private revised (inventory : Inventory epoch)
      (payment : Input.Paid epoch .revision (current epoch (cut inventory .revision).inputs))
      (selected : Input.choose epoch .revision (current epoch (cut inventory .revision).inputs) = some payment) : Execution inventory
  | private progressed (inventory : Inventory epoch) (intent : Intent)
      (payment : Input.Paid epoch intent (current epoch (cut inventory intent).inputs))
      (selected : Input.choose epoch intent (current epoch (cut inventory intent).inputs) = some payment)
      (next : Execution (after inventory intent)) : Execution inventory

/-- Recurse on the actual private execution while retaining its dependent endpoint. -/
def Execution.fold (motive : (saved : Inventory epoch) → Execution saved → Sort u)
    (stopped : (saved : Inventory epoch) → (intent : Intent) → (reason : Stop saved intent) →
      motive saved (.stopped saved intent reason))
    (revised : (saved : Inventory epoch) →
      (payment : Input.Paid epoch .revision (current epoch (cut saved .revision).inputs)) →
      (selected : Input.choose epoch .revision (current epoch (cut saved .revision).inputs) = some payment) →
      motive saved (.revised saved payment selected))
    (progressed : (saved : Inventory epoch) → (intent : Intent) →
      (payment : Input.Paid epoch intent (current epoch (cut saved intent).inputs)) →
      (selected : Input.choose epoch intent (current epoch (cut saved intent).inputs) = some payment) →
      (next : Execution (after saved intent)) → motive (after saved intent) next →
      motive saved (.progressed saved intent payment selected next)) :
    {saved : Inventory epoch} → (actual : Execution saved) → motive saved actual
  | _,.stopped saved intent reason => stopped saved intent reason
  | _,.revised saved payment selected => revised saved payment selected
  | _,.progressed saved intent payment selected next =>
      progressed saved intent payment selected next (Execution.fold motive stopped revised progressed next)

theorem Execution.fold_eq_rec (motive : (saved : Inventory epoch) → Execution saved → Sort u)
    (stopped : (saved : Inventory epoch) → (intent : Intent) → (reason : Stop saved intent) →
      motive saved (.stopped saved intent reason))
    (revised : (saved : Inventory epoch) →
      (payment : Input.Paid epoch .revision (current epoch (cut saved .revision).inputs)) →
      (selected : Input.choose epoch .revision (current epoch (cut saved .revision).inputs) = some payment) →
      motive saved (.revised saved payment selected))
    (progressed : (saved : Inventory epoch) → (intent : Intent) →
      (payment : Input.Paid epoch intent (current epoch (cut saved intent).inputs)) →
      (selected : Input.choose epoch intent (current epoch (cut saved intent).inputs) = some payment) →
      (next : Execution (after saved intent)) → motive (after saved intent) next →
      motive saved (.progressed saved intent payment selected next)) {saved : Inventory epoch} (actual : Execution saved) :
    Execution.fold motive stopped revised progressed actual =
      Execution.rec (motive := motive) stopped revised progressed actual := by
  induction actual
  next => rfl
  next => rfl
  next saved intent payment selected next ih =>
    exact congrArg (progressed saved intent payment selected next) ih

private def proceed (next : Unit → Execution (after inventory intent)) : Execution inventory :=
  Input.Outcome.fold epoch (Result := Execution inventory)
    (fun payment selected _ => .progressed inventory intent payment selected (next ()))
    (fun reason => .stopped inventory intent (.unavailable reason))
    (fun eligible absent actual => .stopped inventory intent (.refused eligible absent actual))
    (outcome inventory intent)

private def finish : Execution inventory :=
  Input.Outcome.fold epoch (Result := Execution inventory)
    (fun payment selected _ => .revised inventory payment selected)
    (fun reason => .stopped inventory .revision (.unavailable reason))
    (fun eligible absent actual => .stopped inventory .revision (.refused eligible absent actual))
    (outcome inventory .revision)

private def exiting (inventory : Inventory epoch) : Execution inventory :=
  proceed inventory .exit (fun _ => finish (after inventory .exit))

private def renewing (inventory : Inventory epoch) : Execution inventory :=
  proceed inventory .renewal (fun _ => exiting (after inventory .renewal))

private def challenging (inventory : Inventory epoch) : Execution inventory :=
  proceed inventory .challenge (fun _ =>
    let saved := after inventory .challenge
    if (current epoch saved.inputs).technology.holder.isSome then
      if Input.Eligible epoch .renewal (current epoch saved.inputs) then renewing saved else exiting saved
    else finish saved)

private def admitting (inventory : Inventory epoch) : Execution inventory :=
  proceed inventory .admission (fun _ => challenging (after inventory .admission))

def produce : Execution inventory :=
  match firstPhase inventory with
  | .revision => finish inventory
  | .challenge => challenging inventory
  | .admission => admitting inventory

def Execution.finalInventory : {inventory : Inventory epoch} → Execution inventory → Inventory epoch
  | _, .stopped saved intent _ => after saved intent
  | _, .revised saved .. => after saved .revision
  | _, .progressed _ _ _ _ next => next.finalInventory

def Execution.finalFinancialRun : {inventory : Inventory epoch} → (execution : Execution inventory) →
    (Financial.Family.process sources).Run inventory.finance.current execution.finalInventory.finance.current
  | _, .stopped saved intent _ => financialRun saved intent
  | _, .revised saved .. => financialRun saved .revision
  | _, .progressed saved intent _ _ next => (financialRun saved intent).concatRuns _ next.finalFinancialRun

theorem Execution.all_past_cohorts_continue (execution : Execution inventory) :
    execution.finalInventory.pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ∧
    execution.finalInventory.pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ∧
    execution.finalInventory.pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := by
  induction execution
  next saved intent reason => exact all_past_cohorts_are_consumed saved intent
  next saved payment selected => exact all_past_cohorts_are_consumed saved .revision
  next saved intent payment selected next ih =>
      have first := all_past_cohorts_are_consumed saved intent
      exact ⟨ih.1.trans first.1,ih.2.1.trans first.2.1,ih.2.2.trans first.2.2⟩

theorem Execution.inputs_extend_the_saved_history (execution : Execution inventory) :
    inventory.inputs <+: execution.finalInventory.inputs := by
  induction execution
  next saved intent reason => exact (cut_inputs_extend_the_saved_history saved intent).trans (after_inputs_extend_the_trial saved intent)
  next saved payment selected => exact (cut_inputs_extend_the_saved_history saved .revision).trans (after_inputs_extend_the_trial saved .revision)
  next saved intent payment selected next ih =>
      exact ((cut_inputs_extend_the_saved_history saved intent).trans (after_inputs_extend_the_trial saved intent)).trans ih


def records : List (Sigma fun _ : Inventory epoch => Intent) :=
  if retried inventory intent then [⟨inventory,intent⟩,⟨cut inventory intent,intent⟩]
  else [⟨cut inventory intent,intent⟩]

theorem every_record_ends_in_the_actual_after (record : Sigma fun _ : Inventory epoch => Intent)
    (member : record ∈ records inventory intent) : (Input.advance record.1 record.2).inputs <+: (after inventory intent).inputs := by
  unfold records at member
  split at member
  next retry =>
    rcases List.mem_cons.mp member with first | second
    · cases first
      have same : cut inventory intent = Input.advance inventory intent := if_pos retry
      rw [← same]
      exact after_inputs_extend_the_trial inventory intent
    · cases List.mem_singleton.mp second
      exact ⟨[], by simp [after]⟩
  next noRetry =>
    cases List.mem_singleton.mp member
    exact ⟨[], by simp [after]⟩

def Execution.records : {inventory : Inventory epoch} → Execution inventory → List (Sigma fun _ : Inventory epoch => Intent)
  | _, .stopped saved intent _ => Programme.records saved intent
  | _, .revised saved .. => Programme.records saved .revision
  | _, .progressed saved intent _ _ next => Programme.records saved intent ++ next.records

theorem Execution.every_record_is_an_actual_prefix (execution : Execution inventory) :
    ∀ record ∈ execution.records, (Input.advance record.1 record.2).inputs <+: execution.finalInventory.inputs := by
  induction execution
  next saved intent reason => exact every_record_ends_in_the_actual_after saved intent
  next saved payment selected => exact every_record_ends_in_the_actual_after saved .revision
  next saved intent payment selected next ih =>
    intro record member
    rcases List.mem_append.mp member with first | rest
    · exact (every_record_ends_in_the_actual_after saved intent record first).trans (next.inputs_extend_the_saved_history (after saved intent))
    · exact ih record rest

private theorem appended_word_is_actual (pastInputs suffix : List (List Action)) (word : List Action) :
    (OutstandingSource.History.actualExecution epoch.source (pastInputs ++ [word] ++ suffix) (pastInputs.length + 1)).submitted = word ∧
    (OutstandingSource.History.actualExecution epoch.source (pastInputs ++ [word] ++ suffix) (pastInputs.length + 1)).before = current epoch pastInputs := by
  constructor
  · have inside : pastInputs.length < (pastInputs ++ [word] ++ suffix).length := by simp
    rw [OutstandingSource.History.scheduled_input_is_actual epoch.source _ pastInputs.length inside]
    simp only [List.append_assoc,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.cons_append,List.nil_append,List.getElem_cons_zero]
  · have same := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
      epoch.source pastInputs ([word] ++ suffix) (pastInputs.length + 2) (Nat.le_refl _)
    change OutstandingSource.History.currentAt epoch.source (pastInputs ++ [word] ++ suffix) (pastInputs.length + 2) = _
    rw [(OutstandingSource.History.actual_frame epoch.source _ _).1,List.append_assoc,same]
    exact (OutstandingSource.History.actual_frame epoch.source pastInputs _).1.symm

theorem each_record_is_interpreted_in_the_final_root (execution : Execution inventory)
    (record : Sigma fun _ : Inventory epoch => Intent) (member : record ∈ execution.records) :
    let inputs := (World.reviewed execution.finalInventory).inputs
    (OutstandingSource.History.actualExecution epoch.source inputs (record.1.inputs.length + 1)).submitted = Input.emit record.1 record.2 ∧
    (OutstandingSource.History.actualExecution epoch.source inputs (record.1.inputs.length + 1)).before = current epoch record.1.inputs ∧
    (OutstandingSource.History.actualExecution epoch.source inputs ((Input.staged record.1 record.2).inputs.length + 1)).submitted = Input.repayment record.1 record.2 ∧
    (OutstandingSource.History.actualExecution epoch.source inputs ((Input.staged record.1 record.2).inputs.length + 1)).before =
      current epoch (Input.staged record.1 record.2).inputs := by
  have pastInputs := (execution.every_record_is_an_actual_prefix inventory record member).trans
    (show execution.finalInventory.inputs <+: (World.reviewed execution.finalInventory).inputs from
      ⟨_,(World.review_inputs_exact execution.finalInventory).symm⟩)
  obtain ⟨suffix,same⟩ := pastInputs
  dsimp
  rw [← same,Input.inputs_exact]
  have first := appended_word_is_actual (epoch := epoch) record.1.inputs
    (Input.repayment record.1 record.2 :: suffix) (Input.emit record.1 record.2)
  have second := appended_word_is_actual (epoch := epoch) (Input.staged record.1 record.2).inputs suffix (Input.repayment record.1 record.2)
  have shape : (record.1.inputs ++ [Input.emit record.1 record.2,Input.repayment record.1 record.2]) ++ suffix =
      (Input.staged record.1 record.2).inputs ++ [Input.repayment record.1 record.2] ++ suffix := by
    change _ = (record.1.inputs ++ [Input.emit record.1 record.2]) ++ [Input.repayment record.1 record.2] ++ suffix
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  have joined : (record.1.inputs ++ [Input.emit record.1 record.2,Input.repayment record.1 record.2]) ++ suffix =
      record.1.inputs ++ [Input.emit record.1 record.2] ++ (Input.repayment record.1 record.2 :: suffix) := by
    simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine ⟨?_,?_,?_,?_⟩
  · rw [joined]; exact first.1
  · rw [joined]; exact first.2
  · rw [shape]; exact second.1
  · rw [shape]; exact second.2

def Execution.continuation (execution : Execution inventory) := World.Runtime.continuationFromRoot execution.finalInventory
def Execution.packet (execution : Execution inventory) : Packet := execution.continuation.packet _
def Execution.financialRun (execution : Execution inventory) :
    (Financial.Family.process sources).Run inventory.finance.current execution.packet.2.finance.current :=
  execution.finalFinancialRun.concatRuns _ (execution.continuation.financialRun _)


private theorem records_start_here : (records inventory intent).head? = some ⟨inventory,intent⟩ := by
  unfold records
  split
  · rfl
  next noRetry =>
    have own : cut inventory intent = inventory := if_neg noRetry
    rw [own]
    rfl

private theorem proceed_records_start_here (following : Unit → Execution (after inventory intent)) :
    (proceed inventory intent following).records.head? = some ⟨inventory,intent⟩ := by
  unfold proceed
  cases outcome inventory intent
  next payment selected actual =>
    change (records inventory intent ++ (following ()).records).head? = _
    unfold records
    split
    · rfl
    next noRetry =>
      have own : cut inventory intent = inventory := if_neg noRetry
      rw [own]
      rfl
  next reason => exact records_start_here inventory intent
  next eligible absent actual => exact records_start_here inventory intent

theorem paid_choice_needs_no_retry (payment : Input.Paid epoch intent (current epoch inventory.inputs))
    (selected : Input.choose epoch intent (current epoch inventory.inputs) = some payment) :
    retried inventory intent = false := by
  unfold retried
  cases Input.outcome epoch intent (current epoch inventory.inputs)
  next other chosen actual => rfl
  next reason => exact False.elim (reason payment.legal.1)
  next eligible absent actual => cases absent.symm.trans selected

theorem eligible_failed_choice_generates_retry
    (eligible : Input.Eligible epoch intent (current epoch inventory.inputs))
    (absent : Input.choose epoch intent (current epoch inventory.inputs) = none) : retried inventory intent = true := by
  unfold retried
  cases Input.outcome epoch intent (current epoch inventory.inputs)
  next payment selected actual => cases absent.symm.trans selected
  next reason => exact False.elim (reason eligible)
  next eligible absent actual => rfl

theorem an_active_start_actually_emits_challenge_first
    (active : Mandate.Response.Active (current epoch inventory.inputs)) :
    (produce inventory).records.head? = some ⟨inventory,.challenge⟩ := by
  have first : firstPhase inventory = .challenge := if_pos active
  unfold produce
  rw [first]
  unfold challenging
  exact proceed_records_start_here inventory .challenge _

theorem a_selected_revision_finishes_at_its_original_actual_after
    (first : firstPhase inventory = .revision)
    (payment : Input.Paid epoch .revision (current epoch inventory.inputs))
    (selected : Input.choose epoch .revision (current epoch inventory.inputs) = some payment) :
    (produce inventory).finalInventory = Input.advance inventory .revision := by
  have noRetry := paid_choice_needs_no_retry inventory .revision payment selected
  have own : cut inventory .revision = inventory := by unfold cut; rw [noRetry]; rfl
  unfold produce
  rw [first]
  unfold finish
  cases outcome inventory .revision
  next other chosen actual =>
    change after inventory .revision = _
    unfold after
    rw [own]
  next reason =>
    have available : Input.Eligible epoch .revision (current epoch (cut inventory .revision).inputs) := by
      rw [own]
      exact payment.legal.1
    exact False.elim (reason available)
  next eligible absent actual =>
    have none : Input.choose epoch .revision (current epoch inventory.inputs) = none := by
      change Input.choose epoch .revision (current epoch (cut inventory .revision).inputs) = none at absent
      rw [own] at absent
      exact absent
    cases none.symm.trans selected

def finalInventory := (produce inventory).finalInventory
abbrev I := World.reviewInput (finalInventory inventory)
def packet := (produce inventory).packet

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Programme
