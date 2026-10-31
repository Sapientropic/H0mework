import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Plan

/-! Actual future inputs and shortage repairs append to the saved full
inventory; the following payment and epoch are generated from its after-state. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable (epoch : Epoch)

structure Demand (intent : Intent) (before : Current) where
  private mk ::
  failed : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : failed ∈ (Mandate.law base epoch.scope).rawItems before (core epoch intent before)
  refused : ¬ (Mandate.law base epoch.scope).Valid failed.before failed.request
  debit : (Bool × Good) × ℚ
  required : debit ∈ (Mandate.law base epoch.scope).debit failed.before failed.request
  shortfall : 0 < debit.2 - failed.before.stock debit.1.1 debit.1.2

def demands (intent : Intent) (before : Current) : List (Demand epoch intent before) :=
  ((Mandate.law base epoch.scope).rawItems before (core epoch intent before)).attach.flatMap fun item =>
    if refused : ¬ (Mandate.law base epoch.scope).Valid item.val.before item.val.request then
      ((Mandate.law base epoch.scope).debit item.val.before item.val.request).attach.filterMap fun debit =>
        if shortfall : 0 < debit.val.2 - item.val.before.stock debit.val.1.1 debit.val.1.2 then
          some ⟨item.val, item.property, refused, debit.val, debit.property, shortfall⟩ else none
    else []

def Demand.request {intent : Intent} {before : Current} (demand : Demand epoch intent before) : Action :=
  ⟨!demand.debit.1.1, [], .resource, [], .transfer (!demand.debit.1.1) demand.debit.1.1
    [(demand.debit.1.2, demand.debit.2 - demand.failed.before.stock demand.debit.1.1 demand.debit.1.2)]⟩

def emitAt (intent : Intent) (before : Current) :=
  core epoch intent before ++ (demands epoch intent before).map (Demand.request epoch)

theorem every_demand_is_a_real_shortfall_in_the_emitted_word (intent : Intent) (before : Current)
    (demand : Demand epoch intent before) (member : demand ∈ demands epoch intent before) :
    demand.failed ∈ (Mandate.law base epoch.scope).rawItems before (emitAt epoch intent before) ∧
    ¬ (Mandate.law base epoch.scope).Valid demand.failed.before demand.failed.request ∧
    demand.debit ∈ (Mandate.law base epoch.scope).debit demand.failed.before demand.failed.request ∧
    0 < demand.debit.2 - demand.failed.before.stock demand.debit.1.1 demand.debit.1.2 ∧
    demand.request epoch ∈ emitAt epoch intent before := by
  refine ⟨?_, demand.refused, demand.required, demand.shortfall, ?_⟩
  · unfold emitAt RawLaw.rawItems
    rw [(Mandate.law base epoch.scope).execute_append]
    exact List.mem_append_left _ demand.actual
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨demand, member, rfl⟩)

theorem paid_word_is_the_actual_selected_candidate (intent : Intent) (before : Current)
    (paid : Paid epoch intent before) (chosen : choose epoch intent before = some paid) :
    emitAt epoch intent before = candidate epoch intent before paid.choice := by
  have same : core epoch intent before = candidate epoch intent before paid.choice := by
    simp only [core, selected, chosen, Option.map_some, Option.getD_some]
  have empty : demands epoch intent before = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro demand _
    exact demand.refused (paid.legal.2 demand.failed (same ▸ demand.actual))
  simp only [emitAt, same, empty, List.map_nil, List.append_nil]

inductive Outcome (intent : Intent) (before : Current) where
  | private paid (payment : Paid epoch intent before) (selected : choose epoch intent before = some payment)
      (actual : ∀ item ∈ (Mandate.law base epoch.scope).rawItems before (emitAt epoch intent before),
        (Mandate.law base epoch.scope).Valid item.before item.request)
  | private unavailable (ineligible : ¬ Eligible epoch intent before)
  | private blocked (eligible : Eligible epoch intent before) (absent : choose epoch intent before = none)
      (refusal : ∃ item ∈ (Mandate.law base epoch.scope).rawItems before (emitAt epoch intent before),
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request)

def outcome (intent : Intent) (before : Current) : Outcome epoch intent before :=
  match selected : choose epoch intent before with
  | some paid => .paid paid selected (by
      rw [paid_word_is_the_actual_selected_candidate epoch intent before paid selected]
      exact paid.legal.2)
  | none => if eligible : Eligible epoch intent before then
      .blocked eligible selected (by
        obtain ⟨item, present, refused⟩ := an_eligible_blocked_core_has_an_actual_refused_item epoch intent before eligible selected
        refine ⟨item, ?_, refused⟩
        unfold emitAt RawLaw.rawItems
        rw [(Mandate.law base epoch.scope).execute_append]
        exact List.mem_append_left _ present)
    else .unavailable eligible

variable {epoch} (inventory : Inventory epoch)
def emit (intent : Intent) := emitAt epoch intent (current epoch inventory.inputs)
def staged (intent : Intent) := World.submit inventory (emit inventory intent)
def repayment (intent : Intent) := Repayment.Portfolio.word (Mandate.law base epoch.scope)
  (Handoff.debtPositions (current epoch (staged inventory intent).inputs)) (current epoch (staged inventory intent).inputs)
def advance (intent : Intent) := World.submit (staged inventory intent) (repayment inventory intent)
structure Disposition (intent : Intent) where
  private mk ::
  decision : Outcome epoch intent (current epoch inventory.inputs)
  nextInventory : Inventory epoch
  exact_after : nextInventory = advance inventory intent

def produce (intent : Intent) : Disposition inventory intent :=
  ⟨outcome epoch intent (current epoch inventory.inputs),advance inventory intent,rfl⟩

abbrev I (intent : Intent) := World.I epoch (advance inventory intent).inputs
abbrev execution (intent : Intent) := OutstandingSource.History.actualExecution epoch.source (advance inventory intent).inputs (inventory.inputs.length + 1)
abbrev repaymentExecution (intent : Intent) := World.actual (staged inventory intent) (repayment inventory intent)

theorem inputs_exact (intent : Intent) :
    (advance inventory intent).inputs = inventory.inputs ++ [emit inventory intent,repayment inventory intent] := by
  change (inventory.inputs ++ [emit inventory intent]) ++ [repayment inventory intent] = _
  rw [List.append_assoc]
  rfl


theorem actual_word_and_cut (intent : Intent) :
    (execution inventory intent).submitted = emit inventory intent ∧
    (execution inventory intent).before = current epoch inventory.inputs := by
  constructor
  · have inside : inventory.inputs.length < (advance inventory intent).inputs.length := by rw [inputs_exact]; simp
    have actual := OutstandingSource.History.scheduled_input_is_actual epoch.source (advance inventory intent).inputs inventory.inputs.length inside
    have same : (advance inventory intent).inputs[inventory.inputs.length] = emit inventory intent := by
      simp only [inputs_exact,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]
    exact actual.trans same
  · have actualPrefix := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix epoch.source inventory.inputs
      [emit inventory intent,repayment inventory intent] (inventory.inputs.length + 2) (Nat.le_refl _)
    change OutstandingSource.History.currentAt epoch.source (advance inventory intent).inputs (inventory.inputs.length + 2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1,inputs_exact,actualPrefix]
    exact (OutstandingSource.History.actual_frame _ _ _).1.symm

theorem actual_repayment_word_and_cut (intent : Intent) :
    (repaymentExecution inventory intent).submitted = repayment inventory intent ∧
    (repaymentExecution inventory intent).before = current epoch (staged inventory intent).inputs := World.actual_word_and_cut _ _

def financialRun (intent : Intent) : (Financial.Family.process sources).Run inventory.finance.current (advance inventory intent).finance.current :=
  (World.financialRun inventory (emit inventory intent)).concatRuns _
    (World.financialRun (staged inventory intent) (repayment inventory intent))

def cycle (intent : Intent) : Packet := World.next (advance inventory intent)
def cycleFinancialRun (intent : Intent) : (Financial.Family.process sources).Run inventory.finance.current (cycle inventory intent).2.finance.current :=
  (financialRun inventory intent).concatRuns _ (World.nextFinancialRun (advance inventory intent))


theorem full_past_cohorts_are_preserved_before_the_next_epoch (intent : Intent) :
    (advance inventory intent).pastGrants.map GrantCohort.origin = inventory.pastGrants.map GrantCohort.origin ∧
    (advance inventory intent).pastChallenges.map ChallengeCohort.origin = inventory.pastChallenges.map ChallengeCohort.origin ∧
    (advance inventory intent).pastServices.map ServiceCohort.origin = inventory.pastServices.map ServiceCohort.origin := by
  have first := World.every_past_origin_keeps_order_and_multiplicity inventory (emit inventory intent)
  have second := World.every_past_origin_keeps_order_and_multiplicity (staged inventory intent) (repayment inventory intent)
  exact ⟨second.1.trans first.1,second.2.1.trans first.2.1,second.2.2.trans first.2.2⟩

theorem cycle_preserves_all_past_cohort_prefixes (intent : Intent) :
    inventory.pastGrants.map GrantCohort.origin <+: (cycle inventory intent).2.pastGrants.map GrantCohort.origin ∧
    inventory.pastChallenges.map ChallengeCohort.origin <+: (cycle inventory intent).2.pastChallenges.map ChallengeCohort.origin ∧
    inventory.pastServices.map ServiceCohort.origin <+: (cycle inventory intent).2.pastServices.map ServiceCohort.origin := by
  have kept := full_past_cohorts_are_preserved_before_the_next_epoch inventory intent
  have next := World.next_preserves_all_original_cohort_prefixes (advance inventory intent)
  rw [kept.1,kept.2.1,kept.2.2] at next
  exact next

def run (packet : Packet) : List Intent → Packet
  | [] => packet
  | intent :: tail => run (cycle packet.2 intent) tail

def runFinancial (packet : Packet) : (intents : List Intent) →
    (Financial.Family.process sources).Run packet.2.finance.current (run packet intents).2.finance.current
  | [] => .nil
  | intent :: tail => (cycleFinancialRun packet.2 intent).concatRuns _ (runFinancial (cycle packet.2 intent) tail)

theorem every_finite_input_epoch_chain_preserves_all_past_cohorts (packet : Packet) (intents : List Intent) :
    packet.2.pastGrants.map GrantCohort.origin <+: (run packet intents).2.pastGrants.map GrantCohort.origin ∧
    packet.2.pastChallenges.map ChallengeCohort.origin <+: (run packet intents).2.pastChallenges.map ChallengeCohort.origin ∧
    packet.2.pastServices.map ServiceCohort.origin <+: (run packet intents).2.pastServices.map ServiceCohort.origin := by
  induction intents generalizing packet with
  | nil => exact ⟨List.prefix_rfl,List.prefix_rfl,List.prefix_rfl⟩
  | cons intent tail ih =>
    have one := cycle_preserves_all_past_cohort_prefixes packet.2 intent
    have rest := ih (cycle packet.2 intent)
    exact ⟨one.1.trans rest.1,one.2.1.trans rest.2.1,one.2.2.trans rest.2.2⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
