import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

structure Demand (intent : Intent) (before : Current) where
  private mk ::
  failed : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit
  actual : failed ∈ (epochLaw ready).rawItems before (core ready intent before)
  refused : ¬ (epochLaw ready).Valid failed.before failed.request
  debit : (Bool × Good) × ℚ
  required : debit ∈ (epochLaw ready).debit failed.before failed.request
  shortfall : 0 < debit.2 - failed.before.stock debit.1.1 debit.1.2

def demands (intent : Intent) (before : Current) : List (Demand ready intent before) :=
  ((epochLaw ready).rawItems before (core ready intent before)).attach.flatMap fun item =>
    if refused : ¬ (epochLaw ready).Valid item.val.before item.val.request then
      ((epochLaw ready).debit item.val.before item.val.request).attach.filterMap fun debit =>
        if shortfall : 0 < debit.val.2 - item.val.before.stock debit.val.1.1 debit.val.1.2 then
          some ⟨item.val, item.property, refused, debit.val, debit.property, shortfall⟩ else none
    else []

def Demand.request {intent : Intent} {before : Current} (demand : Demand ready intent before) : Action :=
  ⟨!demand.debit.1.1, [], .resource, [], .transfer (!demand.debit.1.1) demand.debit.1.1
    [(demand.debit.1.2, demand.debit.2 - demand.failed.before.stock demand.debit.1.1 demand.debit.1.2)]⟩

def emitAt (intent : Intent) (before : Current) :=
  core ready intent before ++ (demands ready intent before).map (Demand.request ready)

theorem every_demand_is_a_real_shortfall_in_the_emitted_word (intent : Intent) (before : Current)
    (demand : Demand ready intent before) (member : demand ∈ demands ready intent before) :
    demand.failed ∈ (epochLaw ready).rawItems before (emitAt ready intent before) ∧
    ¬ (epochLaw ready).Valid demand.failed.before demand.failed.request ∧
    demand.debit ∈ (epochLaw ready).debit demand.failed.before demand.failed.request ∧
    0 < demand.debit.2 - demand.failed.before.stock demand.debit.1.1 demand.debit.1.2 ∧
    demand.request ready ∈ emitAt ready intent before := by
  refine ⟨?_, demand.refused, demand.required, demand.shortfall, ?_⟩
  · unfold emitAt RawLaw.rawItems
    rw [(epochLaw ready).execute_append]
    exact List.mem_append_left _ demand.actual
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨demand, member, rfl⟩)

theorem paid_word_is_the_actual_selected_candidate (intent : Intent) (before : Current)
    (paid : Paid ready intent before) (chosen : choose ready intent before = some paid) :
    emitAt ready intent before = candidate ready intent before paid.choice := by
  have same : core ready intent before = candidate ready intent before paid.choice := by
    simp only [core, selected, chosen, Option.map_some, Option.getD_some]
  have empty : demands ready intent before = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro demand _
    exact demand.refused (paid.legal.2 demand.failed (same ▸ demand.actual))
  simp only [emitAt, same, empty, List.map_nil, List.append_nil]

inductive Outcome (intent : Intent) (before : Current) where
  | private paid (payment : Paid ready intent before) (selected : choose ready intent before = some payment)
      (actual : ∀ item ∈ (epochLaw ready).rawItems before (emitAt ready intent before),
        (epochLaw ready).Valid item.before item.request)
  | private unavailable (ineligible : ¬ Eligible ready intent before)
  | private blocked (eligible : Eligible ready intent before) (absent : choose ready intent before = none)
      (refusal : ∃ item ∈ (epochLaw ready).rawItems before (emitAt ready intent before),
        ¬ (epochLaw ready).Valid item.before item.request)

def outcome (intent : Intent) (before : Current) : Outcome ready intent before :=
  match selected : choose ready intent before with
  | some paid => .paid paid selected (by
      rw [paid_word_is_the_actual_selected_candidate ready intent before paid selected]
      exact paid.legal.2)
  | none => if eligible : Eligible ready intent before then
      .blocked eligible selected (by
        obtain ⟨item, present, refused⟩ := an_eligible_blocked_core_has_an_actual_refused_item ready intent before eligible selected
        refine ⟨item, ?_, refused⟩
        unfold emitAt RawLaw.rawItems
        rw [(epochLaw ready).execute_append]
        exact List.mem_append_left _ present)
    else .unavailable eligible

variable {originInputs : List (List Action)} (inventory : Inventory ready originInputs)

def emit (intent : Intent) := emitAt ready intent (current ready inventory.inputs)
noncomputable def staged (intent : Intent) := submit ready inventory (emit ready inventory intent)
noncomputable def advance (intent : Intent) := Settlement.advance ready (staged ready inventory intent)
noncomputable abbrev I (intent : Intent) := Settlement.I ready (staged ready inventory intent)
noncomputable abbrev execution (intent : Intent) := OutstandingSource.History.actualExecution (epochSource ready) (advance ready inventory intent).inputs (inventory.inputs.length + 1)

theorem inputs_exact (intent : Intent) :
    (advance ready inventory intent).inputs = inventory.inputs ++
      [emit ready inventory intent, Settlement.emit ready (staged ready inventory intent)] := by
  change (inventory.inputs ++ [emit ready inventory intent]) ++ [Settlement.emit ready (staged ready inventory intent)] = _
  rw [List.append_assoc]
  rfl

theorem actual_word_and_cut (intent : Intent) :
    (execution ready inventory intent).submitted = emit ready inventory intent ∧
    (execution ready inventory intent).before = current ready inventory.inputs := by
  constructor
  · have member : inventory.inputs.length < (advance ready inventory intent).inputs.length := by
      rw [inputs_exact]
      simp
    have actual := OutstandingSource.History.scheduled_input_is_actual (epochSource ready)
      (advance ready inventory intent).inputs inventory.inputs.length member
    have same : (advance ready inventory intent).inputs[inventory.inputs.length] = emit ready inventory intent := by
      simp only [inputs_exact, List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact actual.trans same
  · have exactPrefix := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
      (epochSource ready) inventory.inputs [emit ready inventory intent, Settlement.emit ready (staged ready inventory intent)]
      (inventory.inputs.length + 2) (Nat.le_refl _)
    change OutstandingSource.History.currentAt (epochSource ready) (advance ready inventory intent).inputs
      (inventory.inputs.length + 2) = _
    rw [(OutstandingSource.History.actual_frame _ _ _).1, inputs_exact, exactPrefix]
    exact (OutstandingSource.History.actual_frame _ _ _).1.symm

noncomputable def run (inventory : Inventory ready originInputs) : List Intent → Inventory ready originInputs
  | [] => inventory
  | intent :: tail => run (advance ready inventory intent) tail

def nextIntent : Intent :=
  if (Joint.request? ready inventory).isSome then .challenge
  else if (current ready inventory.inputs).technology.holder.isSome then .renewal
  else if (current ready inventory.inputs).technology.offered.isSome then .challenge
  else if (current ready inventory.inputs).clock ≤ ready.task.deadline then .admission else .revision

noncomputable def evolve (inventory : Inventory ready originInputs) : Nat → Inventory ready originInputs
  | 0 => inventory
  | count + 1 => evolve (advance ready inventory (nextIntent ready inventory)) count

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future
