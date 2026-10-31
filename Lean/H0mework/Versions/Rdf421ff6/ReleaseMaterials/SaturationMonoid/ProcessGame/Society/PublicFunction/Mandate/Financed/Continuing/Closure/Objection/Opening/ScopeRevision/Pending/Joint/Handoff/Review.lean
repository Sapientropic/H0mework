import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future.Runtime

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.ProgrammeFace
open Followup
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  (bound : BoundSource base oldScope) (inputs : List (List Action))

abbrev originalInput := OutstandingSource.History.input bound.source inputs
abbrev before := OutstandingSource.History.currentAt bound.source inputs inputs.length
abbrev reported := ProgrammeSource.rawEvent (originalInput bound inputs)
  (ProgrammeHistory.visitAt (originalInput bound inputs) inputs.length).current
abbrev after := OutstandingSource.History.currentAt bound.source inputs (inputs.length + 2)

def Quiet (current : Current) : Prop := current.technology.holder = none ∧ current.technology.offered = none
instance (current : Current) : Decidable (Quiet current) := by unfold Quiet; infer_instance

def reviews := (commandsAt base oldScope (before bound inputs) (reported bound inputs)).filter fun event =>
  decide (event.command = .review ∧ oldScope.task.deadline < event.item.val.before.clock)

structure Ready where
  private mk ::
  actual : ActualCommand base oldScope (before bound inputs) (reported bound inputs)
  recorded : actual ∈ commandsAt base oldScope (before bound inputs) (reported bound inputs)
  review : actual.command = .review
  expired : oldScope.task.deadline < actual.item.val.before.clock
  boundary : 2 ≤ inputs.length
  quiet : Quiet (after bound inputs)

def choose : Option (Ready bound inputs) :=
  if boundary : 2 ≤ inputs.length then
    match selected : (reviews bound inputs).head? with
    | some actual =>
        if quiet : Quiet (after bound inputs) then
          let included := List.mem_filter.mp (List.mem_of_mem_head? selected)
          let checked := of_decide_eq_true included.2
          some ⟨actual, included.1, checked.1, checked.2, boundary, quiet⟩
        else none
    | none => none
  else none

inductive Blocked : Prop where
  | outside (absent : ¬ 2 ≤ inputs.length)
  | unpaid (absent : (reviews bound inputs).head? = none)
  | active (retained : ¬ Quiet (after bound inputs))

theorem every_failed_handoff_has_an_actual_reason (absent : choose bound inputs = none) : Blocked bound inputs := by
  unfold choose at absent
  split at absent
  · split at absent
    · split at absent
      · cases absent
      · exact .active (by assumption)
    · exact .unpaid (by assumption)
  · exact .outside (by assumption)

variable {bound inputs}

def Ready.actor (ready : Ready bound inputs) := ready.actual.item.val.request.signer

theorem Ready.actor_has_real_standing (ready : Ready bound inputs) : ready.actor ∈ Delegation.members oldScope.task := by
  have authority := ready.actual.authorization.2.2.2.2.2
  rw [ready.review] at authority
  exact authority

theorem Ready.actor_is_in_the_actual_root_census (ready : Ready bound inputs) :
    ActualBirth.presentAt (originalInput bound inputs)
      (ProgrammeHistory.visitAt (originalInput bound inputs) inputs.length) ready.actor := by
  change ready.actor ∈ parties (originalInput bound inputs).law _
  apply List.mem_dedup.mpr
  apply List.mem_flatMap.mpr
  refine ⟨ready.actual.item.val, ?_, List.mem_cons_self⟩
  change ready.actual.item.val ∈ bound.source.seed.law.rawItems (before bound inputs) (reported bound inputs)
  rw [bound.law_exact]
  exact ready.actual.item.property

def Ready.birth (ready : Ready bound inputs) :=
  ActualBirth.generate (originalInput bound inputs)
    (ProgrammeHistory.visitAt (originalInput bound inputs) inputs.length) ready.actor ready.actor_is_in_the_actual_root_census

private theorem step_clock (current : Current) (action : Action) :
    ((Mandate.law base oldScope).step current action).clock = current.clock := by
  unfold RawLaw.step
  split <;> rfl

private theorem item_clock (current : Current) (index : Nat) (word : List Action)
    (item : ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit)
    (member : item ∈ ((Mandate.law base oldScope).execute current index word).items) : item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons action tail ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same; rfl
      · exact (ih _ _ later).trans (step_clock _ _)

private theorem visit_clock_nondecreasing (ordinal : Nat) :
    (OutstandingSource.History.currentAt bound.source inputs ordinal).clock ≤
      (OutstandingSource.History.currentAt bound.source inputs (ordinal + 1)).clock := by
  change (ProgrammeSource.rawCurrent (originalInput bound inputs)
    (ProgrammeHistory.visitAt (originalInput bound inputs) ordinal).current).clock ≤
      (ProgrammeSource.rawCurrent (originalInput bound inputs)
        (ProgrammeSource.next (originalInput bound inputs)
          (ProgrammeHistory.visitAt (originalInput bound inputs) ordinal).current)).clock
  rw [ProgrammeSource.actual_raw_next]
  exact (originalInput bound inputs).law.next_clock_nondecreasing _ _

def Ready.actors (ready : Ready bound inputs) :=
  ((Delegation.members bound.source.seed.task ++ Delegation.members oldScope.task) ++ [ready.actor]).eraseDups

def Ready.addedActors (ready : Ready bound inputs) :=
  ready.actors.filter fun actor => decide (actor ∉ Delegation.members bound.source.seed.task)

def Ready.slots (ready : Ready bound inputs) : List (ServiceSlot Bool Good) :=
  bound.source.seed.task.slots ++ ready.addedActors.flatMap fun actor =>
    [⟨actor, base.necessities (eraseCurrent (after bound inputs)) actor, .necessity⟩,
     ⟨actor, base.mandatoryMaintenance (eraseCurrent (after bound inputs)) actor, .maintenance⟩]

def Ready.task (ready : Ready bound inputs) : PublicTaskSpec Bool Good :=
  ⟨ready.slots, (after bound inputs).clock + 2, (after bound inputs).clock + 3, by
    obtain ⟨slot, member, good, inside, positive⟩ := bound.source.seed.task.demand
    exact ⟨slot, List.mem_append_left _ member, good, inside, positive⟩⟩

theorem Ready.actual_successor_is_after_the_expired_scope (ready : Ready bound inputs) :
    oldScope.task.deadline < (after bound inputs).clock := by
  have clock := item_clock (before bound inputs) 0 (reported bound inputs) ready.actual.item.val ready.actual.item.property
  have late := ready.expired
  rw [clock] at late
  have first := visit_clock_nondecreasing (bound := bound) (inputs := inputs) inputs.length
  have second := visit_clock_nondecreasing (bound := bound) (inputs := inputs) (inputs.length + 1)
  have causal : (before bound inputs).clock ≤ (after bound inputs).clock := first.trans second
  exact lt_of_lt_of_le late causal

theorem Ready.new_window_is_after_the_actual_expired_scope (ready : Ready bound inputs) :
    oldScope.task.deadline < ready.task.earliest :=
  lt_add_of_lt_of_nonneg ready.actual_successor_is_after_the_expired_scope (by decide)

def Ready.scope (ready : Ready bound inputs) : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) :=
  ⟨ready.task, .service, .challenge, by decide, [(.service,1)]⟩

theorem every_original_task_slot_is_retained (ready : Ready bound inputs) (slot : ServiceSlot Bool Good)
    (member : slot ∈ bound.source.seed.task.slots) : slot ∈ ready.task.slots := List.mem_append_left _ member

theorem Ready.review_actor_is_in_the_generated_task (ready : Ready bound inputs) : ready.actor ∈ Delegation.members ready.task := by
  by_cases old : ready.actor ∈ Delegation.members bound.source.seed.task
  · obtain ⟨slot, inside, actor⟩ := List.mem_map.mp old
    exact List.mem_map.mpr ⟨slot, every_original_task_slot_is_retained ready slot inside, actor⟩
  · apply List.mem_map.mpr
    refine ⟨⟨ready.actor, [(.service,1)], .necessity⟩, ?_, rfl⟩
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨ready.actor, ?_, List.mem_cons_self⟩
    exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_singleton_self _)), decide_eq_true old⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
