import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Plan

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (ready : Ready bound inputs)

def refusedRequest : Action := ⟨ready.actor, [], .service, [.service], .present⟩

theorem original_request_is_really_refused :
    ¬ (law ready).Valid ((law ready).next (initial ready) []) (refusedRequest ready) := by
  intro accepted
  have permission := accepted.2.1 .service (by simp [refusedRequest, RawLaw.requiredPorts, RawLaw.debit])
  rcases permission with permitted | consent
  · have noHolder : ((law ready).next (initial ready) []).technology.holder = none := ready.quiet.1
    change decide (((law ready).next (initial ready) []).technology.holder = some ready.actor) = true at permitted
    have hasHolder := of_decide_eq_true permitted
    rw [noHolder] at hasHolder
    cases hasHolder
  · exact List.not_mem_nil consent

def debtPositions (current : Current) := Settlement.addresses.filter fun position => decide (0 < Repayment.balance position current)

def source : OutstandingSource Bool Good Mandate.Source.Port (State Bool Unit) Unit where
  seed := {
    law := law ready
    initial := initial ready
    task := ready.task
    actionsAt := emitAt ready
    budget := 0
    original := [refusedRequest ready]
    refused := ⟨⟨0, (law ready).next (initial ready) [], refusedRequest ready⟩,
      List.mem_cons_self, original_request_is_really_refused ready⟩ }
  positive := by
    intro slot member
    rcases List.mem_append.mp member with old | fresh
    · exact bound.source.positive slot old
    · obtain ⟨actor, _, member⟩ := List.mem_flatMap.mp fresh
      simp only [base, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨(.service,1), by simp, by decide⟩
  completionReport := fun current => .original current (Repayment.Portfolio.word (law ready) (debtPositions current) current)

def newBound : BoundSource base ready.scope := ⟨source ready,rfl⟩
def start := (source ready).canonicalPrefix 2 |>.frame.raw
def firstWord := emitAt ready (start ready)
def firstInputs := [firstWord ready]
def afterService := OutstandingSource.History.currentAt (source ready) (firstInputs ready) 3

def responseWord := Repayment.Portfolio.word (law ready) (debtPositions (afterService ready)) (afterService ready)
def epochInputs := [firstWord ready,responseWord ready]
abbrev I := OutstandingSource.History.input (source ready) (epochInputs ready)
abbrev actual (depth : Nat) := OutstandingSource.History.actualExecution (source ready) (epochInputs ready) depth
abbrev current (ordinal : Nat) := OutstandingSource.History.currentAt (source ready) (epochInputs ready) ordinal

theorem initial_is_the_actual_review_successor : (I ready).initial = after bound inputs := rfl

theorem first_word_is_actually_emitted : (actual ready 1).submitted = firstWord ready := by
  exact OutstandingSource.History.scheduled_input_is_actual _ _ 0 (by simp [epochInputs])

theorem first_word_uses_the_actual_start : (actual ready 1).before = start ready := by
  have previous := OutstandingSource.History.finite_prefix_exact (source ready) (epochInputs ready) 0 (by simp [epochInputs])
  exact (OutstandingSource.History.actual_frame (source ready) (epochInputs ready) 2).1.trans
    (congrArg (fun past => past.frame.raw) previous)

theorem response_is_the_actual_second_word : (actual ready 2).submitted = responseWord ready :=
  OutstandingSource.History.scheduled_input_is_actual _ _ 1 (by simp [epochInputs])

theorem response_uses_the_actual_first_after : (actual ready 2).before = afterService ready := by
  exact Mandate.Challenge.Cross.emitted_word_uses_actual_cut (newBound ready) (firstInputs ready) (responseWord ready)

def homologous (index : bound.source.Slot) : (source ready).Slot :=
  ⟨index.val, by
    change index.val < (bound.source.seed.task.slots ++ _).length
    rw [List.length_append]
    omega⟩

theorem original_slot_content_is_preserved (index : bound.source.Slot) :
    (source ready).seed.slot (homologous ready index) = bound.source.seed.slot index := by
  change (bound.source.seed.task.slots ++ _)[index.val] = bound.source.seed.task.slots[index.val]
  exact List.getElem_append_left index.isLt

theorem service_projection (before : Current) (word : List Action) (index : bound.source.Slot)
    (paid : (source ready).SlotPaid before word (homologous ready index)) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law ready) before word
      (bound.source.seed.slot index).bearer (bound.source.seed.slot index).goods (bound.source.seed.slot index).purpose := by
  have payment := paid.2.2
  rw [original_slot_content_is_preserved ready index] at payment
  simpa only [source] using payment

theorem selected_word_really_pays (paid : Paid ready (start ready)) (selected : select ready (start ready) = some paid) :
    (∀ item ∈ (law ready).rawItems (actual ready 1).before (actual ready 1).submitted,
      (law ready).Valid item.before item.request) ∧
    ServiceAdequate (law ready) (actual ready 1).before ready.task (actual ready 1).submitted := by
  rw [first_word_is_actually_emitted,first_word_uses_the_actual_start]
  exact selected_word_pays_the_generated_scope ready _ paid selected

def actualPaidOpening (paid : Paid ready (start ready)) (selected : select ready (start ready) = some paid) :
    PaidOpening ready (actual ready 1).before (actual ready 1).submitted :=
  (decodePaidOpening ready (actual ready 1).before (actual ready 1).submitted).get (by
    rw [first_word_is_actually_emitted,first_word_uses_the_actual_start]
    exact selected_word_has_its_own_paid_opening ready _ paid selected)

inductive Outcome where
  | private paid (payment : Paid ready (start ready)) (selected : select ready (start ready) = some payment)
      (opening : PaidOpening ready (actual ready 1).before (actual ready 1).submitted)
  | private blocked (absent : select ready (start ready) = none)
      (all : ∀ method ∈ methods, ¬ Pass ready (start ready) method)

def outcome : Outcome ready :=
  match selected : select ready (start ready) with
  | some paid => .paid paid selected (actualPaidOpening ready paid selected)
  | none => .blocked selected (blocked_menu_has_actual_failed_checks ready _ selected)

def Outcome.paidOpening? : Outcome ready → Option (PaidOpening ready (actual ready 1).before (actual ready 1).submitted)
  | .paid _ _ opening => some opening
  | .blocked .. => none

theorem selected_actual_opening_is_in_the_generated_outcome (paid : Paid ready (start ready))
    (selected : select ready (start ready) = some paid) :
    (outcome ready).paidOpening? ready = some (actualPaidOpening ready paid selected) := by
  unfold outcome
  split
  next payment actual =>
    have same : payment = paid := Option.some.inj (actual.symm.trans selected)
    subst payment
    rfl
  next absent => cases absent.symm.trans selected

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
