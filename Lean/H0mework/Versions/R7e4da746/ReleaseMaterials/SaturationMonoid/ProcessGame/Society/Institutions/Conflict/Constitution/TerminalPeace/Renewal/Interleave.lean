import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal

open ExposureGuard (Scheduler)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Capitalism.Universal.Abolition.Material (ActualAndIndependent)

noncomputable section

/-- A queue can contain arbitrarily many ordinary scheduler visits.
Later submissions and arbitration can read the already executed prefix.
New arrivals can join the next queue after the due service has run. -/
structure Interleaving (history : Original.Word) where
  scheduler : WarScheduler
  queueLength : Nat → Ready history → Nat
  firstPerson : Nat → Ready history → Bool
  replies : (ordinal : Nat) → (past offered : Original.Word) →
    (current : Ready history) → (request : Request) → Replies current.val.native request

structure Visit (history : Original.Word) where
  private mk ::
  ready : Ready history
  inputs : Original.Word
  pending : Nat

namespace Interleaving

variable {history : Original.Word} (policy : Interleaving history)

def start (origin : Ready history) : Visit history :=
  ⟨origin, [], policy.queueLength 0 origin⟩

def observedHistory (prior : Visit history) : Original.Word :=
  history ++ [some service] ++ prior.inputs

def originalProposal (prior : Visit history) :=
  policy.scheduler.proposal prior.inputs.length (observedHistory prior)

def submission (prior : Visit history) : Submitted prior.ready.val.native :=
  let ordinal := prior.inputs.length
  let past := observedHistory prior
  let proposed := policy.originalProposal prior
  let request := proposed.getD .stopReview
  ⟨request, policy.replies ordinal past (policy.scheduler.offer ordinal past [proposed]) prior.ready request⟩

def firstAt (prior : Visit history) : Bool :=
  policy.firstPerson prior.inputs.length prior.ready

/-- A queued request always goes through the original lanes. At the end
of a finite queue the due service writes before another queue opens. -/
def next (prior : Visit history) : Visit history :=
  match prior.pending with
  | 0 =>
    let current := renew prior.ready (policy.firstAt prior)
    let past := prior.inputs ++ [some (orderedService (policy.firstAt prior))]
    ⟨current, past, policy.queueLength past.length current⟩
  | remaining + 1 =>
    ⟨dispatch prior.ready (policy.submission prior), prior.inputs ++ [policy.originalProposal prior], remaining⟩

def nextWholeWrite (prior : Visit history) : AnyAuthoritativeRootCurrent :=
  match prior.pending with
  | 0 =>
    let accepted := the_service_is_admitted_from_its_current_stock
      prior.ready.val.native prior.ready.property (policy.firstAt prior)
    let action := prior.ready.val.stepAction (orderedService (policy.firstAt prior)) accepted
    ⟨prior.ready.val.state.world, action.target.targetAnswerAndNext.nextCurrent⟩
  | _ + 1 => dispatchWhole prior.ready (policy.submission prior)

def runFrom (origin : Visit history) : Nat → Visit history
  | 0 => origin
  | n + 1 => policy.next (runFrom origin n)

def run (origin : Ready history) : Nat → Visit history := policy.runFrom (policy.start origin)

theorem runFrom_add (origin : Visit history) (n m : Nat) :
    policy.runFrom origin (n + m) = policy.runFrom (policy.runFrom origin n) m := by
  induction m with
  | zero => rfl
  | succ m earlier =>
    change policy.next (policy.runFrom origin (n + m)) = policy.next (policy.runFrom (policy.runFrom origin n) m)
    rw [earlier]

theorem next_at_service (prior : Visit history) (due : prior.pending = 0) :
    (policy.next prior).ready = renew prior.ready (policy.firstAt prior) := by
  simp only [next, due]

theorem next_at_queue (prior : Visit history) (remaining : Nat) (active : prior.pending = remaining + 1) :
    (policy.next prior).ready = dispatch prior.ready (policy.submission prior) ∧
      (policy.next prior).pending = remaining := by
  simp only [next, active, and_self]

theorem next_is_the_whole_successor_of_the_original_visit (prior : Visit history) :
    policy.nextWholeWrite prior = (policy.next prior).ready.val.state.resident.erase := by
  cases queue : prior.pending with
  | zero =>
    rw [next_at_service _ _ queue]
    simp only [nextWholeWrite, queue]
    exact write_is_the_original_whole_successor _ _ _
  | succ remaining =>
    rw [(next_at_queue _ _ remaining queue).1]
    simp only [nextWholeWrite, queue]
    exact dispatch_is_the_original_whole_successor _ _

theorem next_has_its_original_clock_cell (prior : Visit history) :
    (policy.next prior).ready.val.native.raw.clock = prior.ready.val.native.raw.clock ∨
    (policy.next prior).ready.val.native.raw.clock = prior.ready.val.native.raw.clock + 1 := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active, renew_raw]
    exact Or.inr rfl
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_has_its_original_clock_cell _ _

theorem next_has_one_original_position (prior : Visit history) :
    ∃ request, (policy.next prior).inputs = prior.inputs ++ [request] := by
  cases active : prior.pending with
  | zero => exact ⟨some (orderedService (policy.firstAt prior)), by simp only [next, active]⟩
  | succ remaining => exact ⟨policy.originalProposal prior, by simp only [next, active]⟩

theorem next_keeps_original_balances (prior : Visit history) :
    (policy.next prior).ready.val.state.stack.balances = prior.ready.val.state.stack.balances := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active]
    exact renew_keeps_original_balances _ _
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_keeps_original_balances _ _

theorem next_keeps_material_principal (prior : Visit history) :
    (policy.next prior).ready.val.native.raw.claims = prior.ready.val.native.raw.claims := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active, renew_raw]
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_keeps_material_principal _ _

theorem next_has_no_damage (prior : Visit history) : NoNewDamage (policy.next prior).ready.val := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active]
    exact write_has_no_new_damage _ _ _
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_has_no_new_damage _ _

theorem next_pays_at_each_hour (prior : Visit history)
    (elapsed : prior.ready.val.native.raw.clock < (policy.next prior).ready.val.native.raw.clock)
    (person : Bool) :
    1 ≤ foodPaid (policy.next prior).ready.val.items person := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active]
    exact (renew_pays_each_person _ _ person).ge
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1] at elapsed ⊢
    exact dispatch_pays_every_elapsed_hour _ _ elapsed person

theorem next_keeps_every_item_exit (prior : Visit history) :
    ItemExits (policy.next prior).ready.val.items := by
  cases active : prior.pending with
  | zero =>
    rw [next_at_service _ _ active]
    exact admitted_items_have_independent_exits prior.ready.val.native (orderedService (policy.firstAt prior))
      (the_service_is_admitted_from_its_current_stock prior.ready.val.native prior.ready.property (policy.firstAt prior))
  | succ remaining =>
    rw [(next_at_queue _ _ remaining active).1]
    exact dispatch_keeps_every_item_exit _ _

theorem next_keeps_personal_exit (prior : Visit history) (person : Bool) :
    ActualAndIndependent Supply.revisedInput (policy.next prior).ready.val.native.raw (Supply.personalWord person) :=
  every_cut_has_a_personal_exit _ person

end Interleaving

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal
