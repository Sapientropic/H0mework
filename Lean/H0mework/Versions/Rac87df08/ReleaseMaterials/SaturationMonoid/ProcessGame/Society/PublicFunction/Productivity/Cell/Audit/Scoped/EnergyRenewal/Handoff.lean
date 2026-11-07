import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Continuation.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Request where
  replace : Bool
  actor : Party
  query : Query

structure Seed (plan : Plan) where
  private mk ::
  window : Continuation.Window plan
  requests : List Continuation.Request
  ordinal : Nat

def Seed.initial {plan : Plan} (seed : Seed plan) := seed.window.current seed.requests (seed.ordinal+1)
def Seed.scope {plan : Plan} (seed : Seed plan) := seed.window.scope
def Seed.law {plan : Plan} (seed : Seed plan) := seed.window.law

def fromConsumed {plan : Plan} (window : Continuation.Window plan)
    (requests : List Continuation.Request) (ordinal : Nat) : Seed plan := ⟨window,requests,ordinal⟩

theorem from_consumed_is_actual_next {plan : Plan} (window : Continuation.Window plan)
    (requests : List Continuation.Request) (ordinal : Nat) :
    (fromConsumed window requests ordinal).initial = ProgrammeSource.rawCurrent (window.input requests)
      (ProgrammeHistory.visitAt (window.input requests) (ordinal+1)).current := by
  rw [window.current_is_own_root_current]; rfl

def Seed.candidates {plan : Plan} (seed : Seed plan) (current : AuditCurrent) : List Party :=
  (Delegation.members seed.scope.task).eraseDups.filter fun actor =>
    actor != 0 && current.technology.holder != some actor

def Seed.target {plan : Plan} (seed : Seed plan) (current : AuditCurrent) : Party := (seed.candidates current).head?.getD 0

def topUp (recipient : Party) (required : ℚ) (current : AuditCurrent) : Action :=
  transfer recipient (max 0 (required-current.stock recipient .energy))

def Seed.readWord {plan : Plan} (seed : Seed plan) (actor : Party) (query : Query) (current : AuditCurrent) :=
  attempt seed.law current [fun _ => accessRequest actor query,fun _ => deliveryFee]

/-- Selection and both material deficits are generated from the actual source state. -/
def Seed.stages {plan : Plan} (seed : Seed plan) (target : Party) (query : Query) : List (AuditCurrent → Action) :=
  [fun current => Mandate.request seed.scope current 0 .revoke,
   topUp 0 2, topUp target 2,
   fun current => Mandate.request seed.scope current 0 (.propose target),
   fun current => Mandate.request seed.scope current target .accept,
   fun _ => accessRequest target query,fun _ => deliveryFee]

def Seed.word {plan : Plan} (seed : Seed plan) (request : Request) (current : AuditCurrent) : List Action :=
  if request.replace then
    if (seed.candidates current).isEmpty ∨ current.technology.holder.isNone then []
    else attempt seed.law current (seed.stages (seed.target current) request.query)
  else seed.readWord request.actor request.query current

def Seed.requestAt {plan : Plan} (_seed : Seed plan) (requests : List Request) (ordinal : Nat) : Request :=
  (requests[ordinal-(_seed.ordinal+1)]?).getD ⟨false,plan.candidate,defaultQuery ordinal⟩
def Seed.emit {plan : Plan} (seed : Seed plan) (requests : List Request) (current : AuditCurrent) :=
  let ordinal := current.round-seed.window.initial.round
  if ordinal ≤ seed.ordinal then seed.window.emit seed.requests current
  else seed.word (seed.requestAt requests ordinal) current

def Seed.input {plan : Plan} (seed : Seed plan) (requests : List Request) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { law := seed.law, initial := seed.window.initial, instructions := [], emission? := some (seed.emit requests) }

def Seed.current {plan : Plan} (seed : Seed plan) (requests : List Request) : Nat → AuditCurrent :=
  Nat.rec seed.window.initial (fun n current => seed.law.next current (if n = 0 then [] else seed.emit requests current))
theorem Seed.current_succ {plan : Plan} (seed : Seed plan) (requests : List Request) (n : Nat) :
    seed.current requests (n+1) = seed.law.next (seed.current requests n)
      (if n = 0 then [] else seed.emit requests (seed.current requests n)) := rfl
attribute [irreducible] Seed.current
theorem Seed.current_is_own_root_current {plan : Plan} (window : Seed plan) (requests : List Request) (n : Nat) :
    ProgrammeSource.rawCurrent (window.input requests) (ProgrammeHistory.visitAt (window.input requests) n).current =
      window.current requests n := by
  induction n with
  | zero => unfold Seed.current; rfl
  | succ n ih =>
    change ProgrammeSource.rawCurrent (window.input requests)
      (ProgrammeSource.next (window.input requests) (ProgrammeHistory.visitAt (window.input requests) n).current) = _
    rw [ProgrammeSource.actual_raw_next,ih,window.current_succ]
    cases n with
    | zero => rfl
    | succ n =>
      congr 1
      simp only [Nat.succ_ne_zero,if_false]
      rw [← ih]
      change ProgrammeSource.rawEvent (window.input requests)
        (ProgrammeSource.next (window.input requests) (ProgrammeHistory.visitAt (window.input requests) n).current) =
        window.emit requests (ProgrammeSource.rawCurrent (window.input requests)
          (ProgrammeSource.next (window.input requests) (ProgrammeHistory.visitAt (window.input requests) n).current))
      generalize (ProgrammeHistory.visitAt (window.input requests) n).current = prior
      cases prior <;> rfl

theorem Seed.current_round {plan : Plan} (window : Seed plan) (requests : List Request) (n : Nat) :
    (window.current requests n).round = window.window.initial.round+n := by
  induction n with
  | zero => unfold Seed.current; rfl
  | succ n ih => rw [window.current_succ]; change _+1 = _; rw [ih]; omega


theorem Seed.original_prefix {plan : Plan} (seed : Seed plan) (requests : List Request) (n : Nat)
    (earlier : n ≤ seed.ordinal+1) :
    seed.current requests n = seed.window.current seed.requests n := by
  induction n with
  | zero => unfold Seed.current Continuation.Window.current; rfl
  | succ n ih =>
    rw [seed.current_succ,seed.window.current_succ,ih (by omega)]
    congr 1
    split
    · rfl
    · unfold Seed.emit
      rw [seed.window.current_round]
      simp only [Nat.add_sub_cancel_left,if_pos (by omega : n ≤ seed.ordinal)]

theorem Seed.inherited_raw_items {plan : Plan} (seed : Seed plan) (requests : List Request) (n : Nat)
    (earlier : n ≤ seed.ordinal) :
    seed.law.rawItems (seed.current requests n) (if n = 0 then [] else seed.emit requests (seed.current requests n)) =
      seed.window.law.rawItems (seed.window.current seed.requests n)
        (if n = 0 then [] else seed.window.emit seed.requests (seed.window.current seed.requests n)) := by
  rw [seed.original_prefix requests n (by omega)]
  congr 1
  split
  · rfl
  · unfold Seed.emit
    rw [seed.window.current_round]
    simp only [Nat.add_sub_cancel_left,if_pos earlier]

theorem Seed.emission_uses_exact_request {plan : Plan} (seed : Seed plan) (requests : List Request) (n : Nat)
    (later : seed.ordinal < n) :
    seed.emit requests (seed.current requests n) = seed.word (seed.requestAt requests n) (seed.current requests n) := by
  unfold Seed.emit
  rw [seed.current_round]
  simp only [Nat.add_sub_cancel_left,if_neg (by omega : ¬ n ≤ seed.ordinal)]

theorem Seed.handoff_before_is_actual_parent_next {plan : Plan} (seed : Seed plan) (requests : List Request) :
    seed.current requests (seed.ordinal+1) = seed.initial := seed.original_prefix requests _ (by omega)

theorem Seed.target_is_a_different_task_member {plan : Plan} (seed : Seed plan) (current : AuditCurrent)
    (nonempty : seed.candidates current ≠ []) : seed.target current ∈ Delegation.members seed.scope.task ∧
      seed.target current ≠ 0 ∧ current.technology.holder ≠ some (seed.target current) := by
  have inside : seed.target current ∈ seed.candidates current := by
    cases h : seed.candidates current with
    | nil => exact False.elim (nonempty h)
    | cons head tail => simp [Seed.target,h]
  simpa [Seed.candidates] using inside

def Seed.requestActor {plan : Plan} (seed : Seed plan) (request : Request) (current : AuditCurrent) :=
  if request.replace then seed.target current else request.actor

theorem Seed.word_silent {plan : Plan} (seed : Seed plan) (request : Request) (current : AuditCurrent) :
    ∀ action ∈ seed.word request current,Silent action := by
  unfold Seed.word
  split
  · split
    · simp
    · apply attempt_silent
      simp only [Seed.stages,List.mem_cons,List.not_mem_nil,or_false]
      intro stage member state
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · apply attempt_silent
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member state
    rcases member with rfl | rfl <;> trivial

theorem Seed.preserves_every_claim {plan : Plan} (seed : Seed plan) (requests : List Request) (n : Nat) :
    (seed.current requests n).claims = (before plan).claims := by
  induction n with
  | zero => unfold Seed.current; exact seed.window.finance
  | succ n ih =>
    rw [seed.current_succ]
    trans (seed.current requests n).claims
    · apply silent_claims
      split
      · simp
      · unfold Seed.emit
        dsimp only
        split
        · exact seed.window.word_silent _ _
        · exact seed.word_silent _ _
    · exact ih

theorem top_up_is_exact_actual_deficit (recipient : Party) (required : ℚ) (current : AuditCurrent) :
    topUp recipient required current = transfer recipient (max 0 (required-current.stock recipient .energy)) := rfl

theorem Seed.every_material_flow {plan : Plan} (seed : Seed plan) (current : AuditCurrent)
    (word : List Action) (actor : Party) (good : Good) :
    (seed.law.next current word).stock actor good+seed.law.totalDebit (seed.law.rawItems current word) actor good =
      current.stock actor good+seed.law.totalCredit (seed.law.rawItems current word) actor good :=
  seed.law.actual_next_material_balance current word actor good

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff
