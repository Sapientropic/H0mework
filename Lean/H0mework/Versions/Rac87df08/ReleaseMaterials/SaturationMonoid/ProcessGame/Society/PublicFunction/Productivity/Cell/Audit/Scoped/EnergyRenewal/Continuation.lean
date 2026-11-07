import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Command where
  | read | repair | revoke | openWindow | grant
  deriving DecidableEq
structure Request where
  command : Command
  query : Query

/-- Only the original sealed seed and paid successor factory construct windows. -/
structure Window (plan : Plan) where
  private mk ::
  origin : Runtime.EpochSeed plan
  task : PublicTaskSpec Party Good
  slots : task.slots = energySlots
  initial : AuditCurrent
  finance : initial.claims = (before plan).claims
  ancestry : List (ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit × Nat)

def first {plan : Plan} (seed : Runtime.EpochSeed plan) (queries : Nat → Query) (ordinal : Nat) : Window plan :=
  ⟨seed,seed.ready.task,rfl,seed.ready.epochCurrent queries (ordinal+1),
    seed.ready.epoch_preserves_claims queries (ordinal+1),[(seed.ready.epochInput queries,ordinal)]⟩

theorem first_is_actual_generated_next {plan : Plan} (seed : Runtime.EpochSeed plan)
    (queries : Nat → Query) (ordinal : Nat) :
    (first seed queries ordinal).initial = ProgrammeSource.rawCurrent (seed.ready.epochInput queries)
      (ProgrammeHistory.visitAt (seed.ready.epochInput queries) (ordinal+1)).current := by
  rw [seed.ready.epoch_is_own_root_current]; rfl

def Window.scope {plan : Plan} (window : Window plan) : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort) :=
  ⟨window.task,native .machine,native .revision,by decide,[(.energy,1)]⟩

def Window.law {plan : Plan} (window : Window plan) := Mandate.law energyBase window.scope
def Window.readWord {plan : Plan} (window : Window plan) (current : AuditCurrent) (query : Query) :=
  attempt window.law current [fun _ => accessRequest plan.candidate query,fun _ => deliveryFee]

def Window.word {plan : Plan} (window : Window plan) (request : Request) (current : AuditCurrent) : List Action :=
  match request.command with
  | .read => window.readWord current request.query
  | .grant => attempt window.law current
      [fun state => Mandate.request window.scope state 0 (.propose plan.candidate),
       fun state => Mandate.request window.scope state plan.candidate .accept,
       fun _ => accessRequest plan.candidate request.query,fun _ => deliveryFee]
  | .repair =>
      let refused := window.readWord current request.query
      if ¬ window.law.Valid current (accessRequest plan.candidate request.query) ∧
          current.technology.holder = some plan.candidate ∧
          window.scope.task.earliest ≤ current.clock ∧ current.clock ≤ window.scope.task.deadline then
        refused ++ attempt window.law (window.law.execute current 0 refused).final
          [fun _ => transfer plan.candidate 3,fun _ => accessRequest plan.candidate request.query,fun _ => deliveryFee]
      else refused
  | .revoke =>
      let action := Mandate.request window.scope current 0 .revoke
      [action] ++ window.readWord (window.law.step current action) request.query
  | .openWindow =>
      if Quiet current ∧ window.scope.task.deadline < current.clock then
        attempt window.law current [fun _ => applicationFee]
      else []

def Window.requestAt {plan : Plan} (_window : Window plan) (requests : List Request) (ordinal : Nat) : Request :=
  (requests[ordinal-1]?).getD ⟨.read,defaultQuery ordinal⟩
def Window.emit {plan : Plan} (window : Window plan) (requests : List Request) (current : AuditCurrent) :=
  window.word (window.requestAt requests (current.round-window.initial.round)) current
def Window.input {plan : Plan} (window : Window plan) (requests : List Request) :
    ProgrammeSource.Input Party Good AuditPort (Mandate.State Party Technology) Unit :=
  { law := window.law, initial := window.initial, instructions := [], emission? := some (window.emit requests) }
def Window.current {plan : Plan} (window : Window plan) (requests : List Request) : Nat → AuditCurrent :=
  Nat.rec window.initial (fun n current => window.law.next current (if n = 0 then [] else window.emit requests current))
theorem Window.current_succ {plan : Plan} (window : Window plan) (requests : List Request) (n : Nat) :
    window.current requests (n+1) = window.law.next (window.current requests n)
      (if n = 0 then [] else window.emit requests (window.current requests n)) := rfl
attribute [irreducible] Window.current

theorem Window.current_is_own_root_current {plan : Plan} (window : Window plan) (requests : List Request) (n : Nat) :
    ProgrammeSource.rawCurrent (window.input requests) (ProgrammeHistory.visitAt (window.input requests) n).current =
      window.current requests n := by
  induction n with
  | zero => unfold Window.current; rfl
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

theorem Window.current_round {plan : Plan} (window : Window plan) (requests : List Request) (n : Nat) :
    (window.current requests n).round = window.initial.round+n := by
  induction n with
  | zero => unfold Window.current; rfl
  | succ n ih => rw [window.current_succ]; change _+1 = _; rw [ih]; omega

theorem Window.emission_uses_exact_request {plan : Plan} (window : Window plan) (requests : List Request) (n : Nat) :
    window.emit requests (window.current requests n) = window.word (window.requestAt requests n) (window.current requests n) := by
  unfold Window.emit
  rw [window.current_round]
  simp

theorem Window.word_silent {plan : Plan} (window : Window plan) (request : Request) (current : AuditCurrent) :
    ∀ action ∈ window.word request current,Silent action := by
  have reads : ∀ state,∀ action ∈ window.readWord state request.query,Silent action := by
    intro state
    apply attempt_silent
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member state
    rcases member with rfl | rfl <;> trivial
  cases command : request.command <;> simp only [Window.word,command]
  · exact reads current
  · split
    · intro action member
      rcases List.mem_append.mp member with member | member
      · exact reads current action member
      · apply attempt_silent _ _ _ ?_ action member
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        intro stage member state
        rcases member with rfl | rfl | rfl <;> trivial
    · exact reads current
  · intro action member
    rcases List.mem_append.mp member with member | member
    · have same := List.mem_singleton.mp member
      subst action
      trivial
    · exact reads _ action member
  · split
    · apply attempt_silent
      simp only [List.mem_singleton]
      intro stage member state
      subst stage
      trivial
    · simp
  · apply attempt_silent
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    intro stage member state
    rcases member with rfl | rfl | rfl | rfl <;> trivial

theorem Window.preserves_every_claim {plan : Plan} (window : Window plan) (requests : List Request) (n : Nat) :
    (window.current requests n).claims = (before plan).claims := by
  induction n with
  | zero => unfold Window.current; exact window.finance
  | succ n ih =>
    rw [window.current_succ]
    trans (window.current requests n).claims
    · apply silent_claims
      split
      · simp
      · exact window.word_silent _ _
    · exact ih

def Window.openPaid {plan : Plan} (window : Window plan) (requests : List Request) (ordinal : Nat) : Prop :=
  0 < ordinal ∧ (window.requestAt requests ordinal).command = .openWindow ∧
    Quiet (window.current requests ordinal) ∧ window.scope.task.deadline < (window.current requests ordinal).clock ∧
    window.law.Valid (window.current requests ordinal) applicationFee
instance {plan : Plan} (window : Window plan) (requests : List Request) (ordinal : Nat) :
    Decidable (window.openPaid requests ordinal) := by unfold Window.openPaid; infer_instance

/-- A premature, active or unfunded opening cannot construct a successor. -/
def Window.nextWindow {plan : Plan} (window : Window plan) (requests : List Request) (ordinal : Nat) : Option (Window plan) :=
  if window.openPaid requests ordinal then
    let after := window.current requests (ordinal+1)
    let task : PublicTaskSpec Party Good := ⟨energySlots,after.clock+1,after.clock+1+energySlots.length,by decide +kernel⟩
    some ⟨window.origin,task,rfl,after,
      window.preserves_every_claim requests (ordinal+1),window.ancestry++[(window.input requests,ordinal)]⟩
  else none

theorem Window.renewal_has_exact_next {plan : Plan} (window : Window plan) (requests : List Request)
    (ordinal : Nat) (next : Window plan) (generated : window.nextWindow requests ordinal = some next) :
    next.initial = ProgrammeSource.rawCurrent (window.input requests)
      (ProgrammeHistory.visitAt (window.input requests) (ordinal+1)).current ∧
    next.scope.task.earliest = next.initial.clock+1 ∧
    window.scope.task.deadline < next.scope.task.earliest := by
  unfold Window.nextWindow at generated
  split at generated
  · cases Option.some.inj generated
    rw [window.current_is_own_root_current]
    refine ⟨rfl,rfl,?_⟩
    have expired := (by assumption : window.openPaid requests ordinal).2.2.2.1
    change window.scope.task.deadline < (window.current requests (ordinal+1)).clock+1
    rw [window.current_succ]
    change window.scope.task.deadline < (window.current requests ordinal).clock+1+1
    linarith
  · cases generated

theorem Window.opening_is_actual_paid_application {plan : Plan} (window : Window plan) (requests : List Request)
    (ordinal : Nat) (next : Window plan) (generated : window.nextWindow requests ordinal = some next) :
    window.emit requests (window.current requests ordinal) = [applicationFee] ∧
    window.law.Valid (window.current requests ordinal) applicationFee := by
  have paid : window.openPaid requests ordinal := by
    unfold Window.nextWindow at generated
    split at generated
    · assumption
    · cases generated
  rw [window.emission_uses_exact_request]
  have allowed : Quiet (window.current requests ordinal) ∧
      window.scope.task.deadline < (window.current requests ordinal).clock := ⟨paid.2.2.1,paid.2.2.2.1⟩
  constructor
  · simp [Window.word,paid.2.1,allowed,attempt,paid.2.2.2.2]
  · exact paid.2.2.2.2

theorem Window.failed_open_has_typed_reason {plan : Plan} (window : Window plan) (requests : List Request)
    (ordinal : Nat) (absent : window.nextWindow requests ordinal = none) :
    ordinal = 0 ∨ (window.requestAt requests ordinal).command ≠ .openWindow ∨
      ¬ Quiet (window.current requests ordinal) ∨
      ¬ window.scope.task.deadline < (window.current requests ordinal).clock ∨
      ¬ window.law.Valid (window.current requests ordinal) applicationFee := by
  unfold Window.nextWindow at absent
  split at absent
  · cases absent
  · simp only [Window.openPaid,not_and_or,not_lt,nonpos_iff_eq_zero] at *
    assumption

theorem Window.every_material_flow {plan : Plan} (window : Window plan) (current : AuditCurrent)
    (word : List Action) (actor : Party) (good : Good) :
    (window.law.next current word).stock actor good+window.law.totalDebit (window.law.rawItems current word) actor good =
      current.stock actor good+window.law.totalCredit (window.law.rawItems current word) actor good :=
  window.law.actual_next_material_balance current word actor good

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Continuation
