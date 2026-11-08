import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Requests

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

inductive Debt (basis : State) where
  | inherited
  | requested (window : Requests.Window basis)
def Debt.task {basis : State} : Debt basis → PublicTaskSpec Actor Good
  | .inherited => basis.task
  | .requested window => window.task
def Debt.id {basis : State} : Debt basis → Nat
  | .inherited => basis.taskId
  | .requested window => window.id

/-- Expiry is an outstanding responsibility, never a fulfilled or waived receipt. -/
structure PastDue (basis : State) where
  private mk ::
  debt : Debt basis
  observed : Current
  ordinal : Nat
  expired : debt.task.deadline<observed.clock

def search (basis : State) (window : Requests.Window basis) (before : Current) :=
  generate basis.origin.scope window.task Production.code.alphabet Production.code.budget providerCharge before

structure Completion (basis : State) where
  private mk ::
  window : Requests.Window basis
  before : Current
  paid : (search basis window before).succeeded=true

inductive Event where
  | bootstrap | idle | refusedRequest | admitted | waiting | pastDue | served | refusedService
  deriving DecidableEq

structure Protocol (basis : State) where
  received : Nat
  pending : Option (Requests.Window basis)
  expired : List (PastDue basis)
  completed : List (Completion basis)
  event : Event

structure Frame (basis : State) where
  raw : Current
  protocol : Protocol basis

def initial (basis : State) : Frame basis :=
  ⟨basis.raw,⟨0,none,
    if late : basis.task.deadline<basis.raw.clock then [⟨.inherited,basis.raw,0,late⟩] else [],
    [],.idle⟩⟩

def word (basis : State) (requests : Requests.Source) (ordinal : Nat) (frame : Frame basis) : List JointAction :=
  if ordinal=0 then [] else
    match frame.protocol.pending with
    | some window =>
      if frame.raw.clock<window.task.earliest ∨ window.task.deadline<frame.raw.clock then []
      else (search basis window frame.raw).word
    | none => match requests frame.protocol.received frame.raw.round with
      | none => []
      | some submission => Requests.word basis basis.origin.scope frame.raw submission

def update (basis : State) (requests : Requests.Source) (ordinal : Nat) (frame : Frame basis) : Protocol basis :=
  let prior := frame.protocol
  if ordinal=0 then {prior with event:=.bootstrap} else
    match prior.pending with
    | some window =>
      if late : window.task.deadline<frame.raw.clock then
        ⟨prior.received,none,prior.expired++[⟨.requested window,frame.raw,ordinal,late⟩],prior.completed,.pastDue⟩
      else if frame.raw.clock<window.task.earliest then {prior with event:=.waiting}
      else if paid : (search basis window frame.raw).succeeded then
        ⟨prior.received,none,prior.expired,prior.completed++[⟨window,frame.raw,paid⟩],.served⟩
      else {prior with event:=.refusedService}
    | none => match requests prior.received frame.raw.round with
      | none => {prior with event:=.idle}
      | some submission =>
        let actions := word basis requests ordinal frame
        match Requests.receipt? basis basis.origin.scope frame.raw submission actions with
        | none => {prior with received:=prior.received+1,event:=.refusedRequest}
        | some receipt =>
          ⟨prior.received+1,some (Requests.openWindow basis prior.received frame.raw submission actions receipt),
           prior.expired,prior.completed,.admitted⟩

def step (basis : State) (requests : Requests.Source) (ordinal : Nat) (frame : Frame basis) : Frame basis :=
  ⟨(law basis.origin.scope).next frame.raw (word basis requests ordinal frame),update basis requests ordinal frame⟩

def run (basis : State) (requests : Requests.Source) : Nat → Frame basis
  | 0 => initial basis
  | ordinal+1 => step basis requests ordinal (run basis requests ordinal)

theorem run_round (basis : State) (requests : Requests.Source) (ordinal : Nat) :
    (run basis requests ordinal).raw.round=basis.raw.round+ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => change (run basis requests ordinal).raw.round+1=_;rw [ih];omega

def input (basis : State) (requests : Requests.Source) : Finance.Input :=
  {law:=law basis.origin.scope,initial:=basis.raw,instructions:=[],
   emission?:=some fun current =>
     let ordinal := current.round-basis.raw.round
     word basis requests ordinal (run basis requests ordinal)}

theorem own_current (basis : State) (requests : Requests.Source) (ordinal : Nat) :
    ProgrammeSource.rawCurrent (input basis requests) (ProgrammeHistory.visitAt (input basis requests) ordinal).current=
      (run basis requests ordinal).raw := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih =>
    change ProgrammeSource.rawCurrent (input basis requests)
      (ProgrammeSource.next (input basis requests) (ProgrammeHistory.visitAt (input basis requests) ordinal).current)=_
    rw [ProgrammeSource.actual_raw_next,ih]
    change (law basis.origin.scope).next (run basis requests ordinal).raw _=_
    cases ordinal with
    | zero => rfl
    | succ ordinal =>
      congr 1
      have emitted : ProgrammeSource.rawEvent (input basis requests)
          (ProgrammeHistory.visitAt (input basis requests) (ordinal+1)).current=
          ProgrammeSource.wordAt (input basis requests)
            (ProgrammeSource.rawCurrent (input basis requests)
              (ProgrammeHistory.visitAt (input basis requests) (ordinal+1)).current) := by
        change ProgrammeSource.rawEvent (input basis requests)
          (ProgrammeSource.next (input basis requests) (ProgrammeHistory.visitAt (input basis requests) ordinal).current)=
          ProgrammeSource.wordAt (input basis requests)
            (ProgrammeSource.rawCurrent (input basis requests)
              (ProgrammeSource.next (input basis requests) (ProgrammeHistory.visitAt (input basis requests) ordinal).current))
        generalize (ProgrammeHistory.visitAt (input basis requests) ordinal).current=previous
        cases previous <;> rfl
      rw [emitted,ih]
      change word basis requests ((run basis requests (ordinal+1)).raw.round-basis.raw.round)
          (run basis requests ((run basis requests (ordinal+1)).raw.round-basis.raw.round))=_
      rw [run_round]
      simp

theorem completion_pays_its_own_window {basis : State} (completion : Completion basis)
    (slot : ServiceSlot Actor Good) (inside : slot∈completion.window.task.slots) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law basis.origin.scope)
      completion.before (search basis completion.window completion.before).word slot.bearer slot.goods slot.purpose :=
  (search basis completion.window completion.before).success_pays_new_service completion.paid slot inside

theorem completion_keeps_its_own_deadline {basis : State} (completion : Completion basis) :
    completion.window.task.earliest≤completion.before.clock ∧
    ((law basis.origin.scope).next completion.before (search basis completion.window completion.before).word).clock≤
      completion.window.task.deadline :=
  (search basis completion.window completion.before).success_keeps_the_original_window completion.paid

theorem new_service_cannot_settle_the_inherited_task {basis : State} (completion : Completion basis) :
    basis.taskId<completion.window.id := completion.window.newIdentity

theorem due_responsibilities_are_never_dropped (basis : State) (requests : Requests.Source)
    (ordinal : Nat) (frame : Frame basis) :
    frame.protocol.expired <+: (update basis requests ordinal frame).expired := by
  dsimp only [update]
  split
  · exact List.prefix_rfl
  · split
    · split
      · exact List.prefix_append _ _
      · split
        · exact List.prefix_rfl
        · split <;> exact List.prefix_rfl
    · split
      · exact List.prefix_rfl
      · split <;> exact List.prefix_rfl

theorem every_future_prefix_preserves_all_due_responsibilities (basis : State)
    (requests : Requests.Source) (ordinal : Nat) :
    (initial basis).protocol.expired <+: (run basis requests ordinal).protocol.expired := by
  induction ordinal with
  | zero => exact List.prefix_rfl
  | succ n ih => exact ih.trans (due_responsibilities_are_never_dropped basis requests n _)

theorem every_submitted_action_keeps_old_claims (basis : State) (requests : Requests.Source)
    (ordinal : Nat) (frame : Frame basis) :
    ∀ action∈word basis requests ordinal frame,Historical action := by
  dsimp only [word]
  split
  · simp
  · split
    · split
      · simp
      · exact (search basis _ frame.raw).word_preserves_old_instruments Production.code.historical
    · split
      · simp
      · exact Requests.request_word_preserves_old_instruments _ _ _ _

private theorem safe_execution (scope : Scope) (before : Current) (actions : List JointAction) (index : Nat)
    (safe : ∀ action∈actions,Historical action) (instrument : Instrument) (old : instrument≠.delivery) :
    ((law scope).execute before index actions).final.claims instrument=before.claims instrument := by
  induction actions generalizing before index with
  | nil => rfl
  | cons action rest ih =>
    change ((law scope).execute ((law scope).step before action) (index+1) rest).final.claims instrument=_
    rw [ih _ _ (fun a member => safe a (List.mem_cons_of_mem _ member)),
      Productive.steps_keep_old_claims _ _ action (safe action List.mem_cons_self) instrument old]

theorem all_future_prefixes_keep_actual_old_financial_positions (basis : State) (requests : Requests.Source)
    (ordinal : Nat) (instrument : Instrument) (old : instrument≠.delivery) :
    (run basis requests ordinal).raw.claims instrument=basis.raw.claims instrument := by
  induction ordinal with
  | zero => rfl
  | succ n ih =>
    exact (safe_execution _ _ _ 0 (every_submitted_action_keeps_old_claims basis requests n _)
      instrument old).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream
