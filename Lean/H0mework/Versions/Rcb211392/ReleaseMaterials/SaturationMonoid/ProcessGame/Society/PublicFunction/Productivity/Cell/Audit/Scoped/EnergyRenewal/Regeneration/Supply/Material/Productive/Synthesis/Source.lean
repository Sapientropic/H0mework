import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Scan

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Need where
  slots : List (ServiceSlot Actor Good)
  positive : ∃ slot ∈ slots,∃ entry ∈ slot.goods,0<entry.2
  window : ℚ

def Need.openTask (need : Need) (current : Current) : PublicTaskSpec Actor Good :=
  ⟨need.slots,current.clock,current.clock+need.window,need.positive⟩

structure Code where
  need : Need
  alphabet : List JointAction
  budget : Nat
  charge : Charge
  historical : ∀ action ∈ alphabet,Historical action

abbrev OriginalAt (raw : Current) (account : Finance.Account) (scope : Scope) :=
  Σ plan : EnergyRenewal.Plan,{original : Finance.State plan //
    original.session.current=raw ∧ original.account=account ∧ original.session.window.scope=scope}

structure State where
  raw : Current
  account : Finance.Account
  scope : Scope
  task : PublicTaskSpec Actor Good
  taskId : Nat
  completed : List Nat
  original : Option (OriginalAt raw account scope)
  inputs : List Finance.Input

def start {plan : EnergyRenewal.Plan} (code : Code) (original : Finance.State plan) : State :=
  ⟨original.session.current,original.account,original.session.window.scope,
   code.need.openTask original.session.current,0,[],some ⟨plan,original,rfl,rfl,rfl⟩,[]⟩

theorem start_preserves_the_entire_original_carrier {plan : EnergyRenewal.Plan}
    (code : Code) (original : Finance.State plan) :
    (start code original).raw=original.session.current ∧
    (start code original).account=original.account ∧
    (start code original).original=some ⟨plan,original,rfl,rfl,rfl⟩ := ⟨rfl,rfl,rfl⟩

def input (code : Code) (state : State) : Finance.Input :=
  {law:=law state.scope,initial:=state.raw,instructions:=[],
   emission?:=some fun current => (generate state.scope state.task code.alphabet code.budget code.charge current).word,
   localAttempts:=fun _ => code.alphabet}

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
def facade (code : Code) (state : State) := ProgrammeHistory.facade (input code state)
def activated (code : Code) (state : State) := (facade code state).seed.advance 1
def execution (code : Code) (state : State) :=
  match (facade code state).readoutAt (activated code state) .execution with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible

def prepared (_code : Code) (state : State) := (law state.scope).next state.raw []
def scan (code : Code) (state : State) :=
  generate state.scope state.task code.alphabet code.budget code.charge (prepared code state)

theorem actual_generated_word_and_after (code : Code) (state : State) :
    (execution code state).before=prepared code state ∧
    (execution code state).submitted=(scan code state).word ∧
    (execution code state).after=(law state.scope).next (prepared code state) (scan code state).word := by
  exact ⟨rfl,rfl,rfl⟩

theorem same_root_whole_ledger_and_own_next (code : Code) (state : State) :
    HEq ((facade code state).readoutAt (activated code state) .execution)
      ((activated code state).tick.generated.projectionOutcome .execution) ∧
    HEq (activated code state).tick.generated.wholeLedgerWriteBack
      ((activated code state).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated code state).current.visit.current) ∧
    (activated code state).tick.nextCurrent=
      (ProgrammeHistory.process (input code state)).stateAt
        ((ProgrammeHistory.process (input code state)).successor (activated code state).state) := by
  have factor := ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input code state) 1
  exact ⟨factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

def account (code : Code) (state : State) :=
  Financial.Family.continueVisits Finance.sources (input code state) 0 2 state.account
end Runtime

theorem Runtime.old_instruments_keep_their_full_matrix (code : Code) (state : State)
    (instrument : Instrument) (old : instrument≠.delivery) :
    (Runtime.execution code state).after.claims instrument=state.raw.claims instrument := by
  have safe := (Runtime.scan code state).word_preserves_old_instruments code.historical
  have iterate (actions : List JointAction) (current : Current) (index : Nat)
      (safe : ∀ action ∈ actions,Historical action) :
      ((law state.scope).execute current index actions).final.claims instrument=current.claims instrument := by
    induction actions generalizing current index with
    | nil => rfl
    | cons head rest ih =>
      change ((law state.scope).execute ((law state.scope).step current head) (index+1) rest).final.claims instrument=_
      rw [ih _ _ (fun a h => safe a (List.mem_cons_of_mem _ h)),
        steps_keep_old_claims _ _ _ (safe head (by simp)) instrument old]
  exact iterate _ _ 0 safe


open private Supply.Session.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open private Finance.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance

def continueOriginal (code : Code) (state : State) :
    Option (OriginalAt (Runtime.execution code state).after (Runtime.account code state) state.scope) :=
  state.original.map fun ⟨plan,package⟩ =>
    let old := package.val.session
    let after := (Runtime.execution code state).after
    let session : Session plan := Supply.Session.mk old.origin old.received old.window after old.target
      (old.history++[⟨input code state,1⟩]) (by
        calc
          (audit after).claims=(audit state.raw).claims := by
            funext i p q
            exact congrFun (congrFun (Runtime.old_instruments_keep_their_full_matrix code state .audit (by decide)) (.inl p)) (.inl q)
          _=(audit old.current).claims := by rw [package.property.1]
          _=_ := old.finance) (by
        calc
          (provider after).claims=(provider state.raw).claims := by
            funext i p q
            exact congrFun (congrFun (Runtime.old_instruments_keep_their_full_matrix code state .provider (by decide)) (.inr p)) (.inr q)
          _=(provider old.current).claims := by rw [package.property.1]
          _=_ := old.providerFinance)
    ⟨plan,Finance.State.mk session (Runtime.account code state),rfl,rfl,package.property.2.2⟩

def next (code : Code) (state : State) : State :=
  let after := (Runtime.execution code state).after
  let success := (Runtime.scan code state).succeeded
  ⟨after,Runtime.account code state,state.scope,
   if success then code.need.openTask after else state.task,
   if success then state.taskId+1 else state.taskId,
   if success then state.completed++[state.taskId] else state.completed,
   continueOriginal code state,state.inputs++[input code state]⟩

theorem original_package_is_continued_in_its_own_session (code : Code) (state : State)
    {plan : EnergyRenewal.Plan} (original : Finance.State plan)
    (raw : original.session.current=state.raw) (account : original.account=state.account)
    (scope : original.session.window.scope=state.scope)
    (present : state.original=some ⟨plan,original,raw,account,scope⟩) :
    ∃ updated : Finance.State plan,∃ rawEq : updated.session.current=(next code state).raw,
      ∃ accountEq : updated.account=(next code state).account,
      ∃ scopeEq : updated.session.window.scope=(next code state).scope,
      (next code state).original=some ⟨plan,updated,rawEq,accountEq,scopeEq⟩ ∧
      updated.session.origin=original.session.origin ∧ updated.session.received=original.session.received ∧
      updated.session.window=original.session.window ∧ updated.session.target=original.session.target ∧
      updated.session.history=original.session.history++[⟨input code state,1⟩] := by
  unfold next continueOriginal
  rw [present]
  refine ⟨_,?_,?_,?_,rfl,?_,?_,?_,?_,?_⟩
  all_goals first | rfl | exact scope

theorem actual_service_is_paid (code : Code) (state : State)
    (success : (Runtime.scan code state).succeeded=true) (slot : ServiceSlot Actor Good)
    (inside : slot ∈ state.task.slots) :
    Institutions.Capitalism.Universal.Exit.Necessity.BundlePaid (law state.scope)
      (Runtime.execution code state).before (Runtime.execution code state).submitted
      slot.bearer slot.goods slot.purpose :=
  (Runtime.scan code state).success_pays_new_service success slot inside

theorem actual_service_keeps_its_window (code : Code) (state : State)
    (success : (Runtime.scan code state).succeeded=true) :
    state.task.earliest≤(Runtime.execution code state).before.clock ∧
    (Runtime.execution code state).after.clock≤state.task.deadline :=
  (Runtime.scan code state).success_keeps_the_original_window success

theorem failed_task_keeps_its_original_window (code : Code) (state : State)
    (failed : (Runtime.scan code state).succeeded=false) :
    (next code state).task=state.task ∧ (next code state).taskId=state.taskId ∧
    (next code state).completed=state.completed := by
  simp [next,failed]

theorem next_request_uses_the_actual_after (code : Code) (state : State) :
    (input code (next code state)).initial=(Runtime.execution code state).after := rfl

theorem every_original_financial_admission_survives (code : Code) (state : State) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (next code state).account.current.slots.map (Financial.Family.slotClaim Finance.sources) :=
  (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _).trans
    (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _)

def transition (code : Code) (state : State) :
    (Financial.Family.process Finance.sources).Run state.account.current (next code state).account.current :=
  (Financial.Family.visitRun Finance.sources (input code state) 0 state.account).concatRuns _
    (Financial.Family.visitRun Finance.sources (input code state) 1
      (Financial.Family.consumeVisit Finance.sources (input code state) 0 state.account))

def run (code : Code) (initial : State) : Nat → State
  | 0 => initial
  | count+1 => next code (run code initial count)

theorem recursive_after_and_old_origins (code : Code) (initial : State) (count : Nat) :
    (run code initial (count+1)).raw=(Runtime.execution code (run code initial count)).after ∧
    initial.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (run code initial count).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  refine ⟨rfl,?_⟩
  induction count with
  | zero => exact List.prefix_rfl
  | succ n ih => exact ih.trans (every_original_financial_admission_survives code _)

theorem original_package_survives_every_actual_successor (code : Code)
    {plan : EnergyRenewal.Plan} (original : Finance.State plan) (count : Nat) :
    let state := run code (start code original) count
    ∃ updated : Finance.State plan,∃ rawEq : updated.session.current=state.raw,
      ∃ accountEq : updated.account=state.account,∃ scopeEq : updated.session.window.scope=state.scope,
      state.original=some ⟨plan,updated,rawEq,accountEq,scopeEq⟩ ∧
      updated.session.origin=original.session.origin ∧ updated.session.received=original.session.received ∧
      updated.session.window=original.session.window ∧ updated.session.target=original.session.target ∧
      updated.session.history.length=original.session.history.length+count := by
  induction count with
  | zero => exact ⟨original,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,by simp⟩
  | succ n ih =>
    obtain ⟨old,raw,account,scope,present,origin,received,window,target,history⟩ := ih
    obtain ⟨updated,newRaw,newAccount,newScope,newPresent,newOrigin,newReceived,newWindow,newTarget,newHistory⟩ :=
      original_package_is_continued_in_its_own_session code _ old raw account scope present
    exact ⟨updated,newRaw,newAccount,newScope,newPresent,newOrigin.trans origin,newReceived.trans received,
      newWindow.trans window,newTarget.trans target,by simp [newHistory,history,Nat.add_assoc]⟩
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis
