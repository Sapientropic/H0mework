import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Origins

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def auditCurrent (raw : Current) : Cell.Current := Mandate.eraseCurrent (audit raw)

def auditPayment (amount : ℚ) : Cell.RequestAt := ⟨0,[],.common,[],.settle () 0 2 amount⟩
def auditJoint (raw : Current) (amount : ℚ) : JointAction :=
  liftAudit raw ⟨0,[],native .common,[],.settle () 0 2 amount⟩
def providerPayment (amount : ℚ) : ProviderAction := ⟨1,[],.reserve 1,[],.settle () 1 2 amount⟩

def auditWord (scope : Scope) (raw : Current) : List JointAction :=
  let quantity := raw.claims .audit (.inl 0) (.inl 2)
  if 0<quantity ∧ Cell.law.Valid (auditCurrent raw) (auditPayment quantity) ∧
      (law scope).Valid raw (auditJoint raw quantity) then [auditJoint raw quantity] else []

def providerWord (scope : Scope) (raw : Current) : List JointAction :=
  let quantity := raw.claims .provider (.inr 1) (.inr 2)
  if 0<quantity ∧ providerLaw.Valid (provider raw) (providerPayment quantity) ∧
      (law scope).Valid raw (liftProvider raw (providerPayment quantity)) then
    [liftProvider raw (providerPayment quantity)] else []

inductive Lane where | audit | provider
  deriving DecidableEq

def word (lane : Lane) (scope : Scope) (raw : Current) : List JointAction :=
  match lane with | .audit => auditWord scope raw | .provider => providerWord scope raw

def input (lane : Lane) (scope : Scope) (raw : Current) : Finance.Input :=
  {law:=law scope,initial:=raw,instructions:=[],emission?:=some (word lane scope)}

namespace Runtime
def facade (lane : Lane) (scope : Scope) (raw : Current) := ProgrammeHistory.facade (input lane scope raw)
def activated (lane : Lane) (scope : Scope) (raw : Current) := (facade lane scope raw).seed.advance 1
def execution (lane : Lane) (scope : Scope) (raw : Current) :=
  match (facade lane scope raw).readoutAt (activated lane scope raw) .execution with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible

theorem actual_word_and_after (lane : Lane) (scope : Scope) (raw : Current) :
    (execution lane scope raw).before=(law scope).next raw [] ∧
    (execution lane scope raw).submitted=word lane scope ((law scope).next raw []) ∧
    (execution lane scope raw).after=(law scope).next ((law scope).next raw [])
      (word lane scope ((law scope).next raw [])) := ⟨rfl,rfl,rfl⟩

theorem whole_ledger_and_own_next (lane : Lane) (scope : Scope) (raw : Current) :
    HEq (activated lane scope raw).tick.generated.wholeLedgerWriteBack
      ((activated lane scope raw).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated lane scope raw).current.visit.current) ∧
    (activated lane scope raw).tick.nextCurrent=
      (ProgrammeHistory.process (input lane scope raw)).stateAt
        ((ProgrammeHistory.process (input lane scope raw)).successor (activated lane scope raw).state) := by
  have factor := ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input lane scope raw) 1
  exact ⟨factor.2.2.1,factor.2.2.2.2⟩
end Runtime

/-- The native view reads the submitted operation of this same joint occurrence. -/
def auditView (scope : Scope) (raw : Current) : AuditInput :=
  {law:=Cell.law,initial:=auditCurrent raw,instructions:=
    (Runtime.execution .audit scope raw).submitted.map fun _ =>
      auditPayment ((Runtime.execution .audit scope raw).before.claims .audit (.inl 0) (.inl 2))}

def providerView (scope : Scope) (raw : Current) : ProviderInput :=
  {law:=providerLaw,initial:=provider raw,instructions:=
    (Runtime.execution .provider scope raw).submitted.map fun _ =>
      providerPayment ((Runtime.execution .provider scope raw).before.claims .provider (.inr 1) (.inr 2))}

theorem audit_payment_is_one_actual_restricted_step (scope : Scope) (raw : Current) (quantity : ℚ)
    (joint : (law scope).Valid raw (auditJoint raw quantity))
    (nativePaid : Cell.law.Valid (auditCurrent raw) (auditPayment quantity)) :
    auditCurrent ((law scope).step raw (auditJoint raw quantity))=
      Cell.law.step (auditCurrent raw) (auditPayment quantity) := by
  rw [RawLaw.step,if_pos joint,RawLaw.step,if_pos nativePaid]
  apply RawCurrent.ext
  · funext party good
    simp [auditCurrent,Mandate.eraseCurrent,audit,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,
      auditJoint,liftAudit,liftAuditOperation,auditPayment,law,Supply.law,Cell.law,
      flowAt,locate,amount]
  · funext instrument debtor holder
    cases instrument
    simp [auditCurrent,Mandate.eraseCurrent,audit,RawLaw.paidStep,RawLaw.nextClaims,
      auditJoint,liftAudit,liftAuditOperation,auditPayment]
  all_goals rfl

theorem provider_payment_is_one_actual_restricted_step (scope : Scope) (raw : Current) (quantity : ℚ)
    (joint : (law scope).Valid raw (liftProvider raw (providerPayment quantity)))
    (nativePaid : providerLaw.Valid (provider raw) (providerPayment quantity)) :
    provider ((law scope).step raw (liftProvider raw (providerPayment quantity)))=
      providerLaw.step (provider raw) (providerPayment quantity) := by
  rw [RawLaw.step,if_pos joint,RawLaw.step,if_pos nativePaid]
  apply RawCurrent.ext
  · funext party good
    cases good <;> simp [provider,material,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,
      liftProvider,liftProviderOperation,providerPayment,law,Supply.law,providerLaw,
      Protocol.SymbolicAuthentication.UpstreamProductionLaw.law,
      Protocol.SymbolicAuthentication.WorkerInputLaw.law,
      Protocol.SymbolicAuthentication.FuelMandateLaw.law,
      Protocol.SymbolicAuthentication.FuelMandateLaw.base,
      Protocol.SymbolicAuthentication.RenewedQuorumMaterial.base,Mandate.law,Repayment.Recovery.base,
      flowAt,locate,amount]
  · funext instrument debtor holder
    cases instrument
    simp [provider,RawLaw.paidStep,RawLaw.nextClaims,liftProvider,liftProviderOperation,providerPayment]
  all_goals rfl

theorem audit_empty_projection (scope : Scope) (raw : Current) :
    auditCurrent ((law scope).next raw [])=Cell.law.next (auditCurrent raw) [] := rfl

theorem audit_payment_is_one_actual_restricted_next (scope : Scope) (raw : Current) (quantity : ℚ)
    (joint : (law scope).Valid raw (auditJoint raw quantity))
    (nativePaid : Cell.law.Valid (auditCurrent raw) (auditPayment quantity)) :
    auditCurrent ((law scope).next raw [auditJoint raw quantity])=
      Cell.law.next (auditCurrent raw) [auditPayment quantity] := by
  have actual := audit_payment_is_one_actual_restricted_step scope raw quantity joint nativePaid
  apply RawCurrent.ext
  · have field := congrArg (fun c : Cell.Current => c.stock) actual
    exact field
  · have field := congrArg (fun c : Cell.Current => c.claims) actual
    exact field
  · have field := congrArg (fun c : Cell.Current => c.technology) actual
    exact field
  all_goals rfl

theorem audit_view_has_the_entire_actual_after (scope : Scope) (raw : Current) :
    auditCurrent (Runtime.execution .audit scope raw).after=
      ProgrammeSource.rawCurrent (auditView scope raw)
        (ProgrammeHistory.visitAt (auditView scope raw) 2).current := by
  let before := (law scope).next raw []
  change auditCurrent ((law scope).next before (auditWord scope before))=
    Cell.law.next (Cell.law.next (auditCurrent raw) [])
      ((auditWord scope before).map fun _ => auditPayment (before.claims .audit (.inl 0) (.inl 2)))
  rw [←audit_empty_projection scope raw]
  change auditCurrent ((law scope).next before (auditWord scope before))=
    Cell.law.next (auditCurrent before)
      ((auditWord scope before).map fun _ => auditPayment (before.claims .audit (.inl 0) (.inl 2)))
  dsimp only [auditWord]
  split
  · rename_i accepted
    exact audit_payment_is_one_actual_restricted_next scope before _ accepted.2.2 accepted.2.1
  · exact audit_empty_projection scope before

theorem provider_empty_projection (scope : Scope) (raw : Current)
    (synchronized : raw.technology.roundLag≤(raw.round:ℤ)) :
    provider ((law scope).next raw [])=providerLaw.next (provider raw) [] := by
  apply RawCurrent.ext
  · rfl
  · rfl
  · rfl
  · change raw.clock+1-raw.technology.clockLag=raw.clock-raw.technology.clockLag+1
    ring
  · change (((raw.round+1:Nat):ℤ)-raw.technology.roundLag).toNat=
      ((raw.round:ℤ)-raw.technology.roundLag).toNat+1
    omega

theorem provider_payment_is_one_actual_restricted_next (scope : Scope) (raw : Current) (quantity : ℚ)
    (synchronized : raw.technology.roundLag≤(raw.round:ℤ))
    (joint : (law scope).Valid raw (liftProvider raw (providerPayment quantity)))
    (nativePaid : providerLaw.Valid (provider raw) (providerPayment quantity)) :
    provider ((law scope).next raw [liftProvider raw (providerPayment quantity)])=
      providerLaw.next (provider raw) [providerPayment quantity] := by
  have actual := provider_payment_is_one_actual_restricted_step scope raw quantity joint nativePaid
  apply RawCurrent.ext
  · have field := congrArg (fun c : ProviderCurrent => c.stock) actual
    exact field
  · have field := congrArg (fun c : ProviderCurrent => c.claims) actual
    exact field
  · have field := congrArg (fun c : ProviderCurrent => c.technology) actual
    exact field
  · simp only [RawLaw.next,RawLaw.execute,RawLaw.step,if_pos joint,if_pos nativePaid,RawLaw.paidStep]
    change raw.clock+1-raw.technology.clockLag=raw.clock-raw.technology.clockLag+1
    ring
  · simp only [RawLaw.next,RawLaw.execute,RawLaw.step,if_pos joint,if_pos nativePaid,RawLaw.paidStep]
    change (((raw.round+1:Nat):ℤ)-raw.technology.roundLag).toNat=
      ((raw.round:ℤ)-raw.technology.roundLag).toNat+1
    omega

theorem provider_view_has_the_entire_actual_after (scope : Scope) (raw : Current)
    (synchronized : raw.technology.roundLag≤(raw.round:ℤ)) :
    provider (Runtime.execution .provider scope raw).after=
      ProgrammeSource.rawCurrent (providerView scope raw)
        (ProgrammeHistory.visitAt (providerView scope raw) 2).current := by
  let before := (law scope).next raw []
  change provider ((law scope).next before (providerWord scope before))=
    providerLaw.next (providerLaw.next (provider raw) [])
      ((providerWord scope before).map fun _ => providerPayment (before.claims .provider (.inr 1) (.inr 2)))
  rw [←provider_empty_projection scope raw synchronized]
  change provider ((law scope).next before (providerWord scope before))=
    providerLaw.next (provider before)
      ((providerWord scope before).map fun _ => providerPayment (before.claims .provider (.inr 1) (.inr 2)))
  have clocked : before.technology.roundLag≤(before.round:ℤ) := by
    change raw.technology.roundLag≤((raw.round+1:Nat):ℤ)
    omega
  dsimp only [providerWord]
  split
  · rename_i accepted
    exact provider_payment_is_one_actual_restricted_next scope before _ clocked accepted.2.2 accepted.2.1
  · exact provider_empty_projection scope before clocked

/-- The original package is immutable lineage, while all current accounts follow actual payments. -/
structure State where
  origin : Synthesis.State
  raw : Current
  delivery : Finance.Account
  auditAccount : AuditAccount
  providerAccount : ProviderAccount
  task : PublicTaskSpec Actor Good
  taskId : Nat
  completed : List Nat
  inputs : List Finance.Input

def start (state : Synthesis.State) : State :=
  ⟨state,state.raw,state.account,auditGenesis,providerGenesis,
   state.task,state.taskId,state.completed,state.inputs⟩

def next (lane : Lane) (state : State) : State :=
  let occurrence := input lane state.origin.scope state.raw
  ⟨state.origin,(Runtime.execution lane state.origin.scope state.raw).after,
   Financial.Family.continueVisits Finance.sources occurrence 0 2 state.delivery,
   match lane with
     | .audit => Financial.Family.continueVisits auditSources (auditView state.origin.scope state.raw) 0 2 state.auditAccount
     | .provider => state.auditAccount,
   match lane with
     | .audit => state.providerAccount
     | .provider => Financial.Family.continueVisits providerSources (providerView state.origin.scope state.raw) 0 2 state.providerAccount,
   state.task,state.taskId,state.completed,state.inputs++[occurrence]⟩

theorem actual_after_is_the_next_input (lane following : Lane) (state : State) :
    (input following (next lane state).origin.scope (next lane state).raw).initial=
      (Runtime.execution lane state.origin.scope state.raw).after := rfl

theorem original_carrier_and_pending_window_survive (lane : Lane) (state : State) :
    (next lane state).origin=state.origin ∧ (next lane state).task=state.task ∧
    (next lane state).taskId=state.taskId ∧ (next lane state).completed=state.completed := ⟨rfl,rfl,rfl,rfl⟩

def auditRun (state : State) :=
  Financial.Family.continueVisits_run auditSources (auditView state.origin.scope state.raw) 0 2 state.auditAccount

def providerRun (state : State) :=
  Financial.Family.continueVisits_run providerSources (providerView state.origin.scope state.raw) 0 2 state.providerAccount

theorem original_audit_claims_survive (lane : Lane) (state : State) :
    state.auditAccount.current.slots.map (Financial.Family.slotClaim auditSources) <+:
      (next lane state).auditAccount.current.slots.map (Financial.Family.slotClaim auditSources) := by
  cases lane
  · exact Financial.Family.continueVisits_preserves_original_claims _ _ _ _ _
  · exact List.prefix_rfl

theorem original_provider_claims_survive (lane : Lane) (state : State) :
    state.providerAccount.current.slots.map (Financial.Family.slotClaim providerSources) <+:
      (next lane state).providerAccount.current.slots.map (Financial.Family.slotClaim providerSources) := by
  cases lane
  · exact List.prefix_rfl
  · exact Financial.Family.continueVisits_preserves_original_claims _ _ _ _ _

def auditMigrate (state : State) (index : Nat)
    (slot : ResponsibilityLifecycle.ObligationSlot (Financial.Family.vocabulary auditSources))
    (present : state.auditAccount.current.slots[index]?=some slot) :=
  Financial.Family.Migration.follow auditSources (auditRun state) index slot present

def providerMigrate (state : State) (index : Nat)
    (slot : ResponsibilityLifecycle.ObligationSlot (Financial.Family.vocabulary providerSources))
    (present : state.providerAccount.current.slots[index]?=some slot) :=
  Financial.Family.Migration.follow providerSources (providerRun state) index slot present

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement
