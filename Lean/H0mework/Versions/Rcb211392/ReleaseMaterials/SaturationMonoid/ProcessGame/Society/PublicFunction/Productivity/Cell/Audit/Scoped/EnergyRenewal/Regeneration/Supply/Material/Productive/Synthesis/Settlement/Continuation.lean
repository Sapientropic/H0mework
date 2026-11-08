import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Root

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Root
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- The physical producer continues from the paid raw state, not from the archived package's stock. -/
def productionInput (state : State) : Finance.Input :=
  {law:=law state.origin.scope,initial:=state.raw,instructions:=[],
   emission?:=some (Productive.word state.origin.scope .normal)}

namespace Runtime
def productionFacade (state : State) := ProgrammeHistory.facade (productionInput state)
def productionActivated (state : State) := (productionFacade state).seed.advance 1
def productionExecution (state : State) :=
  match (productionFacade state).readoutAt (productionActivated state) .execution with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible
end Runtime

def replenish (state : State) : State :=
  if 2≤state.raw.stock supplier .labor then state
  else ⟨state.origin,(Runtime.productionExecution state).after,
    Financial.Family.continueVisits Finance.sources (productionInput state) 0 2 state.delivery,
    state.auditAccount,state.providerAccount,state.task,state.taskId,state.completed,
    state.inputs++[productionInput state]⟩

/-- The interpreter face uses the live accounts; the full original carrier remains in `State.origin`. -/
def serviceState (state : State) : Synthesis.State :=
  ⟨state.raw,state.delivery,state.origin.scope,state.task,state.taskId,state.completed,none,state.inputs⟩

def advance (state : State) : State :=
  let funded := replenish state
  let result := Synthesis.next Production.code (serviceState funded)
  ⟨state.origin,result.raw,result.account,state.auditAccount,state.providerAccount,
   result.task,result.taskId,result.completed,result.inputs⟩

def run (initial : State) : Nat → State
  | 0 => initial
  | count+1 => advance (run initial count)

theorem reentry_uses_the_paid_inventory (state : State) :
    (productionInput state).initial=state.raw ∧ (serviceState state).raw=state.raw := ⟨rfl,rfl⟩

theorem every_successor_keeps_all_original_native_accounts (state : State) :
    (advance state).origin=state.origin ∧
    (advance state).auditAccount=state.auditAccount ∧
    (advance state).providerAccount=state.providerAccount := ⟨rfl,rfl,rfl⟩

theorem all_future_prefixes_keep_the_original_admissions_and_paid_archives (state : State) (count : Nat) :
    (run state count).origin=state.origin ∧
    (run state count).auditAccount=state.auditAccount ∧
    (run state count).providerAccount=state.providerAccount := by
  induction count with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ count ih => exact ih

theorem funding_never_refreshes_the_pending_window (state : State) :
    (replenish state).task=state.task ∧ (replenish state).taskId=state.taskId ∧
    (replenish state).completed=state.completed := by
  unfold replenish
  split <;> exact ⟨rfl,rfl,rfl⟩

theorem actual_own_service_after (state : State) :
    (advance state).raw=(Synthesis.Runtime.execution Production.code (serviceState (replenish state))).after := rfl

private theorem safe_word_claims (scope : Scope) (raw : Current) (actions : List JointAction)
    (index : Nat) (safe : ∀ action ∈ actions,Historical action) (instrument : Instrument)
    (old : instrument≠.delivery) :
    ((law scope).execute raw index actions).final.claims instrument=raw.claims instrument := by
  induction actions generalizing raw index with
  | nil => rfl
  | cons action rest ih =>
    change ((law scope).execute ((law scope).step raw action) (index+1) rest).final.claims instrument=_
    rw [ih _ _ (fun a h => safe a (List.mem_cons_of_mem _ h)),
      Productive.steps_keep_old_claims scope raw action (safe action List.mem_cons_self) instrument old]

theorem funding_keeps_every_old_financial_position (state : State) (instrument : Instrument)
    (old : instrument≠.delivery) :
    (replenish state).raw.claims instrument=state.raw.claims instrument := by
  unfold replenish
  split
  · rfl
  · change ((law state.origin.scope).next ((law state.origin.scope).next state.raw [])
        (Productive.word state.origin.scope .normal ((law state.origin.scope).next state.raw []))).claims instrument=_
    exact safe_word_claims _ _ _ 0 (Productive.word_historical _ _ _) instrument old

theorem advance_cannot_reissue_the_old_debt (state : State) (instrument : Instrument)
    (old : instrument≠.delivery) :
    (advance state).raw.claims instrument=state.raw.claims instrument :=
  (Synthesis.Runtime.old_instruments_keep_their_full_matrix Production.code (serviceState (replenish state))
    instrument old).trans (funding_keeps_every_old_financial_position state instrument old)

theorem all_future_prefixes_keep_the_actual_settled_matrix (state : State) (count : Nat)
    (instrument : Instrument) (old : instrument≠.delivery) :
    (run state count).raw.claims instrument=state.raw.claims instrument := by
  induction count with
  | zero => rfl
  | succ n ih => exact (advance_cannot_reissue_the_old_debt _ instrument old).trans ih

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Root
