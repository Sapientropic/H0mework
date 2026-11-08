import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Wire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.DonorRelease
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

/-- The original donor signs a real transfer; no hidden balance is copied into the recipient. -/
def request (quantity : ℚ) : JointAction :=
  ⟨receiver,[],.audit (native .common),[],.transfer receiver customer [(.feed,quantity)]⟩

theorem paid (scope : Scope) (current : Current) (quantity : ℚ)
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (nonnegative : 0≤quantity) (stock : quantity≤current.stock receiver .feed) :
    (law scope).Valid current (request quantity) := by
  simp only [native] at service challenge
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    law,Supply.law,request,auditAction,auditOperation,auditParty,auditPort,
    EnergyRenewal.energyBase,Scoped.baseLaw,Cell.law,Mandate.law,Mandate.eraseCurrent,
    Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,audit,receiver,customer,
    native,Scoped.erasePort,flowAt,locate,amount,nonnegative,stock,service,challenge,
    Ne.symm service,Ne.symm challenge]

theorem debit_credit (scope : Scope) (current : Current) (quantity : ℚ) :
    (law scope).debit current (request quantity)=[((receiver,.feed),quantity)] ∧
    (law scope).credit current (request quantity)=[((customer,.feed),quantity)] := by
  exact ⟨rfl,rfl⟩

theorem actual_stock (scope : Scope) (current : Current) (quantity : ℚ)
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (nonnegative : 0≤quantity) (stock : quantity≤current.stock receiver .feed) :
    ((law scope).step current (request quantity)).stock receiver .feed=current.stock receiver .feed-quantity ∧
    ((law scope).step current (request quantity)).stock customer .feed=current.stock customer .feed+quantity ∧
    ((law scope).step current (request quantity)).claims=current.claims := by
  rw [RawLaw.step,if_pos (paid scope current quantity service challenge nonnegative stock)]
  simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,RawLaw.nextClaims,request,receiver,customer,flowAt,locate,amount]

theorem wrong_provider_signer_is_rejected (scope : Scope) (current : Current) (quantity : ℚ) :
    ¬ (law scope).Valid current {request quantity with signer:=supplier} := by
  intro valid
  have permission:=valid.1.2
  simp [RawLaw.operationAllowed,RawPolicy.eval,law,Supply.law,request,transport,
    auditAction,auditParty,auditPort,auditOperation,receiver,supplier,customer] at permission

def allowed (remaining quantity : Nat) : Prop := 0<quantity ∧ quantity≤remaining
instance (remaining quantity : Nat) : Decidable (allowed remaining quantity) := inferInstanceAs (Decidable (_∧_))
def word (remaining quantity : Nat) : List JointAction :=
  if allowed remaining quantity then [request quantity] else []
def input {plan : Plan} (state : Finance.State plan) (remaining quantity : Nat) : Finance.Input :=
  {law:=law state.session.window.scope,initial:=state.session.current,instructions:=[],
   emission?:=some (fun _ => word remaining quantity)}

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {plan : Plan} (state : Finance.State plan) (remaining quantity : Nat)
def facade := ProgrammeHistory.facade (input state remaining quantity)
def activated := (facade state remaining quantity).seed.advance 1
def current : Current :=
  match (facade state remaining quantity).readoutAt (activated state remaining quantity) .execution with
  | .inl ⟨_,result⟩ => result.after
  | .inr impossible => nomatch impossible

theorem current_is_own_root_next : current state remaining quantity=
    ProgrammeSource.rawCurrent (input state remaining quantity)
      (ProgrammeHistory.visitAt (input state remaining quantity) 2).current := by
  exact ProgrammeLiving.projected_execution_uses_actual_root_next _ _

theorem same_occurrence_whole_ledger_and_own_next :
    (activated state remaining quantity).tick.generated.occurrence=
      (activated state remaining quantity).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated state remaining quantity).current.visit.current ∧
    HEq (activated state remaining quantity).tick.generated.wholeLedgerWriteBack
      ((activated state remaining quantity).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated state remaining quantity).current.visit.current) ∧
    HEq ((facade state remaining quantity).readoutAt (activated state remaining quantity) .execution)
      ((activated state remaining quantity).tick.generated.projectionOutcome .execution) ∧
    (activated state remaining quantity).tick.nextCurrent=
      (ProgrammeHistory.process (input state remaining quantity)).stateAt
        ((ProgrammeHistory.process (input state remaining quantity)).successor (activated state remaining quantity).state) :=
  (ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input state remaining quantity) 1).2

def account := Financial.Family.continueVisits Finance.sources (input state remaining quantity) 0 2 state.account
end Runtime

def prepared (scope : Scope) (current : Current) := (law scope).next current []
def after (scope : Scope) (current : Current) (remaining quantity : Nat) :=
  (law scope).next (prepared scope current) (word remaining quantity)

theorem runtime_is_actual_execution {plan : Plan} (state : Finance.State plan) (remaining quantity : Nat) :
    Runtime.current state remaining quantity=after state.session.window.scope state.session.current remaining quantity := by
  rw [Runtime.current_is_own_root_next]
  rfl

theorem claims_preserved (scope : Scope) (current : Current) (remaining quantity : Nat) :
    (after scope current remaining quantity).claims=current.claims := by
  unfold after word
  split
  · change ((law scope).step (prepared scope current) (request quantity)).claims=current.claims
    unfold RawLaw.step
    split
    · rfl
    · rfl
  · rfl

open private Supply.Session.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open private Finance.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance

def next {plan : Plan} (state : Finance.State plan) (remaining quantity : Nat) : Finance.State plan :=
  let old:=state.session
  let current:=Runtime.current state remaining quantity
  let claims : current.claims=old.current.claims := by
    change (Runtime.current state remaining quantity).claims=state.session.current.claims
    rw [runtime_is_actual_execution];exact claims_preserved _ _ _ _
  let session : Session plan := Supply.Session.mk old.origin old.received old.window current old.target
    (old.history++[⟨input state remaining quantity,1⟩]) (by
      calc
        (audit current).claims=(audit old.current).claims := by simp only [audit,claims]
        _ = _ := old.finance) (by
      calc
        (provider current).claims=(provider old.current).claims := by simp only [provider,claims]
        _ = _ := old.providerFinance)
  Finance.State.mk session (Runtime.account state remaining quantity)

theorem original_financial_admissions_keep_their_identity {plan : Plan} (state : Finance.State plan)
    (remaining quantity : Nat) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (next state remaining quantity).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  exact (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _).trans
    (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _)

theorem after_stock (scope : Scope) (current : Current) (remaining quantity : Nat)
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (admitted : allowed remaining quantity) (funded : (remaining:ℚ)≤current.stock receiver .feed) :
    (after scope current remaining quantity).stock receiver .feed=current.stock receiver .feed-quantity ∧
    (after scope current remaining quantity).stock customer .feed=current.stock customer .feed+quantity := by
  have enough : (quantity:ℚ)≤current.stock receiver .feed := le_trans (by exact_mod_cast admitted.2) funded
  unfold after word
  rw [if_pos admitted]
  exact ⟨(actual_stock scope (prepared scope current) quantity service challenge (Nat.cast_nonneg _) enough).1,
    (actual_stock scope (prepared scope current) quantity service challenge (Nat.cast_nonneg _) enough).2.1⟩

def left (remaining quantity : Nat) := if allowed remaining quantity then remaining-quantity else remaining

structure Budget (plan : Plan) where
  state : Finance.State plan
  remaining : Nat
  funded : (remaining:ℚ)≤state.session.current.stock receiver .feed

/-- A public six-unit issue is admitted from the consumed source's own stock. -/
def admit {plan : Plan} (state : Finance.State plan) : Option (Budget plan) :=
  if funded : (6:ℚ)≤state.session.current.stock receiver .feed then some ⟨state,6,funded⟩ else none

def advance {plan : Plan} (budget : Budget plan) (quantity : Nat) : Budget plan :=
  ⟨next budget.state budget.remaining quantity,left budget.remaining quantity,by
    change (left budget.remaining quantity:ℚ)≤(Runtime.current budget.state budget.remaining quantity).stock receiver .feed
    rw [runtime_is_actual_execution]
    by_cases accepted : allowed budget.remaining quantity
    · rw [(after_stock _ _ _ _ (by simp [Continuation.Window.scope,native])
        (by simp [Continuation.Window.scope,native]) accepted budget.funded).1]
      simp only [left,if_pos accepted,Nat.cast_sub accepted.2]
      linarith [budget.funded]
    · simpa [left,after,word,prepared,accepted,RawLaw.next,RawLaw.execute] using budget.funded⟩

theorem rejects_overdraw {plan : Plan} (budget : Budget plan) (quantity : Nat)
    (overdraw : budget.remaining<quantity) :
    (advance budget quantity).remaining=budget.remaining ∧ word budget.remaining quantity=[] := by
  have refused : ¬allowed budget.remaining quantity := fun h => (Nat.not_le_of_lt overdraw) h.2
  simp [advance,left,word,refused]

theorem no_unbacked_feed_credit {plan : Plan} (budget : Budget plan) (quantity : Nat)
    (accepted : allowed budget.remaining quantity) :
    (advance budget quantity).state.session.current.stock customer .feed=
        budget.state.session.current.stock customer .feed+quantity ∧
    (advance budget quantity).state.session.current.stock receiver .feed=
        budget.state.session.current.stock receiver .feed-quantity := by
  have flows:=after_stock budget.state.session.window.scope budget.state.session.current budget.remaining quantity
    (by simp [Continuation.Window.scope,native]) (by simp [Continuation.Window.scope,native]) accepted budget.funded
  change (Runtime.current _ _ _).stock customer .feed=_ ∧ (Runtime.current _ _ _).stock receiver .feed=_
  rw [runtime_is_actual_execution]
  exact ⟨flows.2,flows.1⟩

theorem step_twin {first second : Current} (same : Twin first second) (scope : Scope) (quantity : ℚ)
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (nonnegative : 0≤quantity) (firstStock : quantity≤first.stock receiver .feed)
    (secondStock : quantity≤second.stock receiver .feed) :
    Twin ((law scope).step first (request quantity)) ((law scope).step second (request quantity)) := by
  rw [RawLaw.step,if_pos (paid scope first quantity service challenge nonnegative firstStock),
    RawLaw.step,if_pos (paid scope second quantity service challenge nonnegative secondStock)]
  exact same.paidStep scope (request quantity)

theorem after_twin {first second : Current} (same : Twin first second) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)])
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (remaining quantity : Nat) (firstStock : (remaining:ℚ)≤first.stock receiver .feed)
    (secondStock : (remaining:ℚ)≤second.stock receiver .feed) :
    Twin (after scope first remaining quantity) (after scope second remaining quantity) := by
  have preparation:=next_public same scope cost [] (by simp)
  unfold after word
  split
  · rename_i accepted
    have done:=step_twin preparation scope quantity service challenge (Nat.cast_nonneg _)
      (le_trans (by exact_mod_cast accepted.2) firstStock)
      (le_trans (by exact_mod_cast accepted.2) secondStock)
    exact ⟨done.technology,congrArg (·+1) preparation.clock,congrArg Nat.succ preparation.round,done.claims,done.stock⟩
  · exact next_public preparation scope cost [] (by simp)

structure Related {lp rp : Plan} (first : Budget lp) (second : Budget rp) : Prop where
  session : Supply.Privacy.Source.SessionTwin first.state.session second.state.session
  quota : first.remaining=second.remaining

theorem related_next {lp rp : Plan} (first : Budget lp) (second : Budget rp)
    (same : Related first second) (quantity : Nat) : Related (advance first quantity) (advance second quantity) := by
  refine ⟨⟨?_,same.session.scope,same.session.target,?_⟩,by simp only [advance,same.quota]⟩
  · change Twin (Runtime.current first.state first.remaining quantity) (Runtime.current second.state second.remaining quantity)
    rw [runtime_is_actual_execution,runtime_is_actual_execution,←same.session.scope,←same.quota]
    exact after_twin same.session.current _ rfl
      (by simp [Continuation.Window.scope,native]) (by simp [Continuation.Window.scope,native])
      _ _ first.funded (by simpa only [same.quota] using second.funded)
  · change (next first.state first.remaining quantity).session.history.length=
      (next second.state second.remaining quantity).session.history.length
    simpa only [next,List.length_append,List.length_singleton] using congrArg (·+1) same.session.history

def observe (scope : Scope) (current : Current) (remaining quantity : Nat) : Observation :=
  let before:=prepared scope current
  ⟨Supply.Privacy.publicize before,publicItems scope before (word remaining quantity) 0,
    Supply.Privacy.publicize (after scope current remaining quantity)⟩

theorem complete_observation_equal {first second : Current} (same : Twin first second) (scope : Scope)
    (cost : scope.revisionCost=[(.energy,1)])
    (service : scope.service≠native .common) (challenge : scope.challenge≠native .common)
    (remaining quantity : Nat) (firstStock : (remaining:ℚ)≤first.stock receiver .feed)
    (secondStock : (remaining:ℚ)≤second.stock receiver .feed) :
    observe scope first remaining quantity=observe scope second remaining quantity := by
  have preparation:=next_public same scope cost [] (by simp)
  have done:=after_twin same scope cost service challenge remaining quantity firstStock secondStock
  dsimp only [observe,prepared]
  rw [preparation.publicize,done.publicize]
  congr 1
  unfold word
  split
  · rename_i accepted
    have fundedFirst : (quantity:ℚ)≤(prepared scope first).stock receiver .feed :=
      le_trans (by exact_mod_cast accepted.2) firstStock
    have fundedSecond : (quantity:ℚ)≤(prepared scope second).stock receiver .feed :=
      le_trans (by exact_mod_cast accepted.2) secondStock
    have paidFirst:=paid scope (prepared scope first) quantity service challenge (Nat.cast_nonneg _) fundedFirst
    have paidSecond:=paid scope (prepared scope second) quantity service challenge (Nat.cast_nonneg _) fundedSecond
    have related:=step_twin preparation scope quantity service challenge (Nat.cast_nonneg _) fundedFirst fundedSecond
    dsimp only [prepared] at paidFirst paidSecond
    simp only [publicItems,execute,memo_exact,List.map_cons,List.map_nil,
      RawLaw.actualDebit,RawLaw.actualCredit,paidFirst,paidSecond,if_true,decide_true]
    rw [preparation.publicize,related.publicize]
    rfl
  · rfl

abbrev Strategy := List Observation → Nat → Nat
def play {plan : Plan} (initial : Budget plan) (strategy : Strategy) : Nat → Budget plan×List Observation
  | 0 => (initial,[])
  | n+1 =>
    let (state,past):=play initial strategy n
    let quantity:=strategy past n
    (advance state quantity,past++[observe state.state.session.window.scope state.state.session.current state.remaining quantity])

theorem every_adaptive_release_preserves_complete_output {lp rp : Plan} (first : Budget lp) (second : Budget rp)
    (same : Related first second) (strategy : Strategy) (count : Nat) :
    Related (play first strategy count).1 (play second strategy count).1 ∧
      (play first strategy count).2=(play second strategy count).2 := by
  induction count with
  | zero => exact ⟨same,rfl⟩
  | succ n ih =>
    have visible :
        observe (play first strategy n).1.state.session.window.scope
            (play first strategy n).1.state.session.current (play first strategy n).1.remaining
            (strategy (play second strategy n).2 n)=
          observe (play second strategy n).1.state.session.window.scope
            (play second strategy n).1.state.session.current (play second strategy n).1.remaining
            (strategy (play second strategy n).2 n) := by
      rw [←ih.1.session.scope,←ih.1.quota]
      exact complete_observation_equal ih.1.session.current (play first strategy n).1.state.session.window.scope rfl
        (by simp [Continuation.Window.scope,native]) (by simp [Continuation.Window.scope,native]) _ _
        (play first strategy n).1.funded (by simpa only [ih.1.quota] using (play second strategy n).1.funded)
    simp only [play,ih.2]
    refine ⟨related_next _ _ ih.1 _,?_⟩
    exact congrArg (fun answer => (play second strategy n).2++[answer]) visible

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.DonorRelease
