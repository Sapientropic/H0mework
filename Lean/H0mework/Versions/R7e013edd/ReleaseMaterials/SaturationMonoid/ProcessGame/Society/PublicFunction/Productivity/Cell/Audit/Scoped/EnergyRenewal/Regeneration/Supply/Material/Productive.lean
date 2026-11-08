import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Privacy.Wire

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Protocol.SymbolicAuthentication
abbrev Scope := Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)
abbrev factory : Actor := .inr 1

/-- A source-law permission for the holder's real feed; the production recipes are unchanged. -/
def transport : JointAction := ⟨customer,[],.exchange,[],.transfer customer factory [(.feed,1)]⟩
def law (scope : Scope) : RawLaw Actor Good Port Technology Instrument := {Supply.law scope with
  policy := .opaque fun current action => (Supply.law scope).operationAllowed current action ||
    decide (action=transport ∧ 0<current.claims .delivery supplier receiver)}

theorem every_original_admission_is_preserved (scope : Scope) (current : Current) (action : JointAction)
    (paid : (Supply.law scope).Valid current action) : (law scope).Valid current action := by
  obtain ⟨⟨signer,policy⟩,ports,claims,debit,credit,stock⟩ := paid
  refine ⟨⟨signer,?_⟩,ports,claims,debit,credit,stock⟩
  exact Bool.or_eq_true_iff.mpr (Or.inl policy)

theorem transport_is_rejected_by_the_old_source (scope : Scope) (current : Current) :
    ¬ (Supply.law scope).Valid current transport := by
  intro paid
  have policy := paid.1.2
  simp [RawLaw.operationAllowed,Supply.law,RawPolicy.eval,exchangeAllowed,
    transport,feed,obligation,shipment] at policy

theorem transport_is_paid_from_the_original_holder (scope : Scope) (current : Current)
    (feedstock : 1≤current.stock customer .feed) (pending : 0<current.claims .delivery supplier receiver) :
    (law scope).Valid current transport := by
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,RawLaw.requiredPorts,
    RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,law,transport,Supply.law,
    exchangeAllowed,feed,obligation,shipment,flowAt,locate,amount,customer,factory,feedstock,pending]

theorem paid_transport_moves_the_same_material (scope : Scope) (current : Current)
    (feedstock : 1≤current.stock customer .feed) (pending : 0<current.claims .delivery supplier receiver) :
    ((law scope).step current transport).stock customer .feed=current.stock customer .feed-1 ∧
    ((law scope).step current transport).stock factory .feed=current.stock factory .feed+1 ∧
    ((law scope).step current transport).claims=current.claims := by
  rw [RawLaw.step,if_pos (transport_is_paid_from_the_original_holder scope current feedstock pending)]
  simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,RawLaw.nextClaims,transport,flowAt,locate,amount,customer,factory]

def memo (current : Current) : Current := initialMemo current
theorem memo_exact (current : Current) : memo current=current := initialMemo_exact current

def execute (scope : Scope) (current : Current) : Nat → List JointAction → ExecutionResult Actor Good Port Technology Instrument
  | _,[] => ⟨memo current,[]⟩
  | index,action::rest =>
    let before := memo current
    let tail := execute scope ((law scope).step before action) (index+1) rest
    ⟨tail.final,⟨index,before,action⟩::tail.items⟩
theorem execute_exact (scope : Scope) (current : Current) (index : Nat) (actions : List JointAction) :
    execute scope current index actions=(law scope).execute current index actions := by
  induction actions generalizing current index with
  | nil => simp [execute,RawLaw.execute,memo_exact]
  | cons a rest ih => simp only [execute,memo_exact,ih,RawLaw.execute]

def attempt (scope : Scope) (current : Current) : List (Current → JointAction) → List JointAction
  | [] => []
  | stage::rest =>
    let action := stage current
    if (law scope).Valid current action then action::attempt scope (memo ((law scope).step current action)) rest else [action]

inductive Mode where | normal | denyTransport | denyFactory
  deriving DecidableEq

def stages (current : Current) (mode : Mode) : List (Current → JointAction) :=
  let factoryFunds := current.stock factory .energy<1 ∨ current.stock factory .labor<1
  let donorFunds := current.stock Refeed.donor .energy<1 ∨ current.stock Refeed.donor .labor<1
  let cost : ℚ := (if factoryFunds then 1 else 0)+(if donorFunds then 1 else 0)
  (if current.claims .delivery supplier receiver=0 then [fun _ => obligation] else []) ++
  (if current.stock supplier .energy<cost then
    (if current.stock supplier .feed<1 then [fun _ => feed] else [])++[production] else []) ++
  (if current.stock factory .feed<1 then
    [fun _ => if mode=.denyTransport then {transport with signer:=supplier} else transport] else []) ++
  (if factoryFunds then [fun before => liftProvider before (RenewedQuorumMaterial.give 1)] else []) ++
  [fun before => if mode=.denyFactory then
      {liftProvider before RecycledQuorumMaterial.production with signer:=customer}
    else liftProvider before RecycledQuorumMaterial.production] ++
  (if donorFunds then [fun before => liftProvider before Refeed.fund] else []) ++
  [fun before => liftProvider before Refeed.collect,fun before => liftProvider before Refeed.recycle,
   fun before => liftProvider before Refeed.transport,production,
   fun before => shipment (before.claims .delivery supplier receiver)]

def word (scope : Scope) (mode : Mode) (current : Current) := attempt scope current (stages current mode)
def input {plan : Plan} (state : Finance.State plan) (mode : Mode) : Finance.Input :=
  {law:=law state.session.window.scope,initial:=state.session.current,instructions:=[],
   emission?:=some (word state.session.window.scope mode)}

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {plan : Plan} (state : Finance.State plan) (mode : Mode)
def facade := ProgrammeHistory.facade (input state mode)
def activated := (facade state mode).seed.advance 1
def current : Current :=
  match (facade state mode).readoutAt (activated state mode) .execution with
  | .inl ⟨_,result⟩ => result.after
  | .inr impossible => nomatch impossible

theorem current_is_own_root_next : current state mode=
    ProgrammeSource.rawCurrent (input state mode) (ProgrammeHistory.visitAt (input state mode) 2).current := by
  change (ProgrammeLiving.executionFace (input state mode)
    (ProgrammeSource.emitted (input state mode) (ProgrammeHistory.visitAt (input state mode) 1).current)).after=_
  exact ProgrammeLiving.projected_execution_uses_actual_root_next _ _

theorem same_occurrence_whole_ledger_and_own_next :
    (activated state mode).tick.generated.occurrence=
      (activated state mode).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated state mode).current.visit.current ∧
    HEq (activated state mode).tick.generated.wholeLedgerWriteBack
      ((activated state mode).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated state mode).current.visit.current) ∧
    HEq ((facade state mode).readoutAt (activated state mode) .execution)
      ((activated state mode).tick.generated.projectionOutcome .execution) ∧
    (activated state mode).tick.nextCurrent=
      (ProgrammeHistory.process (input state mode)).stateAt
        ((ProgrammeHistory.process (input state mode)).successor (activated state mode).state) :=
  (ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input state mode) 1).2

def account := Financial.Family.continueVisits Finance.sources (input state mode) 0 2 state.account
end Runtime

theorem steps_keep_old_claims (scope : Scope) (current : Current) (action : JointAction)
    (safe : Historical action) (instrument : Instrument) (old : instrument≠.delivery) :
    ((law scope).step current action).claims instrument=current.claims instrument := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims current action instrument=current.claims instrument
    funext debtor creditor
    cases operation : action.operation <;> simp_all [Historical,RawLaw.nextClaims]
  · rfl

theorem word_historical (scope : Scope) (mode : Mode) (current : Current) :
    ∀ action∈word scope mode current,Historical action := by
  have safe : ∀ current,∀ stage∈stages current mode,∀ before,Historical (stage before) := by
    intro current
    unfold stages
    dsimp only
    repeat' split
    all_goals simp [Historical,transport,feed,obligation,production,shipment,liftProvider,liftProviderOperation,
      RenewedQuorumMaterial.give,RecycledQuorumMaterial.production,Refeed.fund,Refeed.collect,
      Refeed.recycle,Refeed.transport,WorkerInputLaw.energyLabor,WorkerInputLaw.waste,
      RecycledQuorumMaterial.recycle,RecycledQuorumMaterial.waste,UpstreamFeedLaw.request,FuelMandateLaw.give]
  have walk : ∀ current (stages : List (Current → JointAction)),
      (∀ stage∈stages,∀ before,Historical (stage before)) → ∀ action∈attempt scope current stages,Historical action := by
    intro current stages
    induction stages generalizing current with
    | nil => simp [attempt]
    | cons first rest ih =>
      intro safe action member
      simp only [attempt] at member
      split at member
      · rcases List.mem_cons.mp member with rfl | tail
        · exact safe first (by simp) current
        · exact ih _ (fun stage h => safe stage (List.mem_cons_of_mem _ h)) action tail
      · cases List.mem_singleton.mp member;exact safe first (by simp) current
  exact walk current _ (safe current)

theorem after_keeps_old_claims {plan : Plan} (state : Finance.State plan) (mode : Mode)
    (instrument : Instrument) (old : instrument≠.delivery) :
    (Runtime.current state mode).claims instrument=state.session.current.claims instrument := by
  rw [Runtime.current_is_own_root_next]
  have iterate : ∀ (actions : List JointAction) (current : Current) (index : Nat),
      (∀ a∈actions,Historical a) →
      ((law state.session.window.scope).execute current index actions).final.claims instrument=current.claims instrument := by
    intro actions
    induction actions with
    | nil => intros;rfl
    | cons a rest ih =>
      intro current index safe
      change ((law state.session.window.scope).execute ((law state.session.window.scope).step current a)
        (index+1) rest).final.claims instrument=_
      rw [ih _ _ (fun a h => safe a (List.mem_cons_of_mem _ h)),steps_keep_old_claims _ _ _ (safe a (by simp)) instrument old]
  exact iterate _ _ _ (word_historical _ _ _)

open private Supply.Session.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open private Finance.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance

/-- Only a consumed original state enters; both its old origins and its live account survive. -/
def next {plan : Plan} (state : Finance.State plan) (mode : Mode) : Finance.State plan :=
  let old := state.session
  let current := Runtime.current state mode
  let session : Session plan := Supply.Session.mk old.origin old.received old.window current old.target
    (old.history++[⟨input state mode,1⟩]) (by
      calc
        (audit current).claims=(audit old.current).claims := by
          funext i p q;exact congrFun (congrFun (after_keeps_old_claims state mode .audit (by decide)) (.inl p)) (.inl q)
        _ = _ := old.finance) (by
      calc
        (provider current).claims=(provider old.current).claims := by
          funext i p q;exact congrFun (congrFun (after_keeps_old_claims state mode .provider (by decide)) (.inr p)) (.inr q)
        _ = _ := old.providerFinance)
  Finance.State.mk session (Runtime.account state mode)

theorem original_financial_admissions_keep_their_identity {plan : Plan} (state : Finance.State plan) (mode : Mode) :
    state.account.current.slots.map (Financial.Family.slotClaim Finance.sources) <+:
      (next state mode).account.current.slots.map (Financial.Family.slotClaim Finance.sources) := by
  exact (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _).trans
    (Financial.Family.consumeOrigins_preserves_original_claims Finance.sources _ _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive
