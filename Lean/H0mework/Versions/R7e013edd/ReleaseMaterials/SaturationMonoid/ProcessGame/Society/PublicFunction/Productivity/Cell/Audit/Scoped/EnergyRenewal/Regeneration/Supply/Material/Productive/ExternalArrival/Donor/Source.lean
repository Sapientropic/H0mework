import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.ExternalArrival.Wire
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.DonorRelease

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def quantity : ℚ := 6
def request (signer : Actor) : JointAction := {DonorRelease.request quantity with signer:=signer}
def origin {plan : Plan} (state : Finance.State plan) := state.session.current.round

inductive Refusal where
  | stale | withheld | signer | material | sourceLaw
  deriving DecidableEq
inductive Status where
  | supplied | blocked (reason : Refusal)
  deriving DecidableEq

def status {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor)
    (enabled : Bool) (current : Current) : Status :=
  if round ≠ origin state then .blocked .stale
  else if !enabled then .blocked .withheld
  else if signer ≠ receiver then .blocked .signer
  else if ¬quantity ≤ current.stock receiver .feed then .blocked .material
  else if ¬(Productive.law state.session.window.scope).Valid current (request signer) then .blocked .sourceLaw
  else .supplied

def word {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor)
    (enabled : Bool) (current : Current) : List JointAction :=
  if status state round signer enabled current = .supplied then [request signer] else []

def input {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) : Finance.Input :=
  {law:=Productive.law state.session.window.scope,initial:=state.session.current,instructions:=[],
   emission?:=some (word state round signer enabled)}
def prepared {plan : Plan} (state : Finance.State plan) :=
  (Productive.law state.session.window.scope).next state.session.current []
def expected {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) :=
  (Productive.law state.session.window.scope).next (prepared state) (word state round signer enabled (prepared state))

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool)
def facade := ProgrammeHistory.facade (input state round signer enabled)
def activated := (facade state round signer enabled).seed.advance 1
def current : Current :=
  match (facade state round signer enabled).readoutAt (activated state round signer enabled) .execution with
  | .inl ⟨_,result⟩ => result.after
  | .inr impossible => nomatch impossible
theorem current_is_own_root_next : current state round signer enabled =
    ProgrammeSource.rawCurrent (input state round signer enabled)
      (ProgrammeHistory.visitAt (input state round signer enabled) 2).current :=
  ProgrammeLiving.projected_execution_uses_actual_root_next _ _
theorem same_occurrence_whole_ledger_and_own_next :
    (activated state round signer enabled).tick.generated.occurrence =
      (activated state round signer enabled).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated state round signer enabled).current.visit.current ∧
    HEq (activated state round signer enabled).tick.generated.wholeLedgerWriteBack
      ((activated state round signer enabled).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated state round signer enabled).current.visit.current) ∧
    HEq ((facade state round signer enabled).readoutAt (activated state round signer enabled) .execution)
      ((activated state round signer enabled).tick.generated.projectionOutcome .execution) ∧
    (activated state round signer enabled).tick.nextCurrent =
      (ProgrammeHistory.process (input state round signer enabled)).stateAt
        ((ProgrammeHistory.process (input state round signer enabled)).successor (activated state round signer enabled).state) :=
  (ProgrammeHistory.execution_face_shares_whole_ledger_and_next (input state round signer enabled) 1).2
def account := Financial.Family.continueVisits Finance.sources (input state round signer enabled) 0 2 state.account
end Runtime

theorem runtime_is_the_actual_word {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) :
    Runtime.current state round signer enabled = expected state round signer enabled := by
  rw [Runtime.current_is_own_root_next]
  rfl

theorem claims_preserved {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) :
    (expected state round signer enabled).claims = state.session.current.claims := by
  unfold expected word
  split
  · change ((Productive.law state.session.window.scope).step (prepared state) (request signer)).claims = _
    unfold RawLaw.step
    split <;> rfl
  · rfl

open private Supply.Session.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open private Finance.State.mk from H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Finance

def nextFinance {plan : Plan} (state : Finance.State plan) (round : Nat) (signer : Actor) (enabled : Bool) : Finance.State plan :=
  let old := state.session
  let current := Runtime.current state round signer enabled
  let claims : current.claims = old.current.claims := by
    change (Runtime.current state round signer enabled).claims = state.session.current.claims
    rw [runtime_is_the_actual_word]
    exact claims_preserved state round signer enabled
  let session := Supply.Session.mk old.origin old.received old.window current old.target
    (old.history++[⟨input state round signer enabled,1⟩])
    (by calc
      (audit current).claims = (audit old.current).claims := by simp only [audit,claims]
      _ = _ := old.finance)
    (by calc
      (provider current).claims = (provider old.current).claims := by simp only [provider,claims]
      _ = _ := old.providerFinance)
  Finance.State.mk session (Runtime.account state round signer enabled)

structure Receipt (plan : Plan) where
  private mk ::
  before : Finance.State plan
  round : Nat
  signer : Actor
  enabled : Bool
def Receipt.after {plan : Plan} (receipt : Receipt plan) :=
  nextFinance receipt.before receipt.round receipt.signer receipt.enabled

structure State (plan : Plan) where
  private mk ::
  legacy : Consume.State plan
  receipts : List (Receipt plan)

def start {plan : Plan} (legacy : Consume.State plan) : State plan := ⟨legacy,[]⟩
open private Consume.State.mk in Consume.arrival in
def donate {plan : Plan} (state : State plan) (round : Nat) (signer : Actor) (enabled : Bool) : State plan :=
  let receipt : Receipt plan := ⟨state.legacy.service,round,signer,enabled⟩
  ⟨Consume.State.mk receipt.after state.legacy.spent,state.receipts++[receipt]⟩

def operate {plan : Plan} (state : State plan) (command : Lean.Json) : State plan :=
  ⟨Wire.advance state.legacy command,state.receipts⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.ExternalArrival.Donor
