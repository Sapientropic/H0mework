import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumMaterial
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmittedAdaptiveWindow

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good Resources)
open RecycledQuorumMaterial (Action law)

def initial (resources : Resources) (fuel : Nat) : RecycledQuorumMaterial.Current :=
  let old := Repayment.Recovery.initial resources
  ⟨fun party good => if party = 1 ∧ good = .feedstock then fuel else old.stock party good,
    old.claims,⟨old.technology.1,0,none,none,none⟩,old.clock,old.round⟩
def issue : Action := ⟨1,[],.reserve 1,[],.issue () 1 2 7⟩
def payout : Action := ⟨2,[],.reserve 2,[],.transfer 2 1 [(.service,7)]⟩
def oldUse : Action := ⟨1,[],.reserve 1,[],.use 1 [(.service,7)] .investment⟩
def oldRequest : Action := ⟨1,[],.service,[.service],.present⟩
def fee (second : Bool) : Action := ⟨1,[],if second then .challenge else .reserve 1,[],.use 1 [(.service,1)] .external⟩

abbrev code (resources : Resources) (fuel : Nat) (supply : Bool) : Code Party Good Port (Mandate.State Party Bool) Unit where
  law := law
  initial := initial resources fuel
  bootstrap := [issue,payout,oldUse,oldRequest]
  task := Repayment.Recovery.task
  actions := [fee false,fee true,RecycledQuorumMaterial.production] ++ if supply then RecycledQuorumMaterial.word else []
  actionLimit := 4
  sites := 3
  signals := 5
  initialSignal := 0
  siteParty := fun _ => 1
  readLocal := fun site snapshot => if 1 < snapshot.stock .energy then
      if site = 0 then 0 else if site = 1 then 1 else 4
    else if site = 0 then 2 else if site = 1 then 3 else 4
  afterAction := fun _ old _ => if h : old.val < 4 then ⟨old.val + 1,by omega⟩ else 4
  afterSend := fun _ _ old _ => if h : old.val < 4 then ⟨old.val + 1,by omega⟩ else 4
  afterDelivery := fun _ _ old _ => old
  sendCost := fun _ _ => [fee false]
  deliveryCost := fun _ => [fee false]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0,.activate 1,.activate 2,.send 0 2,.send 1 2,.send 2 2,
    .deliver 0,.deliver 1,.deliver 2,.deliver 3]
  eventLimit := 0
  eligible := fun _ => true
  parties := [0,1,2]
  goods := [.feedstock,.service,.waste,.energy,.labor]
  instruments := [()]
  parties_cover := by intro party;fin_cases party <;> simp
  goods_cover := by intro good;cases good <;> simp
  instruments_cover := by intro instrument;cases instrument;simp

def work (resources : Resources) (fuel : Nat) (supply : Bool) : (code resources fuel supply).Policy := fun key _ =>
  if key.1 = 2 then
    if key.2 = 0 then [RecycledQuorumMaterial.production]
    else if supply ∧ key.2.val < 4 then RecycledQuorumMaterial.word else []
  else if key.2 = 0 then [fee false] else if key.2 = 2 then [fee true] else []
theorem generated (resources : Resources) (fuel : Nat) (supply : Bool) : work resources fuel supply ∈ (code resources fuel supply).policies := by
  apply (code resources fuel supply).every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  cases supply <;> unfold work <;> split_ifs <;> simp_all [code,RecycledQuorumMaterial.word]

abbrev source (resources : Resources) (fuel : Nat) (supply : Bool) : Machine Party Good Port (Mandate.State Party Bool) Unit where
  code := code resources fuel supply
  reference := work resources fuel supply
  reference_generated := generated resources fuel supply
  history := (code resources fuel supply).publicPrefix
  original := (code resources fuel supply).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev entry (resources : Resources) (fuel : Nat) (supply : Bool) : Input (code resources fuel supply) := ⟨fun _ _ _ => none,40⟩
def start (resources : Resources) (fuel : Nat) (supply : Bool) : Cursor (code resources fuel supply) :=
  ⟨(source resources fuel supply).reference,(source resources fuel supply).reference_generated,
    (source resources fuel supply).history,(source resources fuel supply).original,
    (source resources fuel supply).opponent,(source resources fuel supply).side,entry resources fuel supply,[],0,
    Distributed.Recall.Information.Agency.start (source resources fuel supply) 0⟩
def activation (resources : Resources) (fuel : Nat) (supply : Bool) (site : Fin (code resources fuel supply).sites) : LocalMove (code resources fuel supply) site :=
  ⟨some ⟨.activate site,by fin_cases site <;> simp [code]⟩,by fin_cases site <;> simp [ownMoves,code]⟩
def sending (resources : Resources) (fuel : Nat) (supply : Bool) (site : Fin (code resources fuel supply).sites) : LocalMove (code resources fuel supply) site :=
  ⟨some ⟨.send site 2,by fin_cases site <;> simp [code]⟩,by fin_cases site <;> simp [ownMoves,code]⟩
def protocol (resources : Resources) (fuel : Nat) (supply early : Bool) : Rule (code resources fuel supply) :=
  ⟨⟨work resources fuel supply,generated resources fuel supply⟩,fun key _ =>
    if key.1 = 2 then
      if key.2.val < 4 then activation resources fuel supply key.1 else ⟨none,List.mem_cons_self⟩
    else if early then ⟨none,List.mem_cons_self⟩
    else if key.2 = 0 ∨ key.2 = 2 then activation resources fuel supply key.1
    else if key.2 = 1 ∨ key.2 = 3 then sending resources fuel supply key.1 else ⟨none,List.mem_cons_self⟩⟩
abbrev protocols (resources : Resources) (fuel : Nat) (supply : Bool) : Nat → Rule (code resources fuel supply) :=
  fun index => protocol resources fuel supply (decide (index < 6))
inductive Network where | normal | missing | replay
  deriving DecidableEq
def environment (resources : Resources) (fuel : Nat) (supply : Bool) (network : Network) : Opponent (code resources fuel supply) := fun actual _ _ =>
  let cut := actual.length - (EventStep.seed (start resources fuel supply)).history.length
  if network = .missing then none
  else if cut = 13 then some ⟨.deliver 0,by simp [code]⟩
  else if cut = 15 then some ⟨.deliver 1,by simp [code]⟩
  else if cut = 25 then some ⟨.deliver 2,by simp [code]⟩
  else if cut = 27 then some ⟨.deliver 3,by simp [code]⟩
  else if network = .replay ∧ cut = 29 then some ⟨.deliver 0,by simp [code]⟩ else none
abbrev rivals (resources : Resources) (fuel : Nat) (supply : Bool) (network : Network) : Nat → Opponent (code resources fuel supply) :=
  fun _ => environment resources fuel supply network
def slot (second : Bool) : Scope := ⟨0,0,if second then 1 else 0⟩
abbrev vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port) (Technology := Bool) (Instrument := Unit) :=
  ⟨fun port => if port = .reserve 1 then some (slot false,true) else if port = .challenge then some (slot true,true) else none,
    fun _ => 0,.service⟩
def encoding (resources : Resources) (fuel : Nat) (supply : Bool) : StageTransport.Encoding (code := code resources fuel supply) := fun signal =>
  if signal = 0 then some ⟨6,0,0,1,slot false,true,1⟩
  else if signal = 1 then some ⟨8,0,1,1,slot false,true,1⟩
  else if signal = 2 then some ⟨18,0,0,1,slot true,true,1⟩
  else if signal = 3 then some ⟨20,0,1,1,slot true,true,1⟩ else none
abbrev reception (resources : Resources) (fuel : Nat) (supply : Bool) (delay : Nat) : StageReception.Law (code resources fuel supply) :=
  ⟨fun _ current => slot (decide (current.stock 1 .energy ≤ 1)),delay⟩
abbrev full (resources : Resources) (fuel : Nat) (supply : Bool) (network : Network) :=
  AdmittedAdaptiveWindow.full (start resources fuel supply) (protocols resources fuel supply) (rivals resources fuel supply network) 0 27
def produce (resources : Resources) (fuel : Nat) (supply : Bool) (network : Network) (delay threshold : Nat) (second : Bool) :=
  AdmittedAdaptiveWindow.windowPlan (start resources fuel supply) vocabulary (encoding resources fuel supply)
    (reception resources fuel supply delay) (protocols resources fuel supply) (rivals resources fuel supply network) 0 27 2 (slot second) threshold

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumSource
