import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeCommandConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Instances.StateCapital.Source

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateSource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Instances
open Distributed.Recall.Information
open Distributed.Recall.Information.Agency.Protocol Continuation

inductive Port where
  | resource (actor : Bool) | service | challenge
  deriving DecidableEq
abbrev Current := RawCurrent Bool Bool (Mandate.State Bool Bool) Unit
abbrev Action := Request Bool Bool Port (Mandate.State Bool Bool) Unit

def base : RawLaw Bool Bool Port Bool Unit where
  technique := fun improved worker => if worker then
    ⟨[(true,1)],[(false,1)],[],[.resource true]⟩ else
    ⟨[(true,1),(false,1)],[(true,if improved then 6 else 5)],[],[.resource false]⟩
  controller := fun _ port => match port with | .resource actor => actor | _ => false
  allowed := fun _ port signer => match port with | .resource actor => decide (actor = signer) | _ => false
  stockPort := fun _ actor _ => .resource actor
  revisionPort := fun _ => .resource false
  revisionCost := StateCapital.law.revisionCost
  settlementUnit := StateCapital.law.settlementUnit
  settlementRate := StateCapital.law.settlementRate
  issuerPort := fun _ => .resource false
  necessities := StateCapital.law.necessities
  mandatoryMaintenance := StateCapital.law.mandatoryMaintenance
  duration := StateCapital.law.duration
def task : PublicTaskSpec Bool Bool := ⟨[⟨false,[(true,1)],.external⟩],0,512,by decide⟩
def scope : Mandate.Scope (Party := Bool) (Good := Bool) (Port := Port) :=
  ⟨task,.service,.challenge,by decide,[(true,2)]⟩
def law := Mandate.law base scope
def initial : Current :=
  ⟨fun _ good => if good then 3 else 0,
   fun _ _ _ => 0,⟨true,0,none,none,none⟩,0,0⟩
def issue : Action := ⟨false,[],.resource false,[],.issue () false true 7⟩
def issued := law.step initial issue
def proposal := Mandate.request scope issued false (.propose true)
def proposed := law.step issued proposal
def acceptance := Mandate.request scope proposed true .accept
def challenge : Action := ⟨false,[],.challenge,[.challenge],.present⟩
def bootstrap := [issue,proposal,acceptance,challenge]
def boot := law.next initial bootstrap
def revoke := Mandate.request scope boot false .revoke

-- Each raw request retains its actual signer; the local command gate chooses
-- the corresponding owner before it can submit that request.
def reproduceLabour : Action := ⟨true,[],.resource true,[],.produce true⟩
def contribute : Action := ⟨true,[],.resource false,[],.transfer true false [(false,1)]⟩
def produceMaterial : Action := ⟨false,[],.resource false,[],.produce false⟩
def wage : Action := ⟨false,[],.resource false,[],.transfer false true [(true,2)]⟩
def consume : Action := ⟨true,[],.resource true,[],.use true [(true,1)] .necessity⟩
def maintain : Action := ⟨false,[],.resource false,[],.use false [(true,1)] .maintenance⟩
def body := [reproduceLabour,contribute,produceMaterial,wage,consume,maintain]

def code : Code Bool Bool Port (Mandate.State Bool Bool) Unit where
  law := law
  initial := initial
  bootstrap := bootstrap
  task := task
  actions := body ++ [revoke]
  actionLimit := 1
  sites := 2
  signals := 1
  initialSignal := 0
  siteParty := fun site => decide (site.val = 1)
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0,.activate 1]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false,true]
  goods := [false,true]
  instruments := [()]
  parties_cover := by intro actor;cases actor <;> simp
  goods_cover := by intro good;cases good <;> simp
  instruments_cover := by intro instrument;cases instrument;simp
def source : Machine Bool Bool Port (Mandate.State Bool Bool) Unit where
  code := code
  reference := fun _ _ => []
  reference_generated := by
    apply code.every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := code.publicPrefix
  original := code.public_prefix_is_an_actual_generated_history
  opponent := EventStep.fixed none
  side := .original
def model : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := Port)
    (Technology := Bool) (Instrument := Unit) := ⟨base,scope,source,rfl,rfl⟩
def origin : Origin model where
  history := ⟨source.history,source.original⟩
  response := ⟨Reaction.restrict code source.opponent,Reaction.restriction_is_generated _ _⟩
  side := .original
def start := EventHistory.ofOrigin model 64 origin
def state := LocalCommandRun.initial model start
def cycle : List LocalCommandSource.Input :=
  [.idle,.idle,.command 0,.idle,.idle,.idle,.command 1,.idle,
   .command 2,.idle,.idle,.idle,.command 3,.idle,.command 4,.idle,
   .command 5,.idle,.idle,.idle]
def inputs := (List.replicate 2 cycle).flatten
def rounds (count : Nat) := LocalCommandRun.run model start (List.replicate count cycle).flatten
def worked := rounds 2
def service := NativeCommandService.produce model start worked 0
def after := service.after model start worked
def deviatingInputs := LocalCommandSource.Input.command 0 :: inputs.tail
def deviating := LocalCommandRun.run model start deviatingInputs

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ProductiveMandateSource
