import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation.Runtime

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Regression

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

abbrev Port := Mandate.Source.Port
abbrev Action := Request Bool Bool Port (Mandate.State Bool Unit) Unit
abbrev task : PublicTaskSpec Bool Bool := ⟨[⟨false,[(true,1)],.necessity⟩],0,100,by decide +kernel⟩
def base : RawLaw Bool Bool Port Unit Unit where
  technique := fun _ _ => ⟨[(false,1)],[(true,2)],[],[]⟩
  controller := fun _ _ => false
  allowed := fun _ port _ => decide (port = .resource)
  stockPort := fun _ _ _ => .resource
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [(false,1)]
  settlementUnit := fun _ => false
  settlementRate := fun _ => 1
  issuerPort := fun _ => .resource
  necessities := fun _ _ => [(true,1)]
  mandatoryMaintenance := fun _ _ => []
  duration := fun _ => 1
abbrev scope : Mandate.Scope (Party := Bool) (Good := Bool) (Port := Port) :=
  ⟨task,.service,.challenge,by decide +kernel,[(false,1)]⟩
abbrev law := Mandate.law base scope
abbrev initial : RawCurrent Bool Bool (Mandate.State Bool Unit) Unit :=
  ⟨fun _ _ => 20,fun _ _ _ => 0,⟨(),0,none,none,none⟩,0,0⟩
def proposal := Mandate.request scope initial false (.propose false)
def acceptance := Mandate.request scope (law.step initial proposal) false .accept
def serve : Action := ⟨false,[],.service,[.service],.use false [(true,1)] .necessity⟩
def issue : Action := ⟨false,[],.resource,[],.issue () false true 1⟩
def repay : Action := ⟨false,[],.resource,[],.settle () false true 1⟩
def production : Action := ⟨false,[],.resource,[],.produce false⟩
def free : Action := ⟨false,[],.resource,[],.present⟩
def waste : Action := ⟨false,[],.resource,[],.use false [(false,1)] .external⟩
abbrev code : Code Bool Bool Port (Mandate.State Bool Unit) Unit where
  law := law
  initial := initial
  bootstrap := [proposal,acceptance,serve,issue,repay]
  task := task
  actions := [production,free,waste]
  actionLimit := 1
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false,true]
  goods := [false,true]
  instruments := [()]
  parties_cover := by intro p;cases p <;> simp
  goods_cover := by intro g;cases g <;> simp
  instruments_cover := by intro i;cases i;simp

def originalPolicy : code.Policy := fun _ _ => []
theorem original_generated : originalPolicy ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [originalPolicy])
abbrev rival : Opponent code := fun _ _ _ => none
abbrev point : Cursor code :=
  ⟨originalPolicy,original_generated,code.publicPrefix,code.public_prefix_is_an_actual_generated_history,
    rival,.original,⟨rival,1⟩,[],0,code.publicPrefix.length+1⟩
abbrev model : Native.Authority.Bound (Party := Bool) (Good := Bool) (Port := Port)
    (Technology := Unit) (Instrument := Unit) := ⟨base,scope,point.source,rfl,rfl⟩
abbrev domain := [point]
abbrev member : Replanning.Point model domain := ⟨point,List.mem_singleton_self _⟩
def activation (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.activate site,by
    have same : site = 0 := Subsingleton.elim _ _
    subst site
    simp [code]⟩,by
    have same : site = 0 := Subsingleton.elim _ _
    subst site
    simp [ownMoves,code]⟩
abbrev fallback : Rule code := ⟨some (fun _ _ => [production,production]),fun key _ => activation key.1⟩
abbrev reference : Program code := [fallback]
abbrev prepared := Open.Continuation.Runtime.prepare model domain fallback reference 0 1 member rival
abbrev publicFlowCompletedFacade := Open.Continuation.Runtime.facade model domain fallback reference 0 1 member rival prepared

def raw (count : Nat) : Program code :=
  [⟨some (fun _ _ => List.replicate count free ++ [production,production]),fallback.events⟩]
def wasteful : Program code := [⟨some (fun _ _ => [waste,production,production]),fallback.events⟩]

theorem arbitrarily_long_free_presentations_keep_their_original_source (count : Nat) :
    Open.Supported model domain fallback (raw count) := by
  intro ordinal _ policy chosen key present request occurs
  have sameStage : stage code fallback (raw count) ordinal =
      ⟨some (fun _ _ => List.replicate count free ++ [production,production]),fallback.events⟩ := by
    cases ordinal <;> rfl
  rw [sameStage] at chosen
  have same : policy = (fun _ _ => List.replicate count free ++ [production,production]) := Option.some.inj chosen.symm
  subst policy
  rcases List.mem_append.mp occurs with freeRequest | productionRequest
  · have equal := List.eq_of_mem_replicate freeRequest
    subst request
    simp
  · simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at productionRequest
    subst request
    simp

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Flow.Regression
