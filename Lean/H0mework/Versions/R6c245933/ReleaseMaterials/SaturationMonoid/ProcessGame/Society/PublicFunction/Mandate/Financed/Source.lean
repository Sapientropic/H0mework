import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Continuation.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open Mandate.Source (Port)

inductive Good where
  | feedstock | service
  deriving DecidableEq

abbrev Current := RawCurrent Bool Good (State Bool Unit) Unit
abbrev Action := Request Bool Good Port (State Bool Unit) Unit

def task : PublicTaskSpec Bool Good :=
  ⟨[⟨false, [(.service, 1)], .necessity⟩, ⟨false, [(.service, 1)], .maintenance⟩],
    1, 10, by decide +kernel⟩

def base : RawLaw Bool Good Port Unit Unit where
  technique := fun _ _ => ⟨[(.feedstock, 1)], [(.service, 3)], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ port _ => decide (port = .resource)
  stockPort := fun _ _ _ => .resource
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [(.service, 1)]
  settlementUnit := fun _ => .service
  settlementRate := fun _ => 1
  issuerPort := fun _ => .resource
  necessities := fun _ _ => [(.service, 1)]
  mandatoryMaintenance := fun _ _ => [(.service, 1)]
  duration := fun _ => 1

def scope : Scope (Party := Bool) (Good := Good) (Port := Port) :=
  ⟨task, .service, .challenge, by decide, [(.service, 1)]⟩
def law := Mandate.law base scope
def position : Repayment.Position Bool Unit := ⟨(), false, true⟩
def terms : Financing.Terms Bool Unit := ⟨false, true, (), 7⟩

def initial (fuel : ℚ) : Current where
  stock := fun actor good => match actor, good with
    | false, .feedstock => fuel
    | true, .service => 8
    | _, _ => 0
  claims := fun _ _ _ => 0
  technology := ⟨(), 0, none, none, none⟩
  clock := 0
  round := 0

def issue : Action := ⟨false, [], .resource, [], .issue () false true 7⟩
def payout : Action := ⟨true, [], .resource, [], .transfer true false [(.service, 7)]⟩
def oldRequest : Action := ⟨true, [], .service, [.service], .present⟩
def necessity : Action := ⟨true, [], .service, [.service], .use false [(.service, 1)] .necessity⟩
def maintenance : Action := ⟨false, [], .service, [.service], .use false [(.service, 1)] .maintenance⟩

def original (fuel : ℚ) : List Action :=
  let funded := law.step (law.step (initial fuel) issue) payout
  let proposal := request scope funded false (.propose true)
  let acceptance := request scope (law.step funded proposal) true .accept
  [oldRequest, issue, payout, proposal, acceptance, necessity]

def alphabet (current : Current) : List Action :=
  offerAcceptanceAlphabet base scope current (Delegation.members task).eraseDups ++
    [{necessity with signer := false}, maintenance]

/-- Only current authority and the actual last boundary choose a request.
Repayment uses the current claim, stock and local paid production. -/
def incoming (current : Current) : Option (IncomingWord law current) :=
  if current.technology.holder = some false then
    IncomingWord.check law current [request scope current false .exit]
  else if current.technology.holder = some true then
    IncomingWord.check law current (Response.produce base scope current).word
  else if current.technology.last = some .exit then
    IncomingWord.check law current (Repayment.respond law position current).word
  else none

def sourceWithFuel (fuel : ℚ) : OutstandingSource Bool Good Port (State Bool Unit) Unit where
  seed := {
    law := law
    initial := initial fuel
    task := task
    actionsAt := alphabet
    budget := 3
    original := original fuel
    refused := by
      refine ⟨⟨0, law.next (initial fuel) [], oldRequest⟩, List.mem_cons_self, ?_⟩
      intro accepted
      have permission := accepted.2.1 .service (by simp [RawLaw.requiredPorts, RawLaw.debit, oldRequest])
      rcases permission with permission | consent
      · cases permission
      · exact List.not_mem_nil consent }
  positive := by
    intro slot inside
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨(.service, 1), by decide, by decide⟩
  incoming? := incoming
  completionReport := fun current => (Response.produce base scope current).report

def source := sourceWithFuel 3
def bound : BoundSource base scope := ⟨source, rfl⟩
def shortSource := sourceWithFuel 2
def shortBound : BoundSource base scope := ⟨shortSource, rfl⟩

theorem zero_financial_genesis : source.input.initial.claims = fun _ _ _ => 0 := rfl

def grant := (NativeRuntime.actualGrants bound 0).get ⟨0, by
  change 0 < (grantsAt base scope (source.currentAt 1) (source.actualExecution 0).submitted).length
  rw [(source.canonical_frame 1).1, source.actual_execution_word]
  decide +kernel⟩

def history (last : Nat) := Lifecycle.through (base := base) (scope := scope)
  (currentAt := Lifecycle.Runtime.currentAt bound) (wordAt := Lifecycle.Runtime.wordAt bound)
  (birth := 0) (grant := grant) last

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed
