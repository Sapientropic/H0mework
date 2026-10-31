import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeServiceRuntime

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate

open Institutions.Capitalism.Universal.Source.Program

/-- Primitive revision requests are calculated from the current source.
The second request uses the actual first step, including refusal and debit. -/
def offerAcceptanceAlphabet {Party Good Port Technology Instrument : Type}
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (current : RawCurrent Party Good (State Party Technology) Instrument)
    (candidates : List Party) : List (Request Party Good Port (State Party Technology) Instrument) :=
  (Delegation.members scope.task).eraseDups.flatMap fun sponsor => candidates.flatMap fun candidate =>
    let proposal := request scope current sponsor (.propose candidate)
    [proposal, request scope ((law base scope).step current proposal) candidate .accept]

namespace Source

inductive Port where
  | service | challenge | resource
  deriving DecidableEq

abbrev Current := RawCurrent Bool Unit (State Bool Unit) Unit
abbrev Action := Request Bool Unit Port (State Bool Unit) Unit

def task : PublicTaskSpec Bool Unit :=
  ⟨[⟨false, [((), 1)], .necessity⟩, ⟨false, [((), 1)], .maintenance⟩], 1, 10, by decide +kernel⟩

def base : RawLaw Bool Unit Port Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ _ => false
  allowed := fun _ port _ => decide (port = .resource)
  stockPort := fun _ _ _ => .resource
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [((), 1)]
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => .resource
  necessities := fun _ _ => [((), 1)]
  mandatoryMaintenance := fun _ _ => [((), 1)]
  duration := fun _ => 1

def scope : Scope (Party := Bool) (Good := Unit) (Port := Port) :=
  ⟨task, .service, .challenge, by decide, [((), 1)]⟩

def law := Mandate.law base scope

def initial : Current where
  stock := fun person _ => if person then 1 else 3
  claims := fun _ _ _ => 7
  technology := ⟨(), 0, none, none, none⟩
  clock := 0
  round := 0

def oldRequest : Action := ⟨true, [], .service, [.service], .present⟩
def necessity : Action := ⟨true, [], .service, [.service], .use false [((), 1)] .necessity⟩
def maintenance : Action := ⟨true, [], .service, [.service], .use false [((), 1)] .maintenance⟩

def alphabet (current : Current) : List Action :=
  offerAcceptanceAlphabet base scope current [true] ++ [necessity, maintenance]

theorem positive_task : ∀ slot ∈ task.slots, ∃ item ∈ slot.goods, 0 < item.2 := by
  intro slot inside
  simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl <;> exact ⟨((), 1), by decide, by decide⟩

def source : OutstandingSource Bool Unit Port (State Bool Unit) Unit where
  seed := {
    law := law
    initial := initial
    task := task
    actionsAt := alphabet
    budget := 4
    original := [oldRequest]
    refused := by decide +kernel }
  positive := positive_task

def actualGrants (depth : Nat) :=
  grantsAt base scope (source.currentAt (depth + 1)) (source.actualExecution depth).submitted

theorem planner_generates_its_own_authority :
    (source.actualExecution 1).submitted =
      [request scope (source.currentAt 2) false (.propose true),
        request scope (law.step (source.currentAt 2)
          (request scope (source.currentAt 2) false (.propose true))) true .accept,
        necessity, maintenance] ∧
    (source.actualExecution 1).after.technology.holder = some true ∧
    (source.actualExecution 1).after.technology.version = 2 ∧
    (source.actualExecution 1).after.stock false () = 0 ∧
    (source.actualExecution 1).after.stock true () = 0 ∧
    (source.actualExecution 1).after.claims () false true = 7 ∧
    source.pendingSlots (source.frameAt 3).payments = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [source.actual_execution_word]
    with_unfolding_all rfl
  · rw [source.actual_execution_after]; decide +kernel
  · rw [source.actual_execution_after]; decide +kernel
  · rw [source.actual_execution_after]; decide +kernel
  · rw [source.actual_execution_after]; decide +kernel
  · rw [source.actual_execution_after]; decide +kernel
  · decide +kernel

theorem actual_grant_is_generated : (actualGrants 1).length = 1 := by decide +kernel

def grant : Grant base scope (source.currentAt 2) (source.actualExecution 1).submitted :=
  (actualGrants 1).get ⟨0, by rw [actual_grant_is_generated]; decide⟩

theorem grant_signatures_and_original_scope :
    grant.proposal.item.val.request.signer = false ∧
    grant.acceptance.item.val.request.signer = true ∧
    grant.candidate = true ∧ grant.electionEvent.officeSeed = scope.service := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Source

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate
