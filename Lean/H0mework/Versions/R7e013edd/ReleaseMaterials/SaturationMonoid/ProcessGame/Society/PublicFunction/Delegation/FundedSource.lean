import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.ActualRevocation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.NativeServiceRuntime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Financing

/-! A single outstanding-task source starts its beneficiary with no material.
The lender releases its own stock only after the liability exists. The raw
alphabet, not a supplied financed plan, generates credit, challenge and service.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 12000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.Funded

open Institutions.Capitalism.Universal.Source.Program

abbrev Party := Fin 3
inductive Port where
  | service | challenge | reserve (owner : Party)
  deriving DecidableEq

abbrev Current := RawCurrent Party Unit (Unit × Option Party) Unit
abbrev Action := Request Party Unit Port (Unit × Option Party) Unit

def task : PublicTaskSpec Party Unit :=
  ⟨[⟨1, [((), 1)], .necessity⟩, ⟨1, [((), 1)], .maintenance⟩], 1, 3, by decide +kernel⟩

def base : RawLaw Party Unit Port Unit Unit where
  technique := fun _ _ => ⟨[], [], [], []⟩
  controller := fun _ port => match port with | .reserve owner => owner | _ => 1
  allowed := fun _ port actor => match port with | .reserve owner => decide (actor = owner) | _ => false
  stockPort := fun _ owner _ => .reserve owner
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [((), 1)]
  settlementUnit := fun _ => ()
  settlementRate := fun _ => 1
  issuerPort := fun _ => .reserve 1
  necessities := fun _ _ => [((), 1)]
  mandatoryMaintenance := fun _ _ => [((), 1)]
  duration := fun _ => 1
  policy := .opaque (fun current request => match request.operation with
    | .issue _ debtor creditor quantity =>
        decide (debtor = 1 ∧ creditor = 2 ∧ quantity = 3 ∧ current.claims () 1 2 = 7)
    | .transfer sender recipient _ =>
        decide (sender = 2 ∧ recipient = 1 ∧ 10 ≤ current.claims () 1 2)
    | _ => true)

def scope : Jurisdiction Party Unit Port :=
  ⟨task, .service, .challenge, by decide, [((), 1)]⟩

def law := Delegation.law base scope

def initial : Current where
  stock := fun person _ => if person = 2 then 3 else 0
  claims := fun _ _ _ => 7
  technology := ((), some 0)
  clock := 0
  round := 0

def terms : Financing.Terms Party Unit := ⟨1, 2, (), 3⟩
def issue : Action := ⟨1, [], .reserve 1, [], .issue () 1 2 3⟩
def payout : Action := ⟨2, [], .reserve 2, [], .transfer 2 1 [((), 3)]⟩
def necessity : Action := ⟨1, [], .service, [.service], .use 1 [((), 1)] .necessity⟩
def maintenance : Action := ⟨1, [], .service, [.service], .use 1 [((), 1)] .maintenance⟩
def oldRequest : Action := ⟨0, [], .service, [.service], .present⟩
def original : Action := ⟨1, [], .service, [.service], .present⟩

def alphabet (current : Current) : List Action :=
  [issue, payout] ++ (members task).eraseDups.map (revokeRequest scope current) ++
    [necessity, maintenance]

def source : OutstandingSource Party Unit Port (Unit × Option Party) Unit where
  seed := {
    law := law
    initial := initial
    task := task
    actionsAt := alphabet
    budget := 5
    original := [original]
    refused := by decide +kernel }
  positive := by
    intro slot inside
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨((), 1), by decide, by decide⟩

def necessitySlot : source.Slot := ⟨0, by decide⟩
def maintenanceSlot : source.Slot := ⟨1, by decide⟩

theorem zero_material_before_actual_funding :
    (source.actualExecution 1).before.stock 1 () = 0 ∧
    (source.actualExecution 1).before.stock 2 () = 3 ∧
    (source.actualExecution 1).before.claims () 1 2 = 7 := by
  rw [source.actual_execution_before]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem planner_generates_joint_word :
    (source.actualExecution 1).submitted =
      [issue, payout, revokeRequest scope (source.currentAt 2) 1, necessity, maintenance] := by
  rw [source.actual_execution_word]
  with_unfolding_all rfl

theorem joint_actual_effect :
    (source.actualExecution 1).after.technology = ((), none) ∧
    (source.actualExecution 1).after.stock 1 () = 0 ∧
    (source.actualExecution 1).after.stock 2 () = 0 ∧
    (source.actualExecution 1).after.claims () 1 2 = 10 ∧
    (source.actualExecution 1).after.claims () 0 1 = 7 ∧
    (source.frameAt 3).payments necessitySlot = some 2 ∧
    (source.frameAt 3).payments maintenanceSlot = some 2 := by
  rw [source.actual_execution_after]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Delegation.Funded
