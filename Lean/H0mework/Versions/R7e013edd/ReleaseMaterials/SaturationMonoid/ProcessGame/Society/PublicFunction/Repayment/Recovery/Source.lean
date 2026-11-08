import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery.Local
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery

open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open OutstandingSource.NativeService
open Delegation.Funded (Party Port)

inductive Good where
  | feedstock | service | waste | energy | labor
  deriving DecidableEq

structure Resources where
  energy : ℚ
  labor : ℚ
  willing : Bool

abbrev Current := RawCurrent Party Good (Bool × Option Party) Unit
abbrev RequestAt := Request Party Good Port (Bool × Option Party) Unit

def task : PublicTaskSpec Party Good :=
  ⟨[⟨1, [(.service, 1)], .necessity⟩, ⟨1, [(.service, 1)], .maintenance⟩], 1, 3, by decide +kernel⟩

def base : RawLaw Party Good Port Bool Unit where
  technique := fun _ operator =>
    if operator = 1 then
      ⟨[(.feedstock, 1), (.energy, 1)], [(.service, 3), (.waste, 1)], [(.labor, 1)], [.reserve operator]⟩
    else ⟨[(.waste, 1), (.energy, 1)], [(.feedstock, 1)], [(.labor, 1)], [.reserve operator]⟩
  controller := fun _ port => match port with | .reserve owner => owner | _ => 1
  allowed := fun _ port actor => match port with | .reserve owner => decide (actor = owner) | _ => false
  stockPort := fun _ owner _ => .reserve owner
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [(.service, 1)]
  settlementUnit := fun _ => .service
  settlementRate := fun _ => 1
  issuerPort := fun _ => .reserve 1
  necessities := fun _ _ => [(.service, 1)]
  mandatoryMaintenance := fun _ _ => [(.service, 1)]
  duration := fun _ => 1
  policy := .opaque (fun current request => match request.operation with
    | .produce operator => decide (operator = 1 ∨ (operator = 2 ∧ current.technology = true))
    | .issue _ debtor creditor quantity => decide
        (debtor = 1 ∧ creditor = 2 ∧
          ((quantity = 7 ∧ current.claims () 1 2 = 0) ∨
           (quantity = 3 ∧ current.claims () 1 2 = 7)))
    | .transfer sender recipient goods => decide
        ((sender = 2 ∧ recipient = 1 ∧
          ((goods = [(.service, 7)] ∧ current.claims () 1 2 = 7) ∨
           (goods = [(.service, 3)] ∧ current.claims () 1 2 = 10) ∨ goods = [(.feedstock, 1)])) ∨
         (sender = 1 ∧ recipient = 2 ∧ goods = [(.waste, 1)]))
    | _ => true)

def scope : Delegation.Jurisdiction Party Good Port :=
  ⟨task, .service, .challenge, by decide, [(.service, 1)]⟩

def law := Delegation.law base scope
def position : Position Party Unit := ⟨(), 1, 2⟩
def route : Route Party Good := ⟨2, .waste, .feedstock⟩

def initial (resources : Resources) : Current where
  stock := fun person good =>
    if person = 2 ∧ good = .service then 10
    else if person = 1 ∧ good = .feedstock then 3
    else if person = 1 ∧ (good = .energy ∨ good = .labor) then 4
    else if person = 2 ∧ good = .energy then resources.energy
    else if person = 2 ∧ good = .labor then resources.labor else 0
  claims := fun _ _ _ => 0
  technology := (resources.willing, some 0)
  clock := 0
  round := 0

def issue (quantity : ℚ) : RequestAt := ⟨1, [], .reserve 1, [], .issue () 1 2 quantity⟩
def payout (quantity : ℚ) : RequestAt := ⟨2, [], .reserve 2, [], .transfer 2 1 [(.service, quantity)]⟩
def oldUse : RequestAt := ⟨1, [], .reserve 1, [], .use 1 [(.service, 7)] .investment⟩
def oldRequest : RequestAt := ⟨1, [], .service, [.service], .present⟩
def necessity : RequestAt := ⟨1, [], .service, [.service], .use 1 [(.service, 1)] .necessity⟩
def maintenance : RequestAt := ⟨1, [], .service, [.service], .use 1 [(.service, 1)] .maintenance⟩

def alphabet (current : Current) : List RequestAt :=
  [issue 3, payout 3] ++ (Delegation.members task).eraseDups.map (Delegation.revokeRequest scope current) ++
    [necessity, maintenance]

def sourceWith (resources : Resources) : OutstandingSource Party Good Port (Bool × Option Party) Unit where
  seed := {
    law := law
    initial := initial resources
    task := task
    actionsAt := alphabet
    budget := 5
    original := [issue 7, payout 7, oldUse, oldRequest]
    refused := by
      let before := law.next (initial resources) []
      let endOfPrefix := law.step (law.step (law.step before (issue 7)) (payout 7)) oldUse
      refine ⟨⟨3, endOfPrefix, oldRequest⟩, ?_, ?_⟩
      · change _ ∈ (law.execute before 0 [issue 7, payout 7, oldUse, oldRequest]).items
        simp only [RawLaw.execute, List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · have technology : endOfPrefix.technology = (resources.willing, some 0) := by
          have keepIssue (current : Current) : (law.step current (issue 7)).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          have keepPayout (current : Current) : (law.step current (payout 7)).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          have keepUse (current : Current) : (law.step current oldUse).technology = current.technology := by
            unfold RawLaw.step
            split <;> rfl
          change (law.step (law.step (law.step before (issue 7)) (payout 7)) oldUse).technology = _
          rw [keepUse, keepPayout, keepIssue]
          rfl
        intro accepted
        have required : Port.service ∈ law.requiredPorts endOfPrefix oldRequest := by
          simp [RawLaw.requiredPorts, RawLaw.debit, oldRequest]
        have guard := accepted.2.1 Port.service required
        have denied : law.allowed endOfPrefix.technology Port.service (1 : Party) = false := by
          rw [technology]
          rfl
        rcases guard with direct | consent
        · change law.allowed endOfPrefix.technology Port.service (1 : Party) = true at direct
          rw [denied] at direct
          cases direct
        · change _ ∈ ([] : List Party) at consent
          exact List.not_mem_nil consent }
  positive := by
    intro slot inside
    simp only [task, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> exact ⟨(.service, 1), by decide, by decide⟩
  completionReport := fun current => .original current (produce law position route current).word

def resources : Resources := ⟨1, 1, true⟩
def source := sourceWith resources
def noEnergySource := sourceWith ⟨0, 1, true⟩
def noLaborSource := sourceWith ⟨1, 0, true⟩
def refusingSource := sourceWith ⟨1, 1, false⟩

abbrev originalRoot := OutstandingSource.NativeService.Runtime.root source
abbrev originalFacade := OutstandingSource.NativeService.Runtime.facade source

theorem zero_financial_genesis (supply : Resources) :
    (sourceWith supply).input.initial.claims = fun _ _ _ => 0 := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery
