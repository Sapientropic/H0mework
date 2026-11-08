import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingBudget
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResupplyLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good Current)
abbrev Action := Repayment.Recovery.RequestAt

-- Supply extends admission, not the original recipes or their material effects.
def law (released : Bool) : RawLaw Party Good Port (Bool × Option Party) Unit := { Repayment.Recovery.law with
  policy := .opaque (fun current request =>
    Repayment.Recovery.law.operationAllowed current request ||
      (released && decide (request.signer = 0) && match request.operation with
        | .transfer sender recipient goods => decide
            (sender = 0 ∧ (recipient = 1 ∨ recipient = 2) ∧ goods = [(.energy,1),(.labor,1)])
        | _ => false)) }

abbrev give (recipient : Party) : Action :=
  ⟨0, [], .reserve 0, [], .transfer 0 recipient [(.energy,1),(.labor,1)]⟩
abbrev word : List Action := [give 1, give 2]
abbrev first (current : Current) := (law true).paidStep current (give 1)

theorem oldValid (released : Bool) (current : Current) (request : Action)
    (accepted : Repayment.Recovery.law.Valid current request) :
    (law released).Valid current request := by
  obtain ⟨⟨signer,policy⟩,ports,claims,debit,credit,stock⟩ := accepted
  exact ⟨⟨signer,by
      change (Repayment.Recovery.law.operationAllowed current request || _) = true
      exact Bool.or_eq_true_iff.mpr (Or.inl policy)⟩,
    ports,claims,debit,credit,stock⟩

structure Funding (current : Current) : Prop where
  energy : 2 ≤ current.stock 0 .energy
  labor : 2 ≤ current.stock 0 .labor

instance (current : Current) : Decidable (Funding current) :=
  decidable_of_iff (2 ≤ current.stock 0 .energy ∧ 2 ≤ current.stock 0 .labor)
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.energy,h.labor⟩⟩

set_option linter.unusedSimpArgs false in
theorem fundedPhases (current : Current) (funded : Funding current) :
    (law true).Valid current (give 1) ∧ (law true).Valid (first current) (give 2) := by
  have energy := funded.energy
  have labor := funded.labor
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    law,give,first,RawLaw.paidStep,Repayment.Recovery.law,Delegation.law,
    Repayment.Recovery.base,Repayment.Recovery.scope,flowAt,locate,amount]
  all_goals repeat' constructor
  all_goals linarith

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good +
    (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then 1 else 0) -
    (if party = 0 ∧ (good = .energy ∨ good = .labor) then 2 else 0)
  clock := current.clock + 1
  round := current.round + 1 }

set_option linter.unusedSimpArgs false in
theorem actualNext (current : Current) (funded : Funding current) :
    (law true).next current word = successor current := by
  obtain ⟨v0,v1⟩ := fundedPhases current funded
  simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos v0]
  change { ((law true).step (first current) (give 2)) with
    clock := current.clock + 1, round := current.round + 1 } = successor current
  rw [RawLaw.step,if_pos v1]
  apply RawCurrent.ext
  · funext party good
    fin_cases party <;> cases good <;>
      simp [successor,first,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,give,law,flowAt,locate,amount] <;> ring
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem actualItems (current : Current) (funded : Funding current) :
    ∀ item ∈ (law true).rawItems current word, (law true).Valid item.before item.request := by
  obtain ⟨v0,v1⟩ := fundedPhases current funded
  intro item member
  simp only [RawLaw.rawItems,word,RawLaw.execute,RawLaw.step,if_pos v0,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact v0
  · exact v1

set_option linter.unusedSimpArgs false in
theorem originalCycle (released : Bool) (current : Current) (inputs : RecyclingLaw.Inputs current) :
    (law released).next current RecyclingLaw.word = RecyclingLaw.successor current ∧
      ∀ item ∈ (law released).rawItems current RecyclingLaw.word,
        (law released).Valid item.before item.request := by
  obtain ⟨v0,v1,v2,v3⟩ := RecyclingLaw.validPhases current inputs
  have w0 := oldValid released _ _ v0
  have w1 := oldValid released _ _ v1
  have w2 := oldValid released _ _ v2
  have w3 := oldValid released _ _ v3
  change (law released).Valid ((law released).paidStep current RecyclingLaw.waste) RecyclingLaw.recycle at w1
  change (law released).Valid ((law released).paidStep ((law released).paidStep current RecyclingLaw.waste)
    RecyclingLaw.recycle) RecyclingLaw.feed at w2
  change (law released).Valid ((law released).paidStep ((law released).paidStep
    ((law released).paidStep current RecyclingLaw.waste) RecyclingLaw.recycle) RecyclingLaw.feed)
    RecyclingLaw.produce at w3
  constructor
  · have same : (law released).next current RecyclingLaw.word =
        Repayment.Recovery.law.next current RecyclingLaw.word := by
      simp only [RecyclingLaw.word,RawLaw.next,RawLaw.execute,RawLaw.step,
        if_pos w0,if_pos w1,if_pos w2,if_pos w3,if_pos v0,if_pos v1,if_pos v2,if_pos v3]
      rfl
    exact same.trans (RecyclingLaw.actualNext current inputs)
  · intro item member
    simp only [RawLaw.rawItems,RecyclingLaw.word,RawLaw.execute,RawLaw.step,
      if_pos w0,if_pos w1,if_pos w2,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact w0
    · exact w1
    · exact w2
    · exact w3

-- The four recipient reserves are primitive resource conditions, not a repair certificate.
structure Restorable (current : Current) : Prop where
  producerFeed : 0 ≤ current.stock 1 .feedstock
  workerFeed : 0 ≤ current.stock 2 .feedstock
  workerWaste : 0 ≤ current.stock 2 .waste
  willing : current.technology.1 = true
  waste : 1 ≤ current.stock 1 .waste
  producerEnergy : 0 ≤ current.stock 1 .energy
  producerLabor : 0 ≤ current.stock 1 .labor
  workerEnergy : 0 ≤ current.stock 2 .energy
  workerLabor : 0 ≤ current.stock 2 .labor

instance (current : Current) : Decidable (Restorable current) :=
  decidable_of_iff (0 ≤ current.stock 1 .feedstock ∧ 0 ≤ current.stock 2 .feedstock ∧
    0 ≤ current.stock 2 .waste ∧ current.technology.1 = true ∧ 1 ≤ current.stock 1 .waste ∧
    0 ≤ current.stock 1 .energy ∧ 0 ≤ current.stock 1 .labor ∧
    0 ≤ current.stock 2 .energy ∧ 0 ≤ current.stock 2 .labor)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩,
      fun h => ⟨h.producerFeed,h.workerFeed,h.workerWaste,h.willing,h.waste,
        h.producerEnergy,h.producerLabor,h.workerEnergy,h.workerLabor⟩⟩

theorem restores (current : Current) (funded : Funding current) (possible : Restorable current) :
    RecyclingLaw.Inputs ((law true).next current word) := by
  rw [actualNext current funded]
  obtain ⟨pf,wf,ww,willing,waste,pe,pl,we,wl⟩ := possible
  constructor <;> simp [successor] <;> assumption

theorem totalResourcesAreTransferred (current : Current) (funded : Funding current)
    (good : Good) :
    ((law true).next current word).stock 0 good +
      ((law true).next current word).stock 1 good +
      ((law true).next current word).stock 2 good =
      current.stock 0 good + current.stock 1 good + current.stock 2 good := by
  rw [actualNext current funded]
  cases good <;> simp [successor] <;> ring

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResupplyLaw
