import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Recovery.Source
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingLaw
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority
open Repayment.Recovery (Good Current law base scope position route)

abbrev Action := Repayment.Recovery.RequestAt
abbrev waste : Action := ⟨1, [], .reserve 1, [], .transfer 1 2 [(.waste,1)]⟩
abbrev recycle : Action := ⟨2, [], .reserve 2, [], .produce 2⟩
abbrev feed : Action := ⟨2, [], .reserve 2, [], .transfer 2 1 [(.feedstock,1)]⟩
abbrev produce : Action := ⟨1, [], .reserve 1, [], .produce 1⟩
abbrev word : List Action := [waste, recycle, feed, produce]
abbrev phase1 (current : Current) := law.paidStep current waste
abbrev phase2 (current : Current) := law.paidStep (phase1 current) recycle
abbrev phase3 (current : Current) := law.paidStep (phase2 current) feed

structure Inputs (current : Current) : Prop where
  producerFeed : 0 ≤ current.stock 1 .feedstock
  workerFeed : 0 ≤ current.stock 2 .feedstock
  workerWaste : 0 ≤ current.stock 2 .waste
  willing : current.technology.1 = true
  waste : 1 ≤ current.stock 1 .waste
  producerEnergy : 1 ≤ current.stock 1 .energy
  producerLabor : 1 ≤ current.stock 1 .labor
  workerEnergy : 1 ≤ current.stock 2 .energy
  workerLabor : 1 ≤ current.stock 2 .labor

-- These are the existing source's four primitive requests, each paid at its own actual prefix.
theorem sourceWord (current : Current) : word =
    Repayment.Recovery.repairWord law position route current ++ [Repayment.production law position current] := rfl

set_option linter.unusedSimpArgs false in
theorem validPhases (current : Current) (inputs : Inputs current) :
    law.Valid current waste ∧ law.Valid (phase1 current) recycle ∧
      law.Valid (phase2 current) feed ∧ law.Valid (phase3 current) produce := by
  have willing := inputs.willing
  have material := inputs.waste
  have producerEnergy := inputs.producerEnergy
  have producerLabor := inputs.producerLabor
  have workerEnergy := inputs.workerEnergy
  have workerLabor := inputs.workerLabor
  have wf := inputs.workerFeed
  have ww := inputs.workerWaste
  have pf := inputs.producerFeed
  simp [RawLaw.Valid, RawLaw.SignerMatches, RawLaw.operationAllowed, RawPolicy.eval,
    RawLaw.requiredPorts, RawLaw.debit, RawLaw.credit, RawLaw.ClaimGuard, NonnegativeBundle,
    phase1, phase2, phase3, waste, recycle, feed, produce, RawLaw.paidStep,
    law, Delegation.law, LawExtension.eraseCurrent, LawExtension.eraseRequest, LawExtension.eraseOperation,
    Repayment.Recovery.law, Repayment.Recovery.base, Repayment.Recovery.scope,
    Repayment.Recovery.task, flowAt, locate, amount, willing, material, producerEnergy, producerLabor, workerEnergy, workerLabor, wf, ww, pf]

def successor (current : Current) : Current :=
  {current with
    stock := fun party good => current.stock party good +
      (if party = 1 ∧ good = .service then 3 else 0) -
      (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then 1 else 0)
    clock := current.clock + 1
    round := current.round + 1}

set_option linter.unusedSimpArgs false in
theorem actualNext (current : Current) (inputs : Inputs current) :
    law.next current word = successor current := by
  obtain ⟨v0,v1,v2,v3⟩ := validPhases current inputs
  simp only [word, RawLaw.next, RawLaw.execute, RawLaw.step, if_pos v0]
  change { (law.step (law.step (law.step (phase1 current) recycle) feed) produce) with
    clock := current.clock + 1, round := current.round + 1} = successor current
  simp only [RawLaw.step, if_pos v1, if_pos v2, if_pos v3]
  apply RawCurrent.ext
  · funext party good
    by_cases first : party = 1
    · subst party
      have second : (1 : Party) ≠ 2 := by decide
      have ne1 : (1 : Party) = 1 := rfl
      have ne2 : (2 : Party) ≠ 1 := by decide
      cases good <;>
      simp [successor, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
        phase1, phase2, phase3, waste, recycle, feed, produce, law, Delegation.law,
        Repayment.Recovery.law, Repayment.Recovery.base, LawExtension.eraseCurrent,
        LawExtension.eraseRequest, LawExtension.eraseOperation, flowAt, locate, amount,
        second, ne1, ne2]
    · by_cases second : party = 2
      · subst party
        have ne1 : (1 : Party) ≠ 2 := by decide
        have ne2 : (2 : Party) = 2 := rfl
        cases good <;>
        simp [successor, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
        phase1, phase2, phase3, waste, recycle, feed, produce, law, Delegation.law,
        Repayment.Recovery.law, Repayment.Recovery.base, LawExtension.eraseCurrent,
        LawExtension.eraseRequest, LawExtension.eraseOperation, flowAt, locate, amount,
        first, ne1, ne2]
      · have ne1 : (1 : Party) ≠ party := Ne.symm first
        have ne2 : (2 : Party) ≠ party := Ne.symm second
        cases good <;>
        simp [successor, RawLaw.paidStep, RawLaw.debit, RawLaw.credit,
        phase1, phase2, phase3, waste, recycle, feed, produce, law, Delegation.law,
        Repayment.Recovery.law, Repayment.Recovery.base, LawExtension.eraseCurrent,
        LawExtension.eraseRequest, LawExtension.eraseOperation, flowAt, locate, amount,
        first, second, ne1, ne2]
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem actualItems (current : Current) (inputs : Inputs current) :
    ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  obtain ⟨v0,v1,v2,v3⟩ := validPhases current inputs
  intro item member
  simp only [RawLaw.rawItems, word, RawLaw.execute, RawLaw.step, if_pos v0, if_pos v1, if_pos v2,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact v0
  · exact v1
  · exact v2
  · exact v3

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingLaw
