import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecyclingBudget
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Law
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumMaterial
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)

abbrev Current := RawCurrent Party Good (Mandate.State Party Bool) Unit
abbrev Action := Request Party Good Port (Mandate.State Party Bool) Unit
abbrev law := Mandate.law Repayment.Recovery.base Repayment.Recovery.scope
abbrev waste : Action := ⟨1,[],.reserve 1,[],.transfer 1 2 [(.waste,1)]⟩
abbrev recycle : Action := ⟨2,[],.reserve 2,[],.produce 2⟩
abbrev feed : Action := ⟨2,[],.reserve 2,[],.transfer 2 1 [(.feedstock,1)]⟩
abbrev production : Action := ⟨1,[],.reserve 1,[],.produce 1⟩
abbrev word : List Action := [waste,recycle,feed,production]
abbrev phase1 (current : Current) := law.paidStep current waste
abbrev phase2 (current : Current) := law.paidStep (phase1 current) recycle
abbrev phase3 (current : Current) := law.paidStep (phase2 current) feed

-- This is the original material carrier under the new source's explicit mandate state.
def material (current : Current) : Repayment.Recovery.Current :=
  ⟨current.stock,current.claims,(current.technology.technology,current.technology.holder),current.clock,current.round⟩
abbrev Inputs (current : Current) := RecyclingLaw.Inputs (material current)

set_option linter.unusedSimpArgs false in
theorem every_recycling_phase_is_paid_at_its_actual_prefix
    (current : Current) (inputs : Inputs current) :
    law.Valid current waste ∧ law.Valid (phase1 current) recycle ∧
      law.Valid (phase2 current) feed ∧ law.Valid (phase3 current) production := by
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := inputs
  simp only [material] at pf wf ww willing stock pe pl we wl
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    phase1,phase2,phase3,waste,recycle,feed,production,RawLaw.paidStep,law,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    flowAt,locate,amount,willing,stock,pe,pl,we,wl,wf,ww,pf]

def successor (current : Current) : Current :=
  {current with
    stock := fun party good => current.stock party good +
      (if party = 1 ∧ good = .service then 3 else 0) -
      (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then 1 else 0)
    clock := current.clock + 1
    round := current.round + 1}

set_option linter.unusedSimpArgs false in
theorem actual_recycling_retains_material_and_pays_both_workers
    (current : Current) (inputs : Inputs current) : law.next current word = successor current := by
  obtain ⟨v0,v1,v2,v3⟩ := every_recycling_phase_is_paid_at_its_actual_prefix current inputs
  simp only [word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos v0]
  change { (law.step (law.step (law.step (phase1 current) recycle) feed) production) with
    clock := current.clock + 1,round := current.round + 1} = successor current
  simp only [RawLaw.step,if_pos v1,if_pos v2,if_pos v3]
  apply RawCurrent.ext
  · funext party good
    fin_cases party <;> cases good <;>
      simp [successor,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,phase1,phase2,phase3,
        waste,recycle,feed,production,law,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount]
  all_goals rfl

theorem every_actual_recycling_item_is_paid (current : Current) (inputs : Inputs current) :
    ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  obtain ⟨v0,v1,v2,v3⟩ := every_recycling_phase_is_paid_at_its_actual_prefix current inputs
  intro item member
  simp only [RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,if_pos v2,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact v0
  · exact v1
  · exact v2
  · exact v3

theorem original_material_commutes_at_the_actual_recycling_boundary
    (current : Current) (inputs : Inputs current) :
    material (law.next current word) = Repayment.Recovery.law.next (material current) RecyclingLaw.word := by
  rw [actual_recycling_retains_material_and_pays_both_workers current inputs,
    RecyclingLaw.actualNext (material current) inputs]
  rfl

def run (current : Current) (count : Nat) : Current :=
  Nat.rec (fun state : Current => state)
    (fun _ previous state => previous (law.next state word)) count current

theorem original_resource_reserve_funds_all_local_recycling_cycles
    (current : Current) (count : Nat) (reserve : RecyclingBudget.Reserve (material current) count) :
    material (run current count) = RecyclingBudget.run (material current) count ∧
      ∀ step, step < count → ∀ item ∈ law.rawItems (run current step) word,
        law.Valid item.before item.request := by
  induction count generalizing current with
  | zero => exact ⟨rfl,by intro step bound;omega⟩
  | succ count ih =>
    have inputs := RecyclingBudget.currentInputs (material current) count reserve
    have same := original_material_commutes_at_the_actual_recycling_boundary current inputs
    have next : RecyclingBudget.Reserve (material (law.next current word)) count := by
      rw [same]
      exact RecyclingBudget.nextReserve (material current) count reserve
    have tail := ih (law.next current word) next
    refine ⟨?_,?_⟩
    · change material (run (law.next current word) count) = _
      rw [tail.1,same]
      rfl
    · intro step bound
      cases step with
      | zero => exact every_actual_recycling_item_is_paid current inputs
      | succ step => exact tail.2 step (by omega)

theorem actual_input_stocks_generate_the_complete_local_recycling_capacity
    (current : Current) (inputs : Inputs current) :
    material (run current (RecyclingBudget.capacity (material current))) =
        RecyclingBudget.expected (material current) (RecyclingBudget.capacity (material current)) ∧
      ∀ step, step < RecyclingBudget.capacity (material current) →
        ∀ item ∈ law.rawItems (run current step) word, law.Valid item.before item.request := by
  have reserve := RecyclingBudget.sourceCapacity (material current) inputs
  have generated := original_resource_reserve_funds_all_local_recycling_cycles current _ reserve.2
  exact ⟨generated.1.trans (RecyclingBudget.allFundedCycles (material current) _ reserve.2).1,generated.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumMaterial
