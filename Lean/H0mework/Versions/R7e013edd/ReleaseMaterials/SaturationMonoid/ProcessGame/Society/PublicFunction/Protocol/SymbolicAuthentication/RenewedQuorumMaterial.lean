import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecycledQuorumMaterial
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResupplyLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumMaterial
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party Port)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)

-- The supplier's recipe and transfer permission are present in this law from genesis.
def base : RawLaw Party Good Port Bool Unit := { Repayment.Recovery.base with
  technique := fun technology operator => if operator = 0 then
      ⟨[(.feedstock,1)],[(.energy,2),(.labor,3)],[(.labor,1)],[.reserve 0]⟩
    else Repayment.Recovery.base.technique technology operator
  policy := .opaque fun current request =>
    Repayment.Recovery.base.operationAllowed current request ||
      (decide (request.signer = 0) && current.technology && match request.operation with
        | .produce operator => decide (operator = 0)
        | .transfer sender recipient goods => decide
            (sender = 0 ∧ (recipient = 1 ∨ recipient = 2) ∧ goods = [(.energy,1),(.labor,1)])
        | _ => false) }
abbrev law := Mandate.law base Repayment.Recovery.scope
abbrev renew : Action := ⟨0,[],.reserve 0,[],.produce 0⟩
abbrev give (recipient : Party) : Action :=
  ⟨0,[],.reserve 0,[],.transfer 0 recipient [(.energy,1),(.labor,1)]⟩
abbrev supply : List Action := [renew,give 1,give 2]
abbrev word : List Action := supply ++ RecycledQuorumMaterial.word

structure Inputs (current : Current) : Prop where
  material : ResupplyLaw.Restorable (material current)
  fuel : 1 ≤ current.stock 0 .feedstock
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy

instance (current : Current) : Decidable (Inputs current) :=
  decidable_of_iff (ResupplyLaw.Restorable (material current) ∧
    1 ≤ current.stock 0 .feedstock ∧ 1 ≤ current.stock 0 .labor ∧ 0 ≤ current.stock 0 .energy)
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
      fun h => ⟨h.material,h.fuel,h.labor,h.energy⟩⟩

def supplied (current : Current) : Current := {current with
  stock := fun party good => current.stock party good -
    (if party = 0 ∧ good = .feedstock then 1 else 0) +
    (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then 1 else 0) }

set_option linter.unusedSimpArgs false in
theorem supply_phases (current : Current) (inputs : Inputs current) :
    law.Valid current renew ∧
      law.Valid (law.paidStep current renew) (give 1) ∧
      law.Valid (law.paidStep (law.paidStep current renew) (give 1)) (give 2) := by
  have fuel := inputs.fuel
  have labor := inputs.labor
  have energy := inputs.energy
  have willing := inputs.material.willing
  change current.technology.technology = true at willing
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    renew,give,RawLaw.paidStep,law,base,Mandate.law,Mandate.eraseCurrent,
    Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    flowAt,locate,amount,willing,fuel,labor,energy]
  all_goals repeat' constructor
  all_goals linarith

set_option linter.unusedSimpArgs false in
theorem actual_supply (current : Current) (inputs : Inputs current) :
    (law.execute current 0 supply).final = supplied current ∧
    (∀ item ∈ law.rawItems current supply, law.Valid item.before item.request) := by
  obtain ⟨v0,v1,v2⟩ := supply_phases current inputs
  constructor
  · simp only [supply,RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,if_pos v2]
    apply RawCurrent.ext
    · funext party good
      fin_cases party <;> cases good <;>
        simp [supplied,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,renew,give,
          law,Mandate.law,base,flowAt,locate,amount] <;> ring
    all_goals rfl
  · intro item member
    simp only [RawLaw.rawItems,supply,RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2

abbrev waste := RecycledQuorumMaterial.waste
abbrev recycle := RecycledQuorumMaterial.recycle
abbrev feed := RecycledQuorumMaterial.feed
abbrev production := RecycledQuorumMaterial.production
abbrev phase1 (current : Current) := law.paidStep current waste
abbrev phase2 (current : Current) := law.paidStep (phase1 current) recycle
abbrev phase3 (current : Current) := law.paidStep (phase2 current) feed

set_option linter.unusedSimpArgs false in
theorem recycling_phases
    (current : Current) (inputs : RecycledQuorumMaterial.Inputs current) :
    law.Valid current waste ∧ law.Valid (phase1 current) recycle ∧
      law.Valid (phase2 current) feed ∧ law.Valid (phase3 current) production := by
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := inputs
  simp only [material] at pf wf ww willing stock pe pl we wl
  simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
    RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,NonnegativeBundle,
    phase1,phase2,phase3,waste,recycle,feed,production,RawLaw.paidStep,law,base,
    Mandate.law,Mandate.eraseCurrent,Mandate.eraseRequest,Mandate.eraseOperation,Mandate.TaskUse,
    Repayment.Recovery.base,Repayment.Recovery.scope,Repayment.Recovery.task,
    flowAt,locate,amount,willing,stock,pe,pl,we,wl,wf,ww,pf]

def recycled (current : Current) : Current :=
  {current with
    stock := fun party good => current.stock party good +
      (if party = 1 ∧ good = .service then 3 else 0) -
      (if (party = 1 ∨ party = 2) ∧ (good = .energy ∨ good = .labor) then 1 else 0)
    clock := current.clock + 1
    round := current.round + 1}

set_option linter.unusedSimpArgs false in
theorem recycling_next
    (current : Current) (inputs : RecycledQuorumMaterial.Inputs current) : law.next current RecycledQuorumMaterial.word = recycled current := by
  obtain ⟨v0,v1,v2,v3⟩ := recycling_phases current inputs
  simp only [RecycledQuorumMaterial.word,RawLaw.next,RawLaw.execute,RawLaw.step,if_pos v0]
  change { (law.step (law.step (law.step (phase1 current) recycle) feed) production) with
    clock := current.clock + 1,round := current.round + 1} = recycled current
  simp only [RawLaw.step,if_pos v1,if_pos v2,if_pos v3]
  apply RawCurrent.ext
  · funext party good
    fin_cases party <;> cases good <;>
      simp [recycled,RawLaw.paidStep,RawLaw.debit,RawLaw.credit,phase1,phase2,phase3,
        waste,recycle,feed,production,law,base,Mandate.law,Repayment.Recovery.base,flowAt,locate,amount]
  all_goals rfl

theorem recycling_items (current : Current) (inputs : RecycledQuorumMaterial.Inputs current) :
    ∀ item ∈ law.rawItems current RecycledQuorumMaterial.word, law.Valid item.before item.request := by
  obtain ⟨v0,v1,v2,v3⟩ := recycling_phases current inputs
  intro item member
  simp only [RawLaw.rawItems,RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,if_pos v2,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact v0
  · exact v1
  · exact v2
  · exact v3


theorem supply_restores (current : Current) (inputs : Inputs current) :
    RecycledQuorumMaterial.Inputs (supplied current) := by
  obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := inputs.material
  constructor <;> simp_all [material,supplied]

def successor (current : Current) : Current := {current with
  stock := fun party good => current.stock party good -
    (if party = 0 ∧ good = .feedstock then 1 else 0) +
    (if party = 1 ∧ good = .service then 3 else 0)
  clock := current.clock + 1
  round := current.round + 1 }

set_option linter.unusedSimpArgs false in
theorem actual_next (current : Current) (inputs : Inputs current) :
    law.next current word = successor current := by
  have suppliedEq := (actual_supply current inputs).1
  have same : law.next current word = law.next (supplied current) RecycledQuorumMaterial.word := by
    simp only [word,RawLaw.next,RawLaw.execute_append,suppliedEq]
    have finalIndex : ∀ index, (law.execute (supplied current) index RecycledQuorumMaterial.word).final =
        (law.execute (supplied current) 0 RecycledQuorumMaterial.word).final := by
      intro index
      simp [RecycledQuorumMaterial.word,RawLaw.execute]
    simp only [finalIndex]
    rfl
  rw [same,recycling_next (supplied current) (supply_restores current inputs)]
  apply RawCurrent.ext
  · funext party good
    by_cases first : party = 1 <;> by_cases second : party = 2 <;> cases good <;>
      simp [successor,recycled,supplied,first,second]
  all_goals rfl

set_option linter.unusedSimpArgs false in
theorem actual_items (current : Current) (inputs : Inputs current) :
    ∀ item ∈ law.rawItems current word, law.Valid item.before item.request := by
  obtain ⟨v0,v1,v2⟩ := supply_phases current inputs
  have suppliedEq := (actual_supply current inputs).1
  simp only [supply,RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,if_pos v2] at suppliedEq
  obtain ⟨w0,w1,w2,w3⟩ := recycling_phases (supplied current) (supply_restores current inputs)
  intro item member
  change item ∈ (law.execute current 0 [renew,give 1,give 2,waste,recycle,feed,production]).items at member
  simp only [RawLaw.execute,RawLaw.step,if_pos v0,if_pos v1,if_pos v2,suppliedEq,
    if_pos w0,if_pos w1,if_pos w2,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact v0
  · exact v1
  · exact v2
  · exact w0
  · exact w1
  · exact w2
  · exact w3

structure Reserve (current : Current) (count : Nat) : Prop where
  material : ResupplyLaw.Restorable (material current)
  fuel : (count : ℚ) ≤ current.stock 0 .feedstock
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy

def capacity (current : Current) : Nat := ⌊current.stock 0 .feedstock⌋₊
def run (current : Current) (count : Nat) : Current :=
  Nat.rec (fun state : Current => state)
    (fun _ previous state => previous (law.next state word)) count current

def expected (current : Current) (count : Nat) : Current := {current with
  stock := fun party good => current.stock party good -
    (if party = 0 ∧ good = .feedstock then count else 0) +
    (if party = 1 ∧ good = .service then 3 * count else 0)
  clock := current.clock + count
  round := current.round + count }

theorem reserve_inputs (current : Current) (count : Nat) (reserve : Reserve current (count + 1)) :
    Inputs current := by
  have positive : (1 : ℚ) ≤ (count + 1 : Nat) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le count)
  exact ⟨reserve.material,positive.trans reserve.fuel,reserve.labor,reserve.energy⟩

theorem next_reserve (current : Current) (count : Nat) (reserve : Reserve current (count + 1)) :
    Reserve (law.next current word) count := by
  rw [actual_next current (reserve_inputs current count reserve)]
  refine ⟨?_,?_,?_,?_⟩
  · obtain ⟨pf,wf,ww,willing,stock,pe,pl,we,wl⟩ := reserve.material
    constructor <;> simp_all [material,successor]
  · have fuel := reserve.fuel
    simp [successor,Nat.cast_add] at fuel ⊢
    linarith
  · simpa [successor] using reserve.labor
  · simpa [successor] using reserve.energy

theorem all_funded_cycles (current : Current) (count : Nat) (reserve : Reserve current count) :
    run current count = expected current count ∧
      ∀ step, step < count → ∀ item ∈ law.rawItems (run current step) word,
        law.Valid item.before item.request := by
  induction count generalizing current with
  | zero =>
    refine ⟨?_,by intro step bound;omega⟩
    apply RawCurrent.ext
    · funext party good;simp [run,expected]
    all_goals simp [run,expected]
  | succ count ih =>
    have input := reserve_inputs current count reserve
    have tail := ih (law.next current word) (next_reserve current count reserve)
    refine ⟨?_,?_⟩
    · change run (law.next current word) count = _
      rw [tail.1,actual_next current input]
      apply RawCurrent.ext
      · funext party good
        by_cases first : party = 1 <;> by_cases supplier : party = 0 <;> cases good <;>
          simp [expected,successor,first,supplier,Nat.cast_add,Nat.cast_one] <;> ring
      · rfl
      · rfl
      · simp [expected,successor,Nat.cast_add];ring
      · simp [expected,successor];omega
    · intro step bound
      cases step with
      | zero => exact actual_items current input
      | succ step => exact tail.2 step (by omega)

theorem actual_fuel_generates_the_complete_renewed_service_budget
    (current : Current) (resources : Reserve current 0) :
    run current (capacity current) = expected current (capacity current) ∧
      ∀ step, step < capacity current → ∀ item ∈ law.rawItems (run current step) word,
        law.Valid item.before item.request := by
  apply all_funded_cycles
  exact ⟨resources.material,Nat.floor_le resources.fuel,resources.labor,resources.energy⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumMaterial
