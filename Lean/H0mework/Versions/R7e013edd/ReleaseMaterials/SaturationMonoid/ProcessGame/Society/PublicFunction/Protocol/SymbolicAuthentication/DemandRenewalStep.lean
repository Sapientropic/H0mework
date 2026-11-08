import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ResidualFeeLaw

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalStep
open Institutions.Capitalism.Universal.Source.Program
open Delegation.Funded (Party)
open Repayment.Recovery (Good)
open RecycledQuorumMaterial (Current Action material)
open RenewedQuorumMaterial (law)
open RenewedQuorumSource (fee)

structure Inventory (current : Current) (cash fuel : Nat) : Prop where
  material : ResupplyLaw.Restorable (material current)
  cash : current.stock 1 .service = cash
  fuel : current.stock 0 .feedstock = fuel
  labor : 1 ≤ current.stock 0 .labor
  energy : 0 ≤ current.stock 0 .energy

def refill (current : Current) : Bool :=
  decide (current.stock 1 .service < 1 ∧ RenewedQuorumMaterial.Inputs current)

def prepared (current : Current) : Current :=
  if refill current then law.next current RenewedQuorumMaterial.word else current

def words (current : Current) (second : Bool) : List (List Action) :=
  (if refill current then [RenewedQuorumMaterial.word] else []) ++ [[fee second]]

def next (current : Current) (second : Bool) : Current :=
  law.next (prepared current) [fee second]

def paid (current : Current) : Bool := decide (1 ≤ (prepared current).stock 1 .service)

theorem the_generated_words_execute_their_literal_next (current : Current) (second : Bool) :
    (words current second).foldl law.next current = next current second := by
  unfold words next prepared
  cases refill current <;> rfl

set_option linter.unusedSimpArgs false in
theorem fee_valid_iff (current : Current) (second : Bool) :
    law.Valid current (fee second) ↔ 1 ≤ current.stock 1 .service := by
  cases second <;>
    simp [RawLaw.Valid,RawLaw.SignerMatches,RawLaw.operationAllowed,RawPolicy.eval,
      RawLaw.requiredPorts,RawLaw.debit,RawLaw.credit,RawLaw.ClaimGuard,fee,law,
      RenewedQuorumMaterial.base,Mandate.law,Mandate.TaskUse,Mandate.eraseCurrent,
      Mandate.eraseRequest,Mandate.eraseOperation,Repayment.Recovery.base,
      Repayment.Recovery.scope,Repayment.Recovery.task,NonnegativeBundle,flowAt,locate,amount]

theorem a_paid_step_has_only_actual_valid_items (current : Current) (second : Bool)
    (accepted : paid current = true) :
    (∀ item ∈ law.rawItems (prepared current) [fee second], law.Valid item.before item.request) ∧
      (refill current = true → ∀ item ∈ law.rawItems current RenewedQuorumMaterial.word,
        law.Valid item.before item.request) := by
  constructor
  · exact ResidualFeeLaw.original_fee_items (prepared current) second (of_decide_eq_true accepted)
  · intro generated
    exact RenewedQuorumMaterial.actual_items current (of_decide_eq_true generated).2

theorem an_unpaid_step_really_attempts_and_refuses_the_original_fee
    (current : Current) (second : Bool) (unpaid : paid current = false) :
    ¬ law.Valid (prepared current) (fee second) ∧
      ⟨0,prepared current,fee second⟩ ∈ law.rawItems (prepared current) [fee second] := by
  refine ⟨?_,by simp [RawLaw.rawItems,RawLaw.execute]⟩
  rw [fee_valid_iff]
  exact of_decide_eq_false unpaid

set_option linter.unusedSimpArgs false in
theorem fee_preserves_inventory (current : Current) (cash fuel : Nat) (second : Bool)
    (stock : Inventory current (cash + 1) fuel) :
    Inventory (law.next current [fee second]) cash fuel := by
  have funded : 1 ≤ current.stock 1 .service := by rw [stock.cash];norm_num
  have balance := ResidualFeeLaw.fee_stock current second funded
  have valid := (fee_valid_iff current second).mpr funded
  have technology : (law.next current [fee second]).technology = current.technology := by
    simp only [RawLaw.next,RawLaw.execute,RawLaw.step,if_pos valid]
    rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨pf,wf,ww,willing,waste,pe,pl,we,wl⟩ := stock.material
    constructor <;> simp only [material] at *
    all_goals first | simpa only [technology] using willing | simpa [balance] using pf |
      simpa [balance] using wf | simpa [balance] using ww | simpa [balance] using waste |
      simpa [balance] using pe | simpa [balance] using pl | simpa [balance] using we | simpa [balance] using wl
  · rw [balance,stock.cash];norm_num
  · simpa [balance] using stock.fuel
  · simpa [balance] using stock.labor
  · simpa [balance] using stock.energy

theorem renewal_preserves_inventory (current : Current) (cash fuel : Nat)
    (stock : Inventory current cash (fuel + 1)) :
    Inventory (law.next current RenewedQuorumMaterial.word) (cash + 3) fuel := by
  have ready : RenewedQuorumMaterial.Inputs current :=
    ⟨stock.material,by rw [stock.fuel];norm_num,stock.labor,stock.energy⟩
  rw [RenewedQuorumMaterial.actual_next current ready]
  refine ⟨?_,?_,?_,?_,?_⟩
  · obtain ⟨pf,wf,ww,willing,waste,pe,pl,we,wl⟩ := stock.material
    constructor <;> simp_all [material,RenewedQuorumMaterial.successor]
  · simp [RenewedQuorumMaterial.successor,stock.cash,Nat.cast_add]
  · simp [RenewedQuorumMaterial.successor,stock.fuel,Nat.cast_add]
  · simpa [RenewedQuorumMaterial.successor] using stock.labor
  · simpa [RenewedQuorumMaterial.successor] using stock.energy

theorem actual_resources_generate_a_paid_step_and_the_smaller_budget
    (current : Current) (cash fuel : Nat) (second : Bool)
    (stock : Inventory current cash fuel) (positive : 0 < cash + 3 * fuel) :
    paid current = true ∧ ∃ cash' fuel', Inventory (next current second) cash' fuel' ∧
      cash' + 3 * fuel' + 1 = cash + 3 * fuel := by
  cases cash with
  | succ cash =>
    have noRefill : refill current = false := by
      unfold refill
      rw [stock.cash]
      simp
    have before : prepared current = current := by simp [prepared,noRefill]
    refine ⟨?_,cash,fuel,?_,by omega⟩
    · simp [paid,before,stock.cash]
    · simpa only [next,before] using fee_preserves_inventory current cash fuel second stock
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have inputs : RenewedQuorumMaterial.Inputs current :=
        ⟨stock.material,by rw [stock.fuel];norm_num,stock.labor,stock.energy⟩
      have yesRefill : refill current = true := by simp [refill,stock.cash,inputs]
      have before : prepared current = law.next current RenewedQuorumMaterial.word := by simp [prepared,yesRefill]
      have renewed := renewal_preserves_inventory current 0 fuel stock
      refine ⟨?_,2,fuel,?_,by omega⟩
      · unfold paid
        rw [before,renewed.cash]
        decide
      · simpa only [next,before] using fee_preserves_inventory _ 2 fuel second renewed

theorem exhausted_resources_generate_a_real_refusal (current : Current)
    (stock : Inventory current 0 0) : paid current = false := by
  have impossible : ¬ RenewedQuorumMaterial.Inputs current := by
    intro inputs
    have fuel := inputs.fuel
    rw [stock.fuel] at fuel
    norm_num at fuel
  simp [paid,prepared,refill,stock.cash,impossible]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalStep
