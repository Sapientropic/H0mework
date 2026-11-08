import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalRun
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewedQuorumConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalConsumer
open Institutions.Capitalism.Universal.Source.Program
open RecycledQuorumMaterial (Current)
open RenewedQuorumMaterial (law)
open RenewedQuorumSource (fee)
open DemandRenewalStep DemandRenewalRun

abbrev original := RenewedQuorumConsumer.current 16

theorem the_original_exhausted_occurrence_supplies_the_primitive_inventory : Inventory original 0 2 := by
  constructor
  · constructor <;> decide +kernel
  all_goals decide +kernel

theorem every_actual_fee_sequence_in_the_source_capacity_is_really_paid
    (demands : List Bool) (within : demands.length ≤ 6) :
    (DemandRenewalRun.run demands original).pending = [] ∧ (DemandRenewalRun.run demands original).served = demands ∧
      (∀ item ∈ items (DemandRenewalRun.run demands original).words original, law.Valid item.before item.request) ∧
      (DemandRenewalRun.run demands original).words.foldl law.next original = (DemandRenewalRun.run demands original).final ∧
      (DemandRenewalRun.run demands original).final.claims = original.claims := by
  obtain ⟨empty,served,trace,_⟩ := the_original_budget_funds_every_demand_in_its_capacity
    demands original 0 2 the_original_exhausted_occurrence_supplies_the_primitive_inventory within
  exact ⟨empty,served,every_generated_item_is_paid original _ trace,
    (every_report_keeps_the_literal_actual_source demands original).1,
    every_report_preserves_all_original_claims demands original⟩

theorem the_whole_actual_material_account_consumes_each_generated_debit_and_credit
    (demands : List Bool) (party : Delegation.Funded.Party) (good : Repayment.Recovery.Good) :
    (DemandRenewalRun.run demands original).final.stock party good +
        law.totalDebit (items (DemandRenewalRun.run demands original).words original) party good =
      original.stock party good + law.totalCredit (items (DemandRenewalRun.run demands original).words original) party good := by
  rw [← (every_report_keeps_the_literal_actual_source demands original).1]
  exact the_entire_actual_material_ledger_balances original _ party good

theorem exhausting_the_original_capacity_really_spends_both_units_of_fuel
    (demands : List Bool) (six : demands.length = 6) :
    (DemandRenewalRun.run demands original).final.stock 0 .feedstock = 0 ∧
      (DemandRenewalRun.run demands original).final.stock 1 .service = 0 ∧
      law.totalDebit (items (DemandRenewalRun.run demands original).words original) 0 .feedstock =
        2 + law.totalCredit (items (DemandRenewalRun.run demands original).words original) 0 .feedstock := by
  obtain ⟨_,_,_,cash,fuel,stock,budget⟩ := the_original_budget_funds_every_demand_in_its_capacity
    demands original 0 2 the_original_exhausted_occurrence_supplies_the_primitive_inventory (by omega)
  have zeroCash : cash = 0 := by omega
  have zeroFuel : fuel = 0 := by omega
  have finalFuel : (DemandRenewalRun.run demands original).final.stock 0 .feedstock = 0 := by simpa only [zeroFuel,Nat.cast_zero] using stock.fuel
  have finalCash : (DemandRenewalRun.run demands original).final.stock 1 .service = 0 := by simpa only [zeroCash,Nat.cast_zero] using stock.cash
  have balance := the_whole_actual_material_account_consumes_each_generated_debit_and_credit demands 0 .feedstock
  rw [finalFuel,the_original_exhausted_occurrence_supplies_the_primitive_inventory.fuel] at balance
  exact ⟨finalFuel,finalCash,by simpa using balance⟩

theorem excess_demand_preserves_the_paid_prefix_and_its_original_refusal
    (demands : List Bool) (excess : 6 < demands.length) :
    (DemandRenewalRun.run demands original).served.length = 6 ∧
      (DemandRenewalRun.run demands original).served ++ (DemandRenewalRun.run demands original).pending = demands ∧
      ∃ front before second tail,
        (DemandRenewalRun.run demands original).words = front ++ DemandRenewalStep.words before second ∧
        before = front.foldl law.next original ∧ PaidTrace original front ∧
        (DemandRenewalRun.run demands original).pending = second :: tail ∧
        ¬ law.Valid (prepared before) (fee second) ∧
        ⟨0,prepared before,fee second⟩ ∈ law.rawItems (prepared before) [fee second] := by
  have count := every_demand_preserves_the_exact_source_capacity_cut demands original 0 2
    the_original_exhausted_occurrence_supplies_the_primitive_inventory
  have served : (DemandRenewalRun.run demands original).served.length = 6 := by simpa [Nat.min_eq_right (by omega : 6 ≤ demands.length)] using count
  have ordered := (every_report_keeps_the_literal_actual_source demands original).2
  refine ⟨served,ordered,?_⟩
  rcases unpaid_tail_keeps_a_paid_prefix_and_its_first_actual_refusal demands original 0 2
    the_original_exhausted_occurrence_supplies_the_primitive_inventory with empty | stopped
  · have same := congrArg List.length ordered
    rw [List.length_append,empty,List.length_nil,served] at same
    omega
  · obtain ⟨front,before,second,tail,words,origin,paid,_,unpaid,pending⟩ := stopped
    exact ⟨front,before,second,tail,words,origin,paid,pending,
      an_unpaid_step_really_attempts_and_refuses_the_original_fee before second unpaid⟩

def withoutFuel : Current := {original with
  stock := fun party good => if party = 0 ∧ good = .feedstock then 0 else original.stock party good}

theorem deleting_the_actual_fuel_removes_the_first_payment :
    paid withoutFuel = false ∧ (DemandRenewalRun.run [false] withoutFuel).served = [] ∧
      (DemandRenewalRun.run [false] withoutFuel).pending = [false] ∧
      ¬ law.Valid (prepared withoutFuel) (fee false) := by
  have stock : Inventory withoutFuel 0 0 := by
    have original := the_original_exhausted_occurrence_supplies_the_primitive_inventory
    refine ⟨?_,?_,?_,?_,?_⟩
    · obtain ⟨pf,wf,ww,willing,waste,pe,pl,we,wl⟩ := original.material
      constructor
      all_goals first | simpa [RecycledQuorumMaterial.material,withoutFuel] using pf |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using wf |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using ww |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using willing |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using waste |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using pe |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using pl |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using we |
        simpa [RecycledQuorumMaterial.material,withoutFuel] using wl
    · simpa [withoutFuel] using original.cash
    · simp [withoutFuel]
    · simpa [withoutFuel] using original.labor
    · simpa [withoutFuel] using original.energy
  have unpaid := exhausted_resources_generate_a_real_refusal withoutFuel stock
  refine ⟨unpaid,?_,?_,(an_unpaid_step_really_attempts_and_refuses_the_original_fee withoutFuel false unpaid).1⟩
  all_goals simp [run_cons,unpaid,refusal]

theorem existing_cash_is_consumed_without_a_redundant_renewal :
    refill (RenewedQuorumConsumer.current 23) = false := by decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DemandRenewalConsumer
