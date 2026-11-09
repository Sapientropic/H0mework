import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Delivery

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (ActualAndIndependent withoutControllerConsents)
open Conflict.Consumers.Evolving (W life)

private theorem a_personal_item_needs_no_external_stock_or_consent
    (raw : Original.Raw) (person : Bool) (index : Nat) (item : Original.Item)
    (listed : item ∈ personalItems raw person index) :
    withoutControllerConsents item.request = item.request ∧
      ∀ part ∈ revisedLaw.debit item.before item.request, part.1.1 = item.request.signer := by
  rcases List.mem_cons.mp listed with rfl | rest
  · refine ⟨rfl, ?_⟩
    intro part debit
    change part ∈ [((person, false), 18)] at debit
    rcases List.mem_singleton.mp debit with rfl
    rfl
  · rcases List.mem_singleton.mp rest with rfl
    refine ⟨rfl, ?_⟩
    intro part debit
    change part ∈ [((person, true), 1)] at debit
    rcases List.mem_singleton.mp debit with rfl
    rfl

private theorem own_authority_from_the_physical_inventory (raw : Original.Raw) (word : W)
    (lawful : ∀ item ∈ physical.rawItems raw word, revisedLaw.Valid item.before item.request)
    (own : ∀ item ∈ physical.rawItems raw word, withoutControllerConsents item.request = item.request ∧
      ∀ part ∈ revisedLaw.debit item.before item.request, part.1.1 = item.request.signer) :
    ActualAndIndependent revisedInput raw word := by
  have execution := PublicFunction.execute_physical_of_authorized revisedLaw raw 0 word
    (fun item listed => PublicFunction.valid_physical _ _ _ (lawful item listed)) lawful
  have same : revisedLaw.rawItems raw word = physical.rawItems raw word := congrArg ExecutionResult.items execution
  intro item listed
  change item ∈ revisedLaw.rawItems raw word at listed
  rw [same] at listed
  obtain ⟨unsigned, payer⟩ := own item listed
  refine ⟨lawful item listed, ?_, fun part present _ => payer part present⟩
  rw [unsigned]
  exact lawful item listed

/-- The native independent-material checker applies to one person's
actual exit. No debit comes from an actor other than its signer. -/
theorem the_personal_exit_passes_the_original_independence_checker
    (raw : Original.Raw) (person : Bool) (carrier : 18 ≤ raw.stock person false)
    (food : 0 ≤ raw.stock person true) :
    ActualAndIndependent revisedInput raw (personalWord person) := by
  apply own_authority_from_the_physical_inventory
  · intro item listed
    rw [RawLaw.rawItems, the_personal_inventory_is_exact raw person 0 carrier food] at listed
    exact every_personal_item_has_original_authority raw person 0 carrier food item listed
  · intro item listed
    rw [RawLaw.rawItems, the_personal_inventory_is_exact raw person 0 carrier food] at listed
    exact a_personal_item_needs_no_external_stock_or_consent raw person 0 item listed

theorem the_ordered_renewal_passes_the_original_independence_checker
    (raw : Original.Raw) (stocked : Stocked raw) (first : Bool) :
    ActualAndIndependent revisedInput raw (personalWord first ++ personalWord (!first)) := by
  apply own_authority_from_the_physical_inventory
  · exact every_ordered_renewal_item_has_original_authority raw stocked first
  · intro item listed
    rw [RawLaw.rawItems, the_ordered_renewal_inventory_is_exact raw stocked first] at listed
    rcases List.mem_append.mp listed with left | right
    · exact a_personal_item_needs_no_external_stock_or_consent raw first 0 item left
    · exact a_personal_item_needs_no_external_stock_or_consent raw (!first) 2 item right

theorem the_joint_renewal_passes_the_original_independence_checker
    (raw : Original.Raw) (stocked : Stocked raw) :
    ActualAndIndependent revisedInput raw renewalWord :=
  the_ordered_renewal_passes_the_original_independence_checker raw stocked false

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply
