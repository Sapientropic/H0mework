import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal.Guard
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Delivery

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (R life)

noncomputable section

def orderedService (first : Bool) : Request :=
  .execute (Supply.personalWord first ++ Supply.personalWord (!first))

abbrev service : Request := orderedService false

private def authorizesOwnWork (person : Bool) : R → Bool
  | ⟨signer, [], false, [], .produce operator⟩ => decide (signer = person ∧ operator = person)
  | ⟨signer, [], false, [], .use bearer goods .necessity⟩ =>
      decide (signer = person ∧ bearer = person ∧ goods = [(true, 1)])
  | _ => false

/-- The independent owners submit their own production and meal items
to this one committed service. These answers are for the service input. -/
def serviceReplies (before : Native) (first : Bool) : Replies before (orderedService first) :=
  fun position person =>
    authorizesOwnWork person (readAction before (orderedService first)).execution.items[position].request

theorem the_service_raw (before : Native) (stocked : Supply.Stocked before.raw) (first : Bool) :
    (readAction before (orderedService first)).next.raw =
      { before.raw with clock := before.raw.clock + 1, round := before.raw.round + 1 } :=
  (Supply.the_native_renewal_can_start_with_either_person before stocked first).2.2.2

private theorem a_self_debit_has_no_cross_community_loss (item : Original.Item)
    (valid : Supply.physical.Valid item.before item.request)
    (own : ∀ entry ∈ Supply.physical.actualDebit item.before item.request,
      entry.1.1 = item.request.signer) (payer good : Bool) :
    Reparation.loss Supply.physical Original.community item (payer, item.request.signer, good) = 0 := by
  unfold Reparation.loss
  split
  · rename_i foreign
    have empty : flowAt (Supply.physical.actualDebit item.before item.request) payer good = 0 := by
      apply amount_zero_of_absent
      intro entry listed exactAddress
      exact foreign.1 (congrArg Original.community
        ((congrArg Prod.fst exactAddress).symm.trans (own entry listed)))
    have received : 0 ≤ flowAt (Supply.physical.actualCredit item.before item.request) payer good := by
      rw [RawLaw.actualCredit, if_pos valid]
      exact amount_nonnegative _ valid.2.2.2.2.1 _
    rw [empty, zero_sub, max_eq_left (neg_nonpos.mpr received)]
  · rfl

private theorem own_work_has_no_foreign_or_financial_effect (item : Original.Item)
    (valid : Supply.revisedLaw.Valid item.before item.request)
    (source : ∃ person, item.request = Supply.grow person ∨ item.request = life person) :
    AllowedItem item ∧ authorizesOwnWork item.request.signer item.request = true := by
  rcases item with ⟨index, raw, request⟩
  rcases source with ⟨person, rfl | rfl⟩
  all_goals
    have physical : Supply.physical.Valid raw _ :=
      PublicFunction.valid_physical Supply.revisedLaw raw _ valid
    refine ⟨⟨valid, ?_, ?_⟩, ?_⟩
    · intro payer _ good _
      apply a_self_debit_has_no_cross_community_loss _ physical _ payer good
      intro entry listed
      rw [RawLaw.actualDebit, if_pos physical] at listed
      first | change entry ∈ [((person, false), 18)] at listed | change entry ∈ [((person, true), 1)] at listed
      rcases List.mem_singleton.mp listed with rfl
      rfl
    · intro payer _ holder _
      rw [RawLaw.actualClaimDelta, if_pos physical]
      rfl
    · simp [authorizesOwnWork, Supply.grow, life]

private theorem every_service_item_is_its_own_work (before : Native) (stocked : Supply.Stocked before.raw)
    (first : Bool) (item : Original.Item) (listed : item ∈ (readAction before (orderedService first)).execution.items) :
    ∃ person, item.request = Supply.grow person ∨ item.request = life person := by
  have selected := (Supply.the_native_renewal_can_start_with_either_person before stocked first).2.1
  change (readAction before (orderedService first)).execution.items = _ at selected
  rw [selected] at listed
  have request := List.mem_map_of_mem (f := ExecutionItem.request) listed
  rw [RawLaw.rawItems, RawLaw.inventory_requests_exact] at request
  change item.request ∈ [Supply.grow first, life first, Supply.grow (!first), life (!first)] at request
  simp only [List.mem_cons, List.not_mem_nil, or_false] at request
  rcases request with same | same | same | same
  · exact ⟨first, Or.inl same⟩
  · exact ⟨first, Or.inr same⟩
  · exact ⟨!first, Or.inl same⟩
  · exact ⟨!first, Or.inr same⟩

theorem the_service_pays_exactly_one_to_each_original_person (before : Native) (stocked : Supply.Stocked before.raw)
    (first person : Bool) : foodPaid (readAction before (orderedService first)).execution.items person = 1 := by
  have selected := (Supply.the_native_renewal_can_start_with_either_person before stocked first).2.1
  change (readAction before (orderedService first)).execution.items = _ at selected
  rw [selected]
  exact Supply.the_ordered_renewal_delivers_each_original_living_unit before.raw stocked first person

theorem the_service_is_admitted_from_its_current_stock (before : Native) (stocked : Supply.Stocked before.raw)
    (first : Bool) : Admission before (orderedService first) (serviceReplies before first) := by
  have selected := Supply.the_native_renewal_can_start_with_either_person before stocked first
  have raw := the_service_raw before stocked first
  refine ⟨selected.1, ?_, ?_, ?_, ?_⟩
  · intro position
    let item := (readAction before (orderedService first)).execution.items[position]
    have written : item ∈ (readAction before (orderedService first)).execution.items := List.getElem_mem position.isLt
    have own := own_work_has_no_foreign_or_financial_effect item (selected.2.2.1 item written)
      (every_service_item_is_its_own_work before stocked first item written)
    have actual : item ∈ Supply.physical.rawItems before.raw (Supply.personalWord first ++ Supply.personalWord (!first)) :=
      selected.2.1 ▸ written
    exact ⟨own.1, own.2, Supply.every_ordered_renewal_item_keeps_the_reserve before.raw stocked first item actual⟩
  · rw [raw]
    exact fun _ _ _ _ => rfl
  · rw [raw]
    exact stocked
  · exact Or.inr ⟨congrArg RawCurrent.clock raw, fun person _ =>
      (the_service_pays_exactly_one_to_each_original_person before stocked first person).ge⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Renewal
