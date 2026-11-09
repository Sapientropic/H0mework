import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Effect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Delivery

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor ActualAndIndependent actualUse originalRequirements)
open Conflict.Consumers.Evolving (W life)

noncomputable section

private abbrev registered := TerminalPeace.Supply.revisedInput
private abbrev physical := TerminalPeace.Supply.physical
private abbrev ownWord := TerminalPeace.Supply.personalWord

private theorem personal_items_are_owned (raw : Original.Raw) (person : Bool) (index : Nat)
    (roster : List Bool) (member : person ∈ roster)
    (carrier : 18 ≤ raw.stock person false) (food : 0 ≤ raw.stock person true) :
    ∀ item ∈ TerminalPeace.Supply.personalItems raw person index, OwnItem registered.law roster item := by
  intro item listed
  have valid := TerminalPeace.Supply.every_personal_item_has_original_authority raw person index carrier food item listed
  rcases List.mem_cons.mp listed with rfl | tail
  · exact ⟨rfl, member, rfl, valid⟩
  · rcases List.mem_singleton.mp tail with rfl
    exact ⟨⟨rfl, Or.inl rfl⟩, member, rfl, valid⟩

private theorem actual_use_agrees_on_the_paid_original_inventory
    (raw : Original.Raw) (word : W) (roster : List Bool)
    (own : ∀ item ∈ physical.rawItems raw word, OwnItem registered.law roster item)
    (inventory : registered.law.rawItems raw word = physical.rawItems raw word) (person : Bool) :
    actualUse registered raw word person .necessity true =
      actualUse (Macro.Public.Scope.checkInput registered) raw word person .necessity true := by
  unfold actualUse
  rw [inventory, show (Macro.Public.Scope.checkInput registered).law = physical from rfl]
  apply congrArg List.sum
  apply List.map_congr_left
  intro item listed
  have paid := (own item listed).valid
  have physically : physical.Valid item.before item.request :=
    PublicFunction.valid_physical _ _ _ paid
  have same : registered.law.actualDebit item.before item.request = physical.actualDebit item.before item.request := by
    simp only [RawLaw.actualDebit, if_pos paid, if_pos physically]
    rfl
  simp only [same]

private theorem the_original_need_is_paid
    (origin raw : Original.Raw) (word : W) (roster : List Bool)
    (each : ∀ person ∈ roster, actualUse registered raw word person .necessity true = 1) :
    OriginalNeedFloor registered origin raw roster word := by
  intro cell listed
  obtain ⟨person, member, exactCell⟩ := List.mem_flatMap.mp listed
  change cell ∈ [(person, Use.necessity, true, amount Bool [(true, 1)] true)] at exactCell
  rw [show amount Bool [(true, 1)] true = 1 by decide +kernel] at exactCell
  rw [List.mem_singleton.mp exactCell]
  exact (each person member).ge

private theorem paid_original_effects_give_the_period
    (origin raw : Original.Raw) (word : W) (roster : List Bool)
    (own : ∀ item ∈ physical.rawItems raw word, OwnItem registered.law roster item)
    (fed : ∀ person ∈ roster,
      actualUse (Macro.Public.Scope.checkInput registered) raw word person .necessity true = 1) :
    Period registered origin raw roster word := by
  have physicalExecution : registered.law.execute raw 0 word = physical.execute raw 0 word :=
    PublicFunction.execute_physical_of_authorized registered.law raw 0 word
      (fun item listed => PublicFunction.valid_physical _ _ _ (own item listed).valid)
      (fun item listed => (own item listed).valid)
  have inventory : registered.law.rawItems raw word = physical.rawItems raw word :=
    congrArg ExecutionResult.items physicalExecution
  have each : ∀ person ∈ roster, actualUse registered raw word person .necessity true = 1 :=
    fun person member =>
      (actual_use_agrees_on_the_paid_original_inventory raw word roster own inventory person).trans (fed person member)
  refine ⟨?_, the_original_need_is_paid origin raw word roster each,
    the_original_need_is_paid raw raw word roster each, ?_⟩
  · intro item listed
    rw [inventory] at listed
    exact own item listed
  · change (0 : ℚ) < 1
    norm_num

theorem the_original_ordered_period_is_paid (origin raw : Original.Raw)
    (stocked : TerminalPeace.Supply.Stocked raw) (first : Bool) :
    Period registered origin raw [false, true] (ownWord first ++ ownWord (!first)) := by
  have literal := TerminalPeace.Supply.the_ordered_renewal_inventory_is_exact raw stocked first
  refine paid_original_effects_give_the_period origin raw _ _ ?_
    (fun person _ => TerminalPeace.Supply.the_ordered_renewal_delivers_each_original_living_unit raw stocked first person)
  intro item listed
  rw [RawLaw.rawItems, literal] at listed
  rcases List.mem_append.mp listed with left | right
  · exact personal_items_are_owned raw first 0 _ (by cases first <;> decide) (stocked first).1 (stocked first).2 item left
  · exact personal_items_are_owned raw (!first) 2 _ (by cases first <;> decide) (stocked (!first)).1 (stocked (!first)).2 item right

theorem the_original_personal_period_is_paid (origin raw : Original.Raw) (person : Bool)
    (carrier : 18 ≤ raw.stock person false) (food : 0 ≤ raw.stock person true) :
    Period registered origin raw [person] (ownWord person) := by
  have literal := TerminalPeace.Supply.the_personal_inventory_is_exact raw person 0 carrier food
  have debit := (TerminalPeace.Supply.the_original_personal_production_and_meal_are_both_paid raw person 0 carrier food).2.2.2
  refine paid_original_effects_give_the_period origin raw _ _ ?_ ?_
  · intro item listed
    rw [RawLaw.rawItems, literal] at listed
    exact personal_items_are_owned raw person 0 _ (List.mem_singleton_self _) carrier food item listed
  · intro bearer member
    have same : bearer = person := List.mem_singleton.mp member
    subst bearer
    unfold actualUse
    rw [show (Macro.Public.Scope.checkInput registered).law = physical from rfl, RawLaw.rawItems, literal]
    change 0 + ((if person = person ∧ Use.necessity = Use.necessity then
      flowAt (physical.actualDebit (physical.step raw (TerminalPeace.Supply.grow person)) (life person)) person true
      else 0) + 0) = 1
    rw [debit]
    simp [flowAt, amount]

private theorem personal_authority_requires_exact_opening_stock (raw : Original.Raw) (person : Bool)
    (authorized : ActualAndIndependent registered raw (ownWord person)) :
    18 ≤ raw.stock person false ∧ 0 ≤ raw.stock person true := by
  let grow := TerminalPeace.Supply.grow person
  let after := registered.law.step raw grow
  have validGrow : registered.law.Valid raw grow :=
    (authorized ⟨0, raw, grow⟩ List.mem_cons_self).1
  have carrier := validGrow.2.2.2.2.2 ((person, false), 18) List.mem_cons_self
  change flowAt [((person, false), 18)] person false ≤ raw.stock person false at carrier
  have sufficient : 18 ≤ raw.stock person false := by simpa [flowAt, amount] using carrier
  have validMeal : registered.law.Valid after (life person) :=
    (authorized ⟨1, after, life person⟩ (List.mem_cons_of_mem _ List.mem_cons_self)).1
  have meal := validMeal.2.2.2.2.2 ((person, true), 1) List.mem_cons_self
  change flowAt [((person, true), 1)] person true ≤ after.stock person true at meal
  have remaining : (1 : ℚ) ≤ after.stock person true := by simpa [flowAt, amount] using meal
  have physicalGrow : physical.Valid raw grow := PublicFunction.valid_physical _ _ _ validGrow
  have same : physical.step raw grow = after := by
    unfold after
    simp only [RawLaw.step, if_pos physicalGrow, if_pos validGrow]
    rfl
  obtain ⟨debit, credit, _⟩ := TerminalPeace.Supply.own_production_writes_the_paid_material_legs raw person sufficient
  have produced := physical.material_step_balance raw grow person true
  change physical.actualDebit raw grow = _ at debit
  change physical.actualCredit raw grow = _ at credit
  rw [same, debit, credit] at produced
  have food : after.stock person true = raw.stock person true + 1 := by
    simpa [flowAt, amount] using produced
  exact ⟨sufficient, by linarith only [remaining, food]⟩

/-- At a person's actual cut, the two material bounds are both necessary
and sufficient for the complete repeatable personal period. -/
theorem the_original_personal_period_iff_own_stock (origin raw : Original.Raw) (person : Bool) :
    Period registered origin raw [person] (ownWord person) ↔
      18 ≤ raw.stock person false ∧ 0 ≤ raw.stock person true :=
  ⟨fun paid => personal_authority_requires_exact_opening_stock raw person paid.toActualAndIndependent,
    fun stock => the_original_personal_period_is_paid origin raw person stock.1 stock.2⟩

theorem the_original_personal_period_iff_original_independence (origin raw : Original.Raw) (person : Bool) :
    Period registered origin raw [person] (ownWord person) ↔ ActualAndIndependent registered raw (ownWord person) :=
  ⟨Period.toActualAndIndependent, fun accepted =>
    (the_original_personal_period_iff_own_stock origin raw person).mpr
      (personal_authority_requires_exact_opening_stock raw person accepted)⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Consumers
