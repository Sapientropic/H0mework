import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Period

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers.Evolving (compact life)

noncomputable section

private abbrev foodDebit (person : Bool) (item : Original.Item) : ℚ :=
  match item.request.operation with
  | .use bearer _ kind => if bearer = person ∧ kind = .necessity then
      flowAt (physical.actualDebit item.before item.request) person true else 0
  | _ => 0

private theorem only_the_personal_owner_is_fed (raw : Original.Raw) (stocked : Stocked raw)
    (owner person : Bool) (index : Nat) :
    ((personalItems raw owner index).map (foodDebit person)).sum = if owner = person then 1 else 0 := by
  have spent := (the_original_personal_production_and_meal_are_both_paid raw owner index
    (stocked owner).1 (stocked owner).2).2.2.2
  change 0 + ((if owner = person ∧ Use.necessity = Use.necessity then
    flowAt (physical.actualDebit (physical.step raw (grow owner)) (life owner)) person true else 0) + 0) = _
  rw [spent]
  by_cases same : owner = person
  · subst person
    simp [flowAt, amount]
  · simp [same]

theorem the_ordered_renewal_delivers_each_original_living_unit
    (raw : Original.Raw) (stocked : Stocked raw) (first person : Bool) :
    Capitalism.Universal.Abolition.Material.actualUse (Macro.Public.Scope.checkInput revisedInput)
      raw (personalWord first ++ personalWord (!first)) person .necessity true = 1 := by
  change ((physical.execute raw 0 (personalWord first ++ personalWord (!first))).items.map
    (foodDebit person)).sum = 1
  rw [the_ordered_renewal_inventory_is_exact raw stocked first]
  simp only [List.map_append, List.sum_append]
  rw [only_the_personal_owner_is_fed raw stocked first person 0,
    only_the_personal_owner_is_fed raw stocked (!first) person 2]
  cases first <;> cases person <;> decide +kernel

theorem the_renewal_delivers_each_original_living_unit (raw : Original.Raw) (stocked : Stocked raw) (person : Bool) :
    Capitalism.Universal.Abolition.Material.actualUse (Macro.Public.Scope.checkInput revisedInput)
      raw renewalWord person .necessity true = 1 :=
  the_ordered_renewal_delivers_each_original_living_unit raw stocked false person

/-- Each unit of food comes from the same person's paid production and
is consumed by their own next material instruction in the actual period. -/
theorem the_ordered_native_renewal_contains_each_persons_paid_work_and_meal
    (before : PhysicalCurrent) (stocked : Stocked before.raw) (first person : Bool) :
    let word := personalWord first ++ personalWord (!first)
    let paid := Physical.Public.compile revisedInput before (.execute word)
    ∃ work ∈ paid.execution.items, ∃ meal ∈ paid.execution.items,
      work.request = grow person ∧ meal.request = life person ∧
      work.request.signer = person ∧ meal.request.signer = person ∧
      work.index + 1 = meal.index ∧ work.before = before.raw ∧
      meal.before = physical.step work.before work.request ∧
      physical.actualDebit work.before work.request = [((person, false), 18)] ∧
      physical.actualCredit work.before work.request = [((person, false), 18), ((person, true), 1)] ∧
      physical.actualDebit meal.before meal.request = [((person, true), 1)] ∧
      work.index = (if person = first then 0 else 2) := by
  let index : Nat := if person = first then 0 else 2
  let work : Original.Item := ⟨index, before.raw, grow person⟩
  let meal : Original.Item := ⟨index + 1, physical.step before.raw (grow person), life person⟩
  have listed := (the_native_renewal_can_start_with_either_person before stocked first).2.1
  rw [RawLaw.rawItems, the_ordered_renewal_inventory_is_exact before.raw stocked first] at listed
  let paid := Physical.Public.compile revisedInput before (.execute (personalWord first ++ personalWord (!first)))
  have works : work ∈ paid.execution.items := by
    dsimp only [paid]
    rw [listed]
    cases first <;> cases person
    · exact List.mem_append_left _ List.mem_cons_self
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ List.mem_cons_self
  have meals : meal ∈ paid.execution.items := by
    dsimp only [paid]
    rw [listed]
    cases first <;> cases person
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have production := own_production_writes_the_paid_material_legs before.raw person (stocked person).1
  have necessity := (the_original_personal_production_and_meal_are_both_paid before.raw person index
    (stocked person).1 (stocked person).2).2.2.2
  exact ⟨work, works, meal, meals, rfl, rfl, rfl, rfl, rfl, rfl, rfl, production.1, production.2.1, necessity, rfl⟩

theorem the_same_native_renewal_contains_each_persons_paid_work_and_meal
    (before : PhysicalCurrent) (stocked : Stocked before.raw) (person : Bool) :
    let paid := physicalRenewal before
    ∃ work ∈ paid.execution.items, ∃ meal ∈ paid.execution.items,
      work.request = grow person ∧ meal.request = life person ∧
      work.request.signer = person ∧ meal.request.signer = person ∧
      work.index + 1 = meal.index ∧ work.before = before.raw ∧
      meal.before = physical.step work.before work.request ∧
      physical.actualDebit work.before work.request = [((person, false), 18)] ∧
      physical.actualCredit work.before work.request = [((person, false), 18), ((person, true), 1)] ∧
      physical.actualDebit meal.before meal.request = [((person, true), 1)] := by
  obtain ⟨work, workListed, meal, mealListed, growRequest, mealRequest, growSigner, mealSigner, order,
    original, next, debit, credit, payment, _⟩ :=
    the_ordered_native_renewal_contains_each_persons_paid_work_and_meal before stocked false person
  exact ⟨work, workListed, meal, mealListed, growRequest, mealRequest, growSigner, mealSigner, order,
    original, next, debit, credit, payment⟩

theorem the_compact_production_cannot_output_any_food (raw : Original.Raw) (person : Bool) :
    flowAt ((Physical.Public.interpreter compact).actualCredit raw (grow person)) person true = 0 := by
  unfold RawLaw.actualCredit
  split
  · change flowAt [((person, false), 18)] person true = 0
    cases person <;> decide +kernel
  · rfl

/-- At insufficient original carrier stock the compiler refuses the
whole submitted personal period and leaves the original current untouched. -/
theorem the_material_compiler_refuses_unfunded_production
    (before : PhysicalCurrent) (person : Bool) (short : before.raw.stock person false < 18) :
    let failed := physicalPersonal before person
    failed.isAccepted = false ∧ failed.execution.items = [] ∧ failed.next = before := by
  have selected : Physical.Public.wordAt before (.execute (personalWord person)) = some (personalWord person) := rfl
  unfold physicalPersonal
  dsimp only
  cases Physical.Public.compile revisedInput before (.execute (personalWord person)) with
  | accepted actual original lawful =>
    rw [selected] at original
    cases Option.some.inj original
    exact (raw_lack_of_carrier_rejects_the_new_production before.raw person short
      (lawful ⟨0, before.raw, grow person⟩ List.mem_cons_self)).elim
  | refused _ _ _ _ _ => exact ⟨rfl, rfl, rfl⟩
  | metadata absent =>
    rw [selected] at absent
    cases absent

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply
