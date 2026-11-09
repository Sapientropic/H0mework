import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Local

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Conflict.Consumers.Evolving (W life)

noncomputable section

abbrev PhysicalCurrent :=
  Capitalism.Universal.Abolition.Root.Actual.Current (Party := Bool) (Good := Bool) (Port := Bool)
    (Technology := Unit) (Instrument := Unit)

def physicalRenewal (before : PhysicalCurrent) :=
  Physical.Public.compile revisedInput before (.execute renewalWord)

def physicalPersonal (before : PhysicalCurrent) (person : Bool) :=
  Physical.Public.compile revisedInput before (.execute (personalWord person))

abbrev personalItems (raw : Original.Raw) (person : Bool) (index : Nat) : List Original.Item :=
  [⟨index, raw, grow person⟩, ⟨index + 1, physical.step raw (grow person), life person⟩]

theorem the_personal_inventory_is_exact (raw : Original.Raw) (person : Bool) (index : Nat)
    (carrier : 18 ≤ raw.stock person false) (food : 0 ≤ raw.stock person true) :
    physical.execute raw index (personalWord person) = ⟨raw, personalItems raw person index⟩ :=
  (the_original_personal_production_and_meal_are_both_paid raw person index carrier food).1

theorem every_personal_item_has_original_authority (raw : Original.Raw) (person : Bool) (index : Nat)
    (carrier : 18 ≤ raw.stock person false) (food : 0 ≤ raw.stock person true) :
    ∀ item ∈ personalItems raw person index, revisedLaw.Valid item.before item.request := by
  have paid := (the_original_personal_production_and_meal_are_both_paid raw person index carrier food).2
  intro item listed
  rcases List.mem_cons.mp listed with rfl | rest
  · exact paid.1
  · rcases List.mem_singleton.mp rest with rfl
    exact paid.2.1

private theorem every_personal_item_keeps_the_reserve (raw : Original.Raw) (stocked : Stocked raw)
    (person : Bool) (index : Nat) (item : Original.Item) (written : item ∈ personalItems raw person index) :
    Stocked item.before ∧ Stocked (physical.step item.before item.request) := by
  have retained := both_personal_material_legs_keep_the_living_reserve raw stocked person
  rcases List.mem_cons.mp written with rfl | tail
  · exact ⟨stocked, retained.1⟩
  · rcases List.mem_singleton.mp tail with rfl
    exact ⟨retained.1, retained.2.symm ▸ stocked⟩

theorem the_ordered_renewal_inventory_is_exact (raw : Original.Raw) (stocked : Stocked raw) (first : Bool) :
    physical.execute raw 0 (personalWord first ++ personalWord (!first)) =
      ⟨raw, personalItems raw first 0 ++ personalItems raw (!first) 2⟩ := by
  rw [RawLaw.execute_append,
    the_personal_inventory_is_exact raw first 0 (stocked first).1 (stocked first).2]
  change ExecutionResult.mk (physical.execute raw 2 (personalWord (!first))).final
    (personalItems raw first 0 ++ (physical.execute raw 2 (personalWord (!first))).items) = _
  rw [the_personal_inventory_is_exact raw (!first) 2 (stocked (!first)).1 (stocked (!first)).2]

theorem the_renewal_inventory_is_exact (raw : Original.Raw) (stocked : Stocked raw) :
    physical.execute raw 0 renewalWord = ⟨raw, personalItems raw false 0 ++ personalItems raw true 2⟩ :=
  the_ordered_renewal_inventory_is_exact raw stocked false

theorem every_ordered_renewal_item_has_original_authority (raw : Original.Raw) (stocked : Stocked raw) (first : Bool) :
    ∀ item ∈ physical.rawItems raw (personalWord first ++ personalWord (!first)),
      revisedLaw.Valid item.before item.request := by
  intro item listed
  rw [RawLaw.rawItems, the_ordered_renewal_inventory_is_exact raw stocked first] at listed
  rcases List.mem_append.mp listed with left | right
  · exact every_personal_item_has_original_authority raw first 0 (stocked first).1 (stocked first).2 item left
  · exact every_personal_item_has_original_authority raw (!first) 2 (stocked (!first)).1 (stocked (!first)).2 item right

theorem every_ordered_renewal_item_keeps_the_reserve (raw : Original.Raw) (stocked : Stocked raw)
    (first : Bool) (item : Original.Item) (written : item ∈ physical.rawItems raw (personalWord first ++ personalWord (!first))) :
    Stocked item.before ∧ Stocked (physical.step item.before item.request) := by
  rw [RawLaw.rawItems, the_ordered_renewal_inventory_is_exact raw stocked first] at written
  rcases List.mem_append.mp written with left | right
  · exact every_personal_item_keeps_the_reserve raw stocked first 0 item left
  · exact every_personal_item_keeps_the_reserve raw stocked (!first) 2 item right

theorem every_renewal_item_has_original_authority (raw : Original.Raw) (stocked : Stocked raw) :
    ∀ item ∈ physical.rawItems raw renewalWord, revisedLaw.Valid item.before item.request :=
  every_ordered_renewal_item_has_original_authority raw stocked false

private theorem native_period_is_the_literal_execution (before : PhysicalCurrent) (word : W)
    (same : (word.map fun request => request.resign request.signer) = word)
    (authorized : ∀ item ∈ physical.rawItems before.raw word, revisedLaw.Valid item.before item.request) :
    let paid := Physical.Public.compile revisedInput before (.execute word)
    paid.isAccepted = true ∧ paid.execution = physical.execute before.raw 0 word ∧
      paid.next.raw = physical.next before.raw word := by
  have selected : Physical.Public.wordAt before (.execute word) = some word := congrArg some same
  dsimp only
  cases Physical.Public.compile revisedInput before (.execute word) with
  | accepted actual original _ =>
    rw [selected] at original
    cases Option.some.inj original
    exact ⟨rfl, rfl, rfl⟩
  | refused actual original item listed failed =>
    rw [selected] at original
    cases Option.some.inj original
    exact (failed (PublicFunction.valid_physical revisedLaw item.before item.request (authorized item listed))).elim
  | metadata absent =>
    rw [selected] at absent
    cases absent

private theorem physical_tick_has_the_original_duration (raw : Original.Raw) (word : W)
    (reused : (physical.execute raw 0 word).final = raw) :
    physical.next raw word = { raw with clock := raw.clock + 1, round := raw.round + 1 } := by
  unfold RawLaw.next
  rw [reused]
  change { raw with clock := raw.clock + max 0 1, round := raw.round + 1 } = _
  rw [max_eq_right zero_le_one]

/-- Either person may go first inside the same period. The compiler
retains that order while both choices give the same material successor. -/
theorem the_native_renewal_can_start_with_either_person
    (before : PhysicalCurrent) (stocked : Stocked before.raw) (first : Bool) :
    let word := personalWord first ++ personalWord (!first)
    let paid := Physical.Public.compile revisedInput before (.execute word)
    paid.isAccepted = true ∧
      paid.execution.items = physical.rawItems before.raw word ∧
      (∀ item ∈ paid.execution.items, revisedLaw.Valid item.before item.request) ∧
      paid.next.raw = { before.raw with clock := before.raw.clock + 1, round := before.raw.round + 1 } := by
  let word := personalWord first ++ personalWord (!first)
  have authorized := every_ordered_renewal_item_has_original_authority before.raw stocked first
  obtain ⟨accepted, actual, result⟩ := native_period_is_the_literal_execution before word rfl authorized
  have items : (Physical.Public.compile revisedInput before (.execute word)).execution.items = physical.rawItems before.raw word :=
    congrArg ExecutionResult.items actual
  have final : (physical.execute before.raw 0 word).final = before.raw :=
    congrArg ExecutionResult.final (the_ordered_renewal_inventory_is_exact before.raw stocked first)
  exact ⟨accepted, items, fun item listed => authorized item ((congrArg (fun entries => item ∈ entries) items).mp listed),
    result.trans (physical_tick_has_the_original_duration before.raw word final)⟩

/-- The paid output is the original public compiler's result at this
actual input current. All raw stocks and claims are retained by the result. -/
theorem the_native_renewal_pays_both_original_bearers (before : PhysicalCurrent) (stocked : Stocked before.raw) :
    let paid := physicalRenewal before
    paid.isAccepted = true ∧
      paid.execution.items = physical.rawItems before.raw renewalWord ∧
      (∀ item ∈ paid.execution.items, revisedLaw.Valid item.before item.request) ∧
      paid.next.raw = { before.raw with clock := before.raw.clock + 1, round := before.raw.round + 1 } :=
  the_native_renewal_can_start_with_either_person before stocked false

/-- The one-person exit uses only this person's literal two instructions.
It has no premise on the other person's stock, agreement, or instruction. -/
theorem the_native_personal_word_is_an_independent_paid_exit (before : PhysicalCurrent) (person : Bool)
    (carrier : 18 ≤ before.raw.stock person false) (food : 0 ≤ before.raw.stock person true) :
    let paid := physicalPersonal before person
    paid.isAccepted = true ∧
      paid.execution.items = personalItems before.raw person 0 ∧
      paid.next.raw = { before.raw with clock := before.raw.clock + 1, round := before.raw.round + 1 } ∧
      physical.actualDebit (physical.step before.raw (grow person)) (life person) = [((person, true), 1)] := by
  have paidPersonal := the_original_personal_production_and_meal_are_both_paid before.raw person 0 carrier food
  have authorized : ∀ item ∈ physical.rawItems before.raw (personalWord person),
      revisedLaw.Valid item.before item.request := by
    intro item listed
    rw [RawLaw.rawItems, paidPersonal.1] at listed
    exact every_personal_item_has_original_authority before.raw person 0 carrier food item listed
  obtain ⟨accepted, actual, result⟩ :=
    native_period_is_the_literal_execution before (personalWord person) rfl authorized
  have exactExecution := actual.trans paidPersonal.1
  have final : (physical.execute before.raw 0 (personalWord person)).final = before.raw :=
    congrArg ExecutionResult.final paidPersonal.1
  exact ⟨accepted, congrArg ExecutionResult.items exactExecution,
    result.trans (physical_tick_has_the_original_duration before.raw (personalWord person) final), paidPersonal.2.2.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply
