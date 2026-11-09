import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply.Rule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply

open Capitalism.Universal.Source.Program
open Conflict.Consumers.Evolving (R life)

private theorem singleton_stock_cost (raw : Original.Raw) (person good : Bool) (quantity : ℚ)
    (stocked : quantity ≤ raw.stock person good) :
    ∀ entry ∈ [((person, good), quantity)],
      flowAt [((person, good), quantity)] entry.1.1 entry.1.2 ≤ raw.stock entry.1.1 entry.1.2 := by
  intro entry listed
  rcases List.mem_singleton.mp listed with rfl
  simpa [flowAt, amount] using stocked

theorem a_person_can_pay_their_own_production (raw : Original.Raw) (person : Bool)
    (carrier : 18 ≤ raw.stock person false) : revisedLaw.Valid raw (grow person) := by
  refine ⟨⟨trivial, ?_⟩, ?_, trivial, ?_, ?_, singleton_stock_cost raw person false 18 carrier⟩
  · change decide (person = person) = true
    simp
  · rw [show revisedLaw.requiredPorts raw (grow person) = [false] from rfl]
    intro port listed
    rcases List.mem_singleton.mp listed with rfl
    exact Or.inl rfl
  · change NonnegativeBundle (Bool × Bool) [((person, false), 18)]
    intro entry listed
    rcases List.mem_singleton.mp listed with rfl
    norm_num
  · change NonnegativeBundle (Bool × Bool) [((person, false), 18), ((person, true), 1)]
    intro entry listed
    rcases List.mem_cons.mp listed with rfl | tail
    · norm_num
    · rcases List.mem_singleton.mp tail with rfl
      norm_num

theorem a_person_can_pay_their_own_meal (raw : Original.Raw) (person : Bool)
    (food : 1 ≤ raw.stock person true) : revisedLaw.Valid raw (life person) := by
  refine ⟨⟨trivial, rfl⟩, ?_, rfl, ?_, ?_, singleton_stock_cost raw person true 1 food⟩
  · rw [show revisedLaw.requiredPorts raw (life person) = [false] from rfl]
    intro port listed
    rcases List.mem_singleton.mp listed with rfl
    exact Or.inl rfl
  · change NonnegativeBundle (Bool × Bool) [((person, true), 1)]
    intro entry listed
    rcases List.mem_singleton.mp listed with rfl
    norm_num
  · change NonnegativeBundle (Bool × Bool) []
    intro entry impossible
    exact (List.not_mem_nil impossible).elim

private theorem physical_accepts (raw : Original.Raw) (request : R) (valid : revisedLaw.Valid raw request) :
    physical.Valid raw request :=
  PublicFunction.valid_physical revisedLaw raw request valid

theorem own_production_writes_the_paid_material_legs (raw : Original.Raw) (person : Bool)
    (carrier : 18 ≤ raw.stock person false) :
    physical.actualDebit raw (grow person) = [((person, false), 18)] ∧
      physical.actualCredit raw (grow person) = [((person, false), 18), ((person, true), 1)] ∧
      (grow person).signer = person :=
  let lawful := physical_accepts raw (grow person) (a_person_can_pay_their_own_production raw person carrier)
  ⟨by rw [RawLaw.actualDebit, if_pos lawful]; rfl, by rw [RawLaw.actualCredit, if_pos lawful]; rfl, rfl⟩

private def withFood (raw : Original.Raw) (person : Bool) : Original.Raw :=
  { raw with stock := fun bearer good =>
      raw.stock bearer good + if bearer = person ∧ good = true then 1 else 0 }

private theorem grow_exact (raw : Original.Raw) (person : Bool) (carrier : 18 ≤ raw.stock person false) :
    physical.step raw (grow person) = withFood raw person := by
  rw [RawLaw.step, if_pos (physical_accepts raw _ (a_person_can_pay_their_own_production raw person carrier))]
  apply RawCurrent.ext
  · funext bearer good
    change raw.stock bearer good - flowAt [((person, false), 18)] bearer good +
        flowAt [((person, false), 18), ((person, true), 1)] bearer good =
      raw.stock bearer good + if bearer = person ∧ good = true then 1 else 0
    cases person <;> cases bearer <;> cases good <;> simp [flowAt, amount]
  · rfl
  · rfl
  · rfl
  · rfl

private theorem one's_food_was_produced (raw : Original.Raw) (person : Bool) (carrier : 18 ≤ raw.stock person false) :
    (physical.step raw (grow person)).stock person true = raw.stock person true + 1 := by
  rw [grow_exact raw person carrier]
  simp [withFood]

private theorem meal_exact (raw : Original.Raw) (person : Bool) (food : 0 ≤ raw.stock person true) :
    physical.step (withFood raw person) (life person) = raw := by
  have stocked : 1 ≤ (withFood raw person).stock person true := by
    simpa [withFood] using (le_add_of_nonneg_left food : (1 : ℚ) ≤ raw.stock person true + 1)
  rw [RawLaw.step, if_pos (physical_accepts _ _ (a_person_can_pay_their_own_meal _ person stocked))]
  apply RawCurrent.ext
  · funext bearer good
    change raw.stock bearer good + (if bearer = person ∧ good = true then 1 else 0) -
        flowAt [((person, true), 1)] bearer good + flowAt [] bearer good = raw.stock bearer good
    cases person <;> cases bearer <;> cases good <;> simp [flowAt, amount]
  · rfl
  · rfl
  · rfl
  · rfl

theorem both_personal_material_legs_keep_the_living_reserve (raw : Original.Raw)
    (stocked : Stocked raw) (person : Bool) :
    Stocked (physical.step raw (grow person)) ∧
      physical.step (physical.step raw (grow person)) (life person) = raw := by
  rw [grow_exact raw person (stocked person).1]
  refine ⟨?_, meal_exact raw person (stocked person).2⟩
  intro bearer
  refine ⟨?_, ?_⟩
  · simpa [withFood] using (stocked bearer).1
  · change 0 ≤ raw.stock bearer true + (if bearer = person ∧ true = true then 1 else 0)
    exact add_nonneg (stocked bearer).2 (by split <;> norm_num)

/-- This person's production and consumption touch their own inventory.
The original material, standing financial principal, and every other
person's stock return literally to the input state before the time tick. -/
theorem the_original_personal_production_and_meal_are_both_paid
    (raw : Original.Raw) (person : Bool) (index : Nat)
    (carrier : 18 ≤ raw.stock person false) (food : 0 ≤ raw.stock person true) :
    let produced := physical.step raw (grow person)
    physical.execute raw index (personalWord person) =
      ⟨raw, [⟨index, raw, grow person⟩, ⟨index + 1, produced, life person⟩]⟩ ∧
    revisedLaw.Valid raw (grow person) ∧ revisedLaw.Valid produced (life person) ∧
    physical.actualDebit produced (life person) = [((person, true), 1)] := by
  let produced := physical.step raw (grow person)
  have available : 1 ≤ produced.stock person true := by
    rw [one's_food_was_produced raw person carrier]
    linarith
  have ownMeal := a_person_can_pay_their_own_meal produced person available
  have final : physical.step produced (life person) = raw := by
    unfold produced
    rw [grow_exact raw person carrier]
    exact meal_exact raw person food
  refine ⟨?_, a_person_can_pay_their_own_production raw person carrier, ownMeal, ?_⟩
  · change ExecutionResult.mk (physical.step produced (life person))
      [⟨index, raw, grow person⟩, ⟨index + 1, produced, life person⟩] = _
    rw [final]
  · rw [RawLaw.actualDebit, if_pos (physical_accepts produced _ ownMeal)]
    rfl

theorem raw_lack_of_carrier_rejects_the_new_production (raw : Original.Raw) (person : Bool)
    (short : raw.stock person false < 18) : ¬ physical.Valid raw (grow person) := by
  intro accepted
  have enough := accepted.2.2.2.2.2 ((person, false), 18) List.mem_cons_self
  change flowAt [((person, false), 18)] person false ≤ raw.stock person false at enough
  exact (not_le_of_gt short) (by simpa [flowAt, amount] using enough)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Supply
