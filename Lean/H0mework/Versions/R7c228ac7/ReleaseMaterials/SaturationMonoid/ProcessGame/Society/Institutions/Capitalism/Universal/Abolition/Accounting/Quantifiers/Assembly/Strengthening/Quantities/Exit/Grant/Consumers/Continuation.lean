import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Composition

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Source.Program Abolition.Root.Registered
open Innovation.Contribution.Pricing.Root.Runtime
open Innovation.Contribution.Pricing.Consumers.Actual
  (life lifeWord request source_input_is_the_original_registered_input every_original_person_keeps_actual_standing)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

private abbrev law := Physical.Public.interpreter Joint.Consumers.Compact.input

theorem life_is_valid_from_actual_stock (raw : RawCurrent Bool Bool Unit Unit)
    (person : Bool) (stock : 1 ≤ raw.stock person true) : law.Valid raw (life person) := by
  refine ⟨⟨trivial, rfl⟩, fun _ _ => Or.inl rfl, rfl, ?_, ?_, ?_⟩
  · change ∀ lot ∈ [((person, true), (1 : ℚ))], 0 ≤ lot.2
    simp
  · change ∀ lot ∈ ([] : Flow Bool Bool), 0 ≤ lot.2
    simp
  · intro item listed
    change item ∈ [((person, true), (1 : ℚ))] at listed
    obtain rfl := List.mem_singleton.mp listed
    cases person <;>
      simpa [life, request, RawLaw.debit, locate, flowAt, amount] using stock

theorem life_word_valid_after_grant (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    let target := redeemed lifeSource position (proposal quantity)
    ∀ item ∈ (Physical.Public.interpreter target.native.input).rawItems target.raw lifeWord,
      (Physical.Public.interpreter target.native.input).Valid item.before item.request := by
  dsimp only
  rw [redeemed_input_is_the_original, source_input_is_the_original_registered_input]
  let raw := (redeemed lifeSource position (proposal quantity)).raw
  have first := life_is_valid_from_actual_stock raw false (original_food_is_still_available quantity paid false).ge
  have otherStock : (law.step raw (life false)).stock true true = 1 := by
    rw [RawLaw.step, if_pos first]
    simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, life, request, locate, flowAt, amount,
      show raw.stock true true = 1 from original_food_is_still_available quantity paid true]
  have second := life_is_valid_from_actual_stock (law.step raw (life false)) true otherStock.ge
  simp only [lifeWord, RawLaw.rawItems, RawLaw.execute, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  exact ⟨first, second⟩

theorem actual_continuation (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    let target := redeemed lifeSource position (proposal quantity)
    Trace target lifeWord (Execution.endAt target (proposal quantity).continuation) ∧
      Ready (Execution.endAt target (proposal quantity).continuation) := by
  have signed : ∀ item ∈ lifeWord, item.consents = [] := by
    intro item listed
    simp only [lifeWord, List.mem_cons, List.not_mem_nil, or_false] at listed
    rcases listed with rfl | rfl <;> rfl
  obtain ⟨trace, finished, _⟩ := Execution.pay_checked_primitives (redeemed lifeSource position (proposal quantity))
    lifeWord 0 paid.ready paid.available signed (life_word_valid_after_grant quantity paid)
  exact ⟨trace, finished⟩

theorem actual_service_is_independent (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    ∀ item ∈ Execution.inventory (redeemed lifeSource position (proposal quantity)) (proposal quantity).continuation,
      Independent lifeSource [] item := by
  have trace := (actual_continuation quantity paid).1
  change ∀ item ∈ Execution.inventory (redeemed lifeSource position (proposal quantity))
    (Execution.primitiveScript lifeWord), Independent lifeSource [] item
  rw [Execution.primitive_inventory trace 0]
  simp only [lifeWord, RawLaw.execute, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  constructor <;>
    refine ⟨every_original_person_keeps_actual_standing _, List.not_mem_nil, rfl, ?_⟩ <;>
    intro entry inside _ <;>
    unfold RawLaw.actualDebit at inside <;>
    split at inside <;>
    simp [RawLaw.debit, life, request, locate] at inside ⊢ <;>
    subst entry <;> rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
