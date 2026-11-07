import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers.Continuation
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Witness
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.PrimitiveClock

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers

open Source.Program Abolition.Root.Registered
open Innovation.Contribution.Pricing.Consumers.Actual
  (life lifeWord task every_original_person_keeps_actual_standing the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)

noncomputable section

theorem actual_exit_service_after_redemption (quantity : ℚ) (paid : PaidAt lifeSource position quantity) :
    Clock.FullyServed (redeemed lifeSource position (proposal quantity)) task (proposal quantity).continuation := by
  let source := redeemed lifeSource position (proposal quantity)
  let script := (proposal quantity).continuation
  let live := Clock.geometry source task script
  have listed : life false ∈ lifeWord := List.mem_cons_self
  obtain ⟨item, original, request, accepted⟩ := Execution.every_original_request_has_its_paid_native_inventory_item
    (actual_continuation quantity paid).1 (life false) listed
  obtain ⟨ordinal, exactItem⟩ := List.mem_iff_get.mp original
  change (Execution.inventory source script).get ordinal = item at exactItem
  let slot : Fin task.slots.length := ⟨0, by decide⟩
  have left : slot ∈ live.leftCarrier := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩
  have time : item.before.clock = source.raw.clock := by
    have inventory := Execution.primitive_inventory (actual_continuation quantity paid).1 0
    rw [inventory] at original
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp original
    rcases List.mem_cons.mp present with same | tail
    · rw [same]
    · rcases List.mem_cons.mp tail with same | none
      · rw [same]
        unfold RawLaw.step
        split <;> rfl
      · exact (List.not_mem_nil none).elim
  have eligible : live.Feasible slot ordinal := by
    change task.earliest ≤ ((Execution.inventory source script).get ordinal).before.clock ∧
      (Physical.Public.interpreter source.native.input).Valid ((Execution.inventory source script).get ordinal).before
        ((Execution.inventory source script).get ordinal).request ∧
      Exit.Necessity.UseMatches ((Execution.inventory source script).get ordinal).request.operation
        (task.slots.get slot).bearer (task.slots.get slot).goods (task.slots.get slot).purpose
    rw [exactItem]
    refine ⟨?_, accepted, ?_⟩
    · rw [time]
      change task.earliest ≤ (redeemed lifeSource position (proposal quantity)).raw.clock
      rw [the_paid_grant_microsteps_keep_the_real_clock lifeSource position (proposal quantity) paid]
      change task.earliest ≤ lifeSource.raw.clock
      rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
      decide +kernel
    · rw [request]
      exact ⟨rfl, rfl, rfl⟩
  have edge := (live.mem_edgeCarrier_iff (slot, ordinal)).mpr ⟨left, Finset.mem_univ _, eligible⟩
  refine ⟨{(slot, ordinal)}, live.singleton_mem_matchings edge, ?_⟩
  change ({(slot, ordinal)} : Finset _).card = live.leftCarrier.card
  rw [Finset.card_singleton]
  change 1 = (Finset.univ.filter fun slot : Fin task.slots.length => (task.slots.get slot).goods ≠ []).card
  decide +kernel

theorem actual_eligibility (quantity : ℚ) (positive : 0 < quantity) (paid : PaidAt lifeSource position quantity) :
    Eligible lifeSource position [] task (proposal quantity) where
  standing := ⟨every_original_person_keeps_actual_standing false, List.not_mem_nil,
    every_original_person_keeps_actual_standing true, List.not_mem_nil,
    ⟨_, List.mem_cons_self, rfl, _, List.mem_cons_self, by decide⟩⟩
  positive := positive
  native := Innovation.Contribution.Pricing.Consumers.Actual.source_ready
  review := Innovation.Contribution.Pricing.Consumers.Actual.source_review
  grant := paid.qualified
  preparation := by simp [proposal, Execution.inventory]
  continuation := actual_service_is_independent quantity paid
  served := by
    apply Clock.Window.a_fully_paid_script_ending_in_time_serves_every_original_window _ _ _
      (actual_exit_service_after_redemption quantity paid)
    rw [Execution.a_paid_primitive_trace_keeps_the_actual_clock (actual_continuation quantity paid).1,
      the_paid_grant_microsteps_keep_the_real_clock lifeSource position (proposal quantity) paid]
    change lifeSource.raw.clock ≤ task.deadline
    rw [the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    decide +kernel

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Consumers
