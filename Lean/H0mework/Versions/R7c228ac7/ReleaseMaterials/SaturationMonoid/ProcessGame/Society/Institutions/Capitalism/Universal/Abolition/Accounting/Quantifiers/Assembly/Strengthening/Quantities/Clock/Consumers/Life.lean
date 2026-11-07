import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Term
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeSettlement
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.WorkHours
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Consumers

open Source.Program PublicFunction Abolition.Root.Registered
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary)
open Innovation.Contribution.Pricing.Consumers.Actual
  (task life source_input_is_the_original_registered_input the_actual_quote_cut_comes_from_the_paid_original_food_repair)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource lifeScript lifeTrace lifeTarget life_target_is_the_actual_script_successor
  the_two_actual_life_payments_write_the_original_ledger)

noncomputable section

private def firstOrdinal : Fin (Execution.inventory lifeSource lifeScript).length :=
  ⟨0, by unfold lifeScript; rw [Execution.primitive_inventory lifeTrace 0]; decide⟩

private theorem first_ordinal_is_the_actual_false_member_debit :
    (Execution.inventory lifeSource lifeScript).get firstOrdinal = ⟨0, lifeSource.raw, life false⟩ := by
  have actual : (Execution.inventory lifeSource lifeScript)[0]? = some ⟨0, lifeSource.raw, life false⟩ := by
    unfold lifeScript
    rw [Execution.primitive_inventory lifeTrace 0]
    rfl
  have inside : 0 < (Execution.inventory lifeSource lifeScript).length := firstOrdinal.isLt
  rw [List.getElem?_eq_getElem inside] at actual
  exact Option.some.inj actual

theorem the_original_service_has_a_distinct_paid_slot : FullyServed lifeSource task lifeScript := by
  let live := geometry lifeSource task lifeScript
  let slot : Fin task.slots.length := ⟨0, by decide⟩
  have left : slot ∈ live.leftCarrier := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by decide⟩
  have feasible : live.Feasible slot firstOrdinal := by
    change task.earliest ≤ ((Execution.inventory lifeSource lifeScript).get firstOrdinal).before.clock ∧
      (Physical.Public.interpreter lifeSource.native.input).Valid
        ((Execution.inventory lifeSource lifeScript).get firstOrdinal).before
        ((Execution.inventory lifeSource lifeScript).get firstOrdinal).request ∧
      Exit.Necessity.UseMatches ((Execution.inventory lifeSource lifeScript).get firstOrdinal).request.operation
        (task.slots.get slot).bearer (task.slots.get slot).goods (task.slots.get slot).purpose
    rw [first_ordinal_is_the_actual_false_member_debit, source_input_is_the_original_registered_input,
      the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    decide +kernel
  have edge := (live.mem_edgeCarrier_iff (slot, firstOrdinal)).mpr ⟨left, Finset.mem_univ _, feasible⟩
  refine ⟨{(slot, firstOrdinal)}, live.singleton_mem_matchings edge, ?_⟩
  change ({(slot, firstOrdinal)} : Finset _).card = live.leftCarrier.card
  rw [Finset.card_singleton]
  decide +kernel

private theorem the_actual_service_uses_the_current_clock :
    (Execution.endAt lifeSource lifeScript).raw.clock = lifeSource.raw.clock := by
  rw [life_target_is_the_actual_script_successor,
    Innovation.Contribution.Pricing.Root.Runtime.Trace.raw_is_the_complete_original_execution lifeTrace]
  exact (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
      (Physical.Public.interpreter lifeSource.native.input) lifeSource.raw 0 _).1

abbrev initialTime : EReal := ((lifeSource.raw.clock : ℝ) : EReal)

theorem the_original_public_service_attains_the_tight_clock_boundary :
    deadlineCut lifeSource task = (initialTime : WithTop EReal) ∧ PaidBy lifeSource task initialTime := by
  have paid := the_two_actual_life_payments_write_the_original_ledger
  have clock : completionClock lifeSource lifeScript = initialTime := by
    unfold completionClock initialTime
    rw [the_actual_service_uses_the_current_clock]
  have served := the_original_service_has_a_distinct_paid_slot
  refine ⟨?_, ⟨lifeScript, paid, served, clock.le⟩⟩
  apply le_antisymm
  · have bound := Bounds.lower_le lifeSource
      (Bounds.Restriction.restrict (inspectService lifeSource task) (completionClock lifeSource)) lifeScript paid.toFeasible
    rw [Bounds.Restriction.restrict, (service_pass_iff_fully_paid lifeSource task lifeScript).mpr served, clock] at bound
    exact bound
  · apply le_of_not_gt
    intro earlier
    obtain ⟨script, _, _, timely⟩ := Bounds.Restriction.a_strict_limit_produces_a_paid_qualified_script
      lifeSource (inspectService lifeSource task) (completionClock lifeSource) _ earlier
    have impossible := WithTop.coe_lt_coe.mp timely
    have nondecreasing := sub_nonneg.mp (Recovery.elapsed_nonnegative lifeSource script)
    have strict : (Execution.endAt lifeSource script).raw.clock < lifeSource.raw.clock :=
      Rat.cast_lt.mp (EReal.coe_lt_coe_iff.mp impossible)
    exact (not_lt_of_ge nondecreasing) strict

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Consumers
