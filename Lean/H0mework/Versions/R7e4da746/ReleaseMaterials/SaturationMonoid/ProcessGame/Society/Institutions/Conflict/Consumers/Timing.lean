import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.History

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime
open Conflict.Root

noncomputable section

private def registration := Quantities.Execution.primitiveScript [issue]

private def proposals (_ : C) : List W × List W := ([conflict], [peace])

private def atCut := pressureAt Original.source registration decisionStock proposals

private theorem before_issue_has_no_peace_settlement : atCut 0 = none := by
  change pressure Original.source decisionStock [conflict] [peace] = none
  apply (pressure_is_absent_iff_a_menu_has_no_paid_word _ _ _ _).mpr
  right
  intro word listed paid
  have same := List.mem_singleton.mp listed
  subst word
  have original := paid.authorized ⟨0, Original.source.raw, settle⟩ List.mem_cons_self
  rw [Original.source_input_is_the_original_registered_input,
    Original.the_actual_quote_cut_comes_from_the_paid_original_food_repair] at original
  have absent : ¬ compact.law.Valid Original.quoteCut settle := by decide +kernel
  exact absent original

private theorem pending_issue_has_no_paid_comparison : atCut 1 = none := by
  change pressure (afterBody Original.source issue) decisionStock [conflict] [peace] = none
  apply (pressure_is_absent_iff_a_menu_has_no_paid_word _ _ _ _).mpr
  right
  intro word listed paid
  have same := List.mem_singleton.mp listed
  subst word
  have valid : (Physical.Public.interpreter Original.source.native.input).Valid Original.source.raw issue := by
    rw [Original.source_input_is_the_original_registered_input,
      Original.the_actual_quote_cut_comes_from_the_paid_original_food_repair]
    decide +kernel
  have work := the_actual_body_must_consume_its_original_native_head Original.source issue
    Original.source_ready Original.source_review rfl valid
  exact (paid.trace.a_nonempty_execution_starts_at_the_actual_ready_boundary (by simp [peace])).1 work

private theorem registered_issue_has_positive_pressure : atCut 2 = some 4 := by
  change pressure source decisionStock [conflict] [peace] = some 4
  rw [pressure_of_two_paid_words decisionStock conflictPaid peacePaid, old_war_peace_gap]

theorem first_crossing_occurs_at_original_native_registration :
    onset Original.source registration decisionStock proposals = some 2 ∧
      peak Original.source registration decisionStock proposals = some (2, 4) := by
  constructor
  · change Threshold.firstPositive atCut [0, 1, 2] = some 2
    simp [Threshold.firstPositive, before_issue_has_no_peace_settlement,
      pending_issue_has_no_paid_comparison, registered_issue_has_positive_pressure]
  · change Threshold.peak atCut [0, 1, 2] = some (2, 4)
    simp only [Threshold.peak, List.filterMap_cons, before_issue_has_no_peace_settlement,
      pending_issue_has_no_paid_comparison, registered_issue_has_positive_pressure,
      Option.map_none, Option.map_some, List.filterMap_nil]
    rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Consumers.Evolving
