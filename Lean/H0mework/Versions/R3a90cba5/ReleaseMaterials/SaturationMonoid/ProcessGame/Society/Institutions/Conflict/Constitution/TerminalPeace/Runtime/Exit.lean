import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Runtime.Living
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Check

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Conflict.Consumers.Evolving (C)
open Civil.Persistence (timelyUses)
open Quantities.Execution (endAt next next_input inventory)
open ExposureGuard

noncomputable section

private theorem sum_after_filter_le {Item : Type} (keep : Item → Bool) (value : Item → ℚ)
    (nonnegative : ∀ item, 0 ≤ value item) (items : List Item) :
    ((items.filter keep).map value).sum ≤ (items.map value).sum := by
  induction items with
  | nil => exact le_rfl
  | cons item _ earlier =>
    cases accepted : keep item with
    | false =>
      simp only [List.filter_cons, accepted, Bool.false_eq_true, if_false, List.map_cons, List.sum_cons]
      exact earlier.trans (le_add_of_nonneg_left (nonnegative item))
    | true =>
      simp only [List.filter_cons, accepted, if_true, List.map_cons, List.sum_cons]
      exact add_le_add_right earlier _

private theorem the_timely_part_is_at_most_the_actual_delivery
    (deadline : ℚ) (command : List Bool) (person : Bool) (cut : C) (word : Original.Word) :
    timelyUses deadline command (person, .necessity, true, 1) cut word ≤
      Quantities.Demand.delivered cut word person .necessity true := by
  rw [Quantities.Demand.delivered_is_from_original_inventory]
  induction word generalizing cut with
  | nil => exact le_rfl
  | cons input word earlier =>
    let value (item : Original.Item) := flowAt (Optimality.Cost.actualPart cut.native.handlerFace.rootRead
      item.before item.request (.use .necessity)) person true
    let own := fun item : Original.Item => decide (Civil.Persistence.OwnMaterial cut command item)
    have weights : ∀ item, 0 ≤ value item :=
      fun item => Optimality.Cost.actualPart_nonnegative _ item.before item.request _ _ _
    have law : (next cut input).native.handlerFace.rootRead = cut.native.handlerFace.rootRead :=
      congrArg Physical.Public.interpreter (next_input cut input)
    have tail := earlier (next cut input)
    rw [law] at tail
    have items : inventory cut (input :: word) =
        Boundary.Actual.items cut input ++ inventory (next cut input) word :=
      Quantities.Execution.inventory_append cut [input] word
    rw [items, List.map_append, List.sum_append]
    change (if (next cut input).raw.clock ≤ deadline then
        (((Boundary.Actual.items cut input).filter own).map value).sum else 0) +
        timelyUses deadline command (person, .necessity, true, 1) (next cut input) word ≤
      ((Boundary.Actual.items cut input).map value).sum + ((inventory (next cut input) word).map value).sum
    refine add_le_add ?_ tail
    split
    · exact sum_after_filter_le own value weights _
    · exact List.sum_nonneg (fun amount found => by
        obtain ⟨item, _, rfl⟩ := List.mem_map.mp found
        exact weights item)

private theorem a_retained_unfunded_need_prevents_independent_exit
    (seed : C) (community : Bool → Bool) (anchor history : Original.Word)
    (control : Original.Raw → List Bool) (person : Bool)
    (needed : (person, .necessity, true, (1 : ℚ)) ∈ Exit.needCells seed community anchor history)
    (gap : ∀ word, Quantities.Demand.delivered (endAt seed history) word person .necessity true < 1) :
    ¬ Exit.Available seed community anchor history control := by
  rintro ⟨word, checked⟩
  let current := endAt seed history
  have enough := checked.floor _ needed
  have physical := the_timely_part_is_at_most_the_actual_delivery (Civil.Persistence.Window.at current).deadline
    (control current.raw) person current word
  exact (not_le_of_gt (gap word)) (enough.trans physical)

private theorem the_original_exit_need_is_retained (history : Original.Word) :
    (false, .necessity, true, (1 : ℚ)) ∈ Exit.needCells Original.seed Original.community Original.history history := by
  have original : Original.occurrence ∈ Reparation.Actual.originalLosses Original.seed Original.community Original.history := by
    rw [Original.the_original_loss_is_the_only_filed_occurrence]
    exact List.mem_singleton_self _
  have victim := every_original_victim_is_a_bearer Original.seed Original.community Original.history Original.occurrence original
  rw [Original.original_victim] at victim
  have inRoster := Exit.original_bearer_keeps_their_exit_row Original.seed Original.community
    Original.history history false victim
  unfold Exit.needCells Exit.needsAt Capitalism.Universal.Abolition.Material.originalRequirements
  refine List.mem_dedup.mpr (List.mem_append_left _ (List.mem_flatMap.mpr ⟨false, inRoster, ?_⟩))
  rw [show (endAt Original.seed Original.history).native.input = _ from Original.same_source]
  change (false, Use.necessity, true, (1 : ℚ)) ∈ [(false, Use.necessity, true, amount Bool [(true, 1)] true)]
  decide +kernel

/-- The same protected whole state that actually paid the first period
can no longer realize a fresh independent exit with the original material. -/
theorem the_paid_protected_successor_has_no_original_independent_exit (control : Original.Raw → List Bool) :
    ¬ Exit.Available Original.seed Original.community Original.history paidLivingVisit.history control :=
  a_retained_unfunded_need_prevents_independent_exit _ _ _ _ control false
    (the_original_exit_need_is_retained _) (fun word => lt_of_eq_of_lt
      (the_protected_successor_cannot_deliver_food word false) zero_lt_one)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace
