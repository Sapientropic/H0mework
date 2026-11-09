import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Consumers.Frontier.Inventory

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt inventory)
open Conflict.Consumers.Evolving (compact)

noncomputable section

private theorem first_is_original : firstProduction loss [grow] = beforeSale := by
  rw [firstProduction, original_drain_exact]
  rfl

theorem credit_first : ProducesAtFirstWrite loss [grow] := by
  unfold ProducesAtFirstWrite
  dsimp only
  rw [original_drain_exact, at_original]
  let item : Original.Item := ⟨0, Original.cut.raw, grow⟩
  refine ⟨item, ?_, false, false, rfl, ?_⟩
  · obtain ⟨written, _⟩ := first_production_is_written true
    have items := written.inventory
    rw [at_original] at items
    rw [items]
    exact List.mem_singleton_self _
  · change 0 < flowAt ((Physical.Public.interpreter Original.cut.native.input).actualCredit
      Original.cut.raw grow) false false
    rw [Original.same_source, Original.cut_raw]
    decide +kernel

theorem first_production_precedes_the_closed_word : (firstProduction loss [grow]).IsPrefix closed := by
  rw [first_is_original, closed, beforePayment, beforeDelivery]
  exact ((List.prefix_append beforeSale _).trans (List.prefix_append _ _)).trans (List.prefix_append _ _)

theorem opening_production_is_written : ProductionWrite replies loss (openingDrain loss) [grow] := by
  rw [original_drain_exact]
  obtain ⟨write, _⟩ := first_production_is_written true
  exact write

private theorem closed_is_feasible : Feasible loss replies reserve (firstProduction loss [grow]) offers closed :=
  ⟨first_production_precedes_the_closed_word, every_original_material_position_keeps_the_reserve,
    whole_original_row_is_paid, original_live_entry⟩

/-- This actual exchange gains stock at a different original account
first. The ninth visit is a certified bound on the first possible cofinal entry. -/
theorem the_original_compiler_selects_the_least_paid_visit :
    ∃ original credit result,
      compileJoint loss replies reserve [grow] offers = .paid original credit result ∧
      result.word.length ≤ 9 ∧
      ∀ visits, FeasibleBy loss replies reserve (firstProduction loss [grow]) offers visits ↔
        result.word.length ≤ visits := by
  obtain ⟨original, credit, result, compiled⟩ :=
    (compileJoint_pays_iff loss replies reserve [grow] offers).mpr
      ⟨opening_production_is_written, credit_first, closed, closed_is_feasible⟩
  exact ⟨original, credit, result, compiled, result.earliest closed closed_is_feasible,
    fun visits => result.feasible_by_iff loss replies reserve _ offers visits⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.OriginalExchange
