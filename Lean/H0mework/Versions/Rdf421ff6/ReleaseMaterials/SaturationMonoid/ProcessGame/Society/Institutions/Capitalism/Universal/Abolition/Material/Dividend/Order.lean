import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)

theorem checks_of_exact_endpoints
    (baseline replacement : List (RawEvent Party Good Port Technology Instrument))
    (financial : NonFinancial (baseline ++ replacement))
    (timely : (final law current replacement).clock ≤ (final law current baseline).clock)
    (all : ∀ person good, (final law current baseline).stock person good ≤ (final law current replacement).stock person good)
    (one : ∃ person good, (final law current baseline).stock person good < (final law current replacement).stock person good) :
    Checks law current baseline replacement := by
  refine ⟨financial, timely, ?_, ?_⟩
  · intro cell _affected
    rw [dividend_is_one_actual_stock_difference]
    exact sub_nonneg.mpr (all cell.1 cell.2)
  · obtain ⟨person, good, strict⟩ := one
    have affected : (person, good) ∈ comparisonCells law current baseline replacement := by
      by_contra absent
      have missing : (person, good) ∉ cells law current baseline ∧ (person, good) ∉ cells law current replacement := by
        simpa only [comparisonCells, List.mem_dedup, List.mem_append, not_or] using absent
      rw [final_stock_is_exact_net, final_stock_is_exact_net,
        no_effect_outside_actual_cells law current baseline person good missing.1,
        no_effect_outside_actual_cells law current replacement person good missing.2] at strict
      exact (lt_irrefl _ strict)
    refine ⟨(person, good), affected, ?_⟩
    rw [dividend_is_one_actual_stock_difference]
    exact sub_pos.mpr strict

theorem checks_transitive
    {first middle last : List (RawEvent Party Good Port Technology Instrument)}
    (earlier : Checks law current first middle) (later : Checks law current middle last) :
    Checks law current first last := by
  apply checks_of_exact_endpoints law current first last
  · intro word present
    rcases List.mem_append.mp present with initial | finalWord
    · exact earlier.1 word (List.mem_append_left _ initial)
    · exact later.1 word (List.mem_append_right _ finalWord)
  · exact later.2.1.trans earlier.2.1
  · intro person good
    exact (all_bearers_and_goods_keep_their_material_share law current first middle earlier person good).trans
      (all_bearers_and_goods_keep_their_material_share law current middle last later person good)
  · obtain ⟨person, good, strict⟩ := one_real_unit_strictly_increases law current first middle earlier
    exact ⟨person, good, strict.trans_le
      (all_bearers_and_goods_keep_their_material_share law current middle last later person good)⟩

theorem checks_irreflexive (periods : List (RawEvent Party Good Port Technology Instrument)) :
    ¬ Checks law current periods periods := by
  intro checked
  obtain ⟨person, good, impossible⟩ := one_real_unit_strictly_increases law current periods periods checked
  exact lt_irrefl _ impossible

#print axioms checks_of_exact_endpoints
#print axioms checks_transitive
#print axioms checks_irreflexive

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend
