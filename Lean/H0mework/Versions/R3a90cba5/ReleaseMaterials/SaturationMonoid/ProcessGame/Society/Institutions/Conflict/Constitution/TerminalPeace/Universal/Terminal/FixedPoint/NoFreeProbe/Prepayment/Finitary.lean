import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Budget

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

variable (law : RawLaw Party Good Port Technology Instrument)
  (base : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)
  (bid : ReviewBid Party Good Port Technology Instrument)

private def budgetCells : List (Party × Good) :=
  Balance.cells law base word ++ bid.expenses.map (fun lot => (bid.payer, lot.1))

private theorem outside_budgetCells (person : Party) (good : Good)
    (absent : (person, good) ∉ budgetCells law base word bid) :
    bid.fee person good = 0 ∧ Balance.gain law base word person good = 0 := by
  obtain ⟨debit, credit⟩ := Balance.no_effect_outside_original_support law base word person good
    (fun listed => absent (List.mem_append_left _ listed))
  refine ⟨?_, by simp only [Balance.gain, debit, credit, sub_self]⟩
  by_cases same : person = bid.payer
  · subst person
    rw [ReviewBid.fee, if_pos rfl]
    apply amount_zero_of_absent
    intro lot listed address
    exact absent (List.mem_append_right _ (List.mem_map.mpr ⟨lot, listed, by rw [address]⟩))
  · simp only [ReviewBid.fee, if_neg same]

/-- Evaluate the original productive word, then test the signed charge on
the union of original production and bill coordinates. No type-wide scan
of people or goods is needed. -/
def budgetCheck : Bool :=
  let executed := law.execute base 0 word
  let quantities := (budgetCells law base word bid).map fun cell =>
    (bid.fee cell.1 cell.2,
      law.totalCredit executed.items cell.1 cell.2 - law.totalDebit executed.items cell.1 cell.2)
  decide (law.Valid executed.final (reviewRequest bid.payer bid.port bid.expenses)) &&
    (quantities.all (fun amounts => decide (0 ≤ amounts.1 ∧ amounts.1 ≤ amounts.2)) &&
      quantities.any (fun amounts => decide (amounts.1 < amounts.2)))

/-- The finite support test is exact even for a submitted bill outside the
tariff and for a word with negative net production. -/
theorem budgetCheck_iff : budgetCheck law base word bid = true ↔ BaseBudget law base word bid := by
  simp only [budgetCheck, Bool.and_eq_true, List.all_map, List.any_map, List.all_eq_true,
    List.any_eq_true, Function.comp_apply, decide_eq_true_eq]
  change
    (law.Valid (law.execute base 0 word).final (reviewRequest bid.payer bid.port bid.expenses) ∧
      (∀ cell ∈ budgetCells law base word bid, 0 ≤ bid.fee cell.1 cell.2 ∧
        bid.fee cell.1 cell.2 ≤ Balance.gain law base word cell.1 cell.2) ∧
      (∃ cell ∈ budgetCells law base word bid, bid.fee cell.1 cell.2 <
        Balance.gain law base word cell.1 cell.2)) ↔ BaseBudget law base word bid
  constructor
  · rintro ⟨legal, within, ⟨⟨person, good⟩, _, strict⟩⟩
    have every (payer : Party) (item : Good) : 0 ≤ bid.fee payer item ∧
        bid.fee payer item ≤ Balance.gain law base word payer item := by
      by_cases listed : (payer, item) ∈ budgetCells law base word bid
      · exact within _ listed
      · obtain ⟨zeroFee, zeroGain⟩ := outside_budgetCells law base word bid payer item listed
        simp only [zeroFee, zeroGain, le_refl, and_self]
    exact ⟨legal, fun p g => (every p g).1, fun p g => (every p g).2, ⟨person, good, strict⟩⟩
  · intro budget
    refine ⟨budget.legal, fun cell _ => ⟨budget.nonnegative cell.1 cell.2, budget.fits cell.1 cell.2⟩, ?_⟩
    obtain ⟨person, good, strict⟩ := budget.surplus
    refine ⟨(person, good), ?_, strict⟩
    by_contra absent
    obtain ⟨zeroFee, zeroGain⟩ := outside_budgetCells law base word bid person good absent
    rw [zeroFee, zeroGain] at strict
    exact (lt_irrefl 0) strict

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
