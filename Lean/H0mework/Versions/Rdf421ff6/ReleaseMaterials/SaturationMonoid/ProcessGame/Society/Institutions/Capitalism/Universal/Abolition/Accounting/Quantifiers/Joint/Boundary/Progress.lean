import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Cells

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

private theorem filtered_count_mono {α : Type} (items : List α) (left right : α → Bool)
    (included : ∀ item ∈ items, left item = true → right item = true) :
    (items.filter left).length ≤ (items.filter right).length := by
  induction items with
  | nil => exact le_rfl
  | cons item rest inherited =>
      have tail := inherited (fun next member => included next (List.mem_cons_of_mem item member))
      by_cases l : left item = true <;> by_cases r : right item = true
      · simpa [List.filter,l,r] using Nat.succ_le_succ tail
      · exact (r (included item List.mem_cons_self l)).elim
      · simpa [List.filter,l,r] using Nat.le_succ_of_le tail
      · simpa [List.filter,l,r] using tail

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

theorem an_actual_word_cannot_increase_the_number_of_original_unpaid_cells
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument) :
    budget seed claim (Current.advance seed claim current word) ≤ budget seed claim current := by
  apply filtered_count_mono
  intro cell _ observed
  exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true observed)
    (actual_word_never_refills_either_original_row seed claim current word cell))

theorem strict_source_progress_really_clears_an_original_cell
    (current : Current seed claim) (word : RawEvent Party Good Port Technology Instrument)
    (progress : budget seed claim (Current.advance seed claim current word) < budget seed claim current) :
    ∃ cell ∈ scope seed, 0 < remaining seed claim current cell ∧
      remaining seed claim (Current.advance seed claim current word) cell = 0 := by
  by_contra absent
  have reverse : budget seed claim current ≤ budget seed claim (Current.advance seed claim current word) := by
    apply filtered_count_mono
    intro cell original observed
    have positive : 0 < remaining seed claim current cell := of_decide_eq_true observed
    have nonzero : remaining seed claim (Current.advance seed claim current word) cell ≠ 0 :=
      fun zero => absent ⟨cell,original,positive,zero⟩
    exact decide_eq_true (lt_of_le_of_ne (remaining_nonnegative seed claim _ cell) (Ne.symm nonzero))
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
