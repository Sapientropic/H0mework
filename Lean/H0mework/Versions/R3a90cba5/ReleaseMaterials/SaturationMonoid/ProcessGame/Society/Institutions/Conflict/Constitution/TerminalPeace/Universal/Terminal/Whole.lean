import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Minimum

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Reparation.Actual (ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (registered : Script Party Good Port Technology Instrument → Prop)
  (offers : ProductionMenu Party Good Port Technology Instrument := ProductionMenu.empty)

inductive WholeOutcome where
  | paid (word : Script Party Good Port Technology Instrument)
      (actual : Realization loss answers registered word offers) (all : WholeCleared loss answers word)
      (fewestVisits : ∀ other : Script Party Good Port Technology Instrument,
        ViableEntry loss answers registered other offers → WholeCleared loss answers other → word.length ≤ other.length)
  | residual (best : Outcome loss answers registered offers)
      (every : ∀ word : Script Party Good Port Technology Instrument,
        Realization loss answers registered word offers →
        ∃ row ∈ (Occurrence.reached answers loss word).stack.balances, 0 < row.2.remaining)

private theorem portfolio_minimum_is_zero
    (canPay : ∃ word : Script Party Good Port Technology Instrument,
      ViableEntry loss answers registered word offers ∧ WholeCleared loss answers word) :
    liveInfimum loss answers registered offers .wholePortfolio = 0 ∧
    liveInfimum loss answers registered offers .wholePortfolio ∈ liveValues loss answers registered offers .wholePortfolio := by
  obtain ⟨word, live, all⟩ := canPay
  have exactValue := (portfolio_value_is_zero_iff loss answers word).mpr all
  have upper := (liveInfimum_le_every_actual_terminal loss answers registered offers .wholePortfolio word live).trans_eq exactValue
  have hasZero : (0 : ℝ) ∈ liveValues loss answers registered offers .wholePortfolio :=
    ⟨word, live, exactValue⟩
  have lower : 0 ≤ liveInfimum loss answers registered offers .wholePortfolio := by
    apply le_csInf ⟨0, hasZero⟩
    rintro amount ⟨actual, _, rfl⟩
    exact settlementValue_nonnegative loss answers .wholePortfolio actual
  have equal := le_antisymm upper lower
  exact ⟨equal, equal.symm ▸ hasZero⟩

private def paidFromOptimum
    (canPay : ∃ word : Script Party Good Port Technology Instrument,
      ViableEntry loss answers registered word offers ∧ WholeCleared loss answers word) :
    Outcome loss answers registered offers .wholePortfolio → WholeOutcome loss answers registered offers
  | .attained word actual minimum fewest =>
    let zero := (portfolio_minimum_is_zero loss answers registered offers canPay).1
    .paid word actual ((portfolio_value_is_zero_iff loss answers word).mp (minimum.trans zero))
      (fun other live cleared => fewest other live
        (((portfolio_value_is_zero_iff loss answers other).mpr cleared).trans zero.symm))
  | .approached missing _ => False.elim (missing (portfolio_minimum_is_zero loss answers registered offers canPay).2)
  | .obstructed failed _ => False.elim (canPay.elim fun word payable => failed word ⟨realize payable.1⟩)

/-- On the fully payable domain, both reports use the same minimum
portfolio visit and the same rooted realization. -/
def compileWhole : WholeOutcome loss answers registered offers := by
  classical
  exact if canPay : ∃ word : Script Party Good Port Technology Instrument,
      ViableEntry loss answers registered word offers ∧ WholeCleared loss answers word then
    paidFromOptimum loss answers registered offers canPay
      (source_generated_terminal_peace loss answers registered offers .wholePortfolio)
  else
    .residual (source_generated_terminal_peace loss answers registered offers) (fun word run => by
      by_contra hidden
      apply canPay
      refine ⟨word, realization_has_an_exactly_viable_source run, ?_⟩
      intro row listed
      exact le_antisymm (le_of_not_gt fun positive => hidden ⟨row, listed, positive⟩) row.2.nonnegative)

theorem both_portfolio_reports_select_the_same_whole_terminal
    (canPay : ∃ word : Script Party Good Port Technology Instrument,
      ViableEntry loss answers registered word offers ∧ WholeCleared loss answers word) :
    ∃ word run minimum shortest all fewest,
      source_generated_terminal_peace loss answers registered offers .wholePortfolio = .attained word run minimum shortest ∧
      compileWhole loss answers registered offers = .paid word run all fewest := by
  classical
  have zero := portfolio_minimum_is_zero loss answers registered offers canPay
  cases selected : source_generated_terminal_peace loss answers registered offers .wholePortfolio with
  | attained word run minimum shortest =>
    have all := (portfolio_value_is_zero_iff loss answers word).mp (minimum.trans zero.1)
    have fewest (other : Script Party Good Port Technology Instrument)
        (viable : ViableEntry loss answers registered other offers) (cleared : WholeCleared loss answers other) :=
      shortest other viable (((portfolio_value_is_zero_iff loss answers other).mpr cleared).trans zero.1.symm)
    refine ⟨word, run, minimum, shortest, all, fewest, rfl, ?_⟩
    rw [compileWhole, dif_pos canPay, selected]
    rfl
  | approached missing _ => exact (missing zero.2).elim
  | obstructed refused _ =>
    obtain ⟨word, live, _⟩ := canPay
    exact (refused word ⟨realize live⟩).elim

theorem simultaneous_clearance_is_generated_exactly_when_a_live_original_prefix_pays_every_row :
    (∃ word actual all fewest, compileWhole loss answers registered offers = .paid word actual all fewest) ↔
      ∃ word : Script Party Good Port Technology Instrument,
        ViableEntry loss answers registered word offers ∧ WholeCleared loss answers word := by
  constructor
  · rintro ⟨word, actual, all, _, _⟩
    exact ⟨word, realization_has_an_exactly_viable_source actual, all⟩
  · rintro ⟨word, viable, all⟩
    cases compileWhole loss answers registered offers with
    | paid exactWord actual cleared fewest => exact ⟨exactWord, actual, cleared, fewest, rfl⟩
    | residual _ left =>
      obtain ⟨row, original, positive⟩ := left word (realize viable)
      exact (ne_of_gt positive (all row original)).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
