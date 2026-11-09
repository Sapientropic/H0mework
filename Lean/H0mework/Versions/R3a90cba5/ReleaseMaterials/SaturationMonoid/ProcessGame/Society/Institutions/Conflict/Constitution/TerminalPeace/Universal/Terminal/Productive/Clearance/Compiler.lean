import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Batch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Pilot
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Cycle

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Reparation.Actual (Occurrence ReceiptAnswers Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)

local notation "Word" => Script Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

variable (pilot : ProductionPilot loss)

/-- One produced candidate, including the actually funded prefix and the
living realization obtained after the original ledger is cleared. -/
structure ProducedClearance where
  cycles : Nat
  word : Word
  approved : NativeFundingApproved loss pilot answers cycles
  funded : FundingCovers loss pilot answers cycles
  leastCycles : ∀ n, NativeFundingApproved loss pilot answers n → FundingCovers loss pilot answers n → cycles ≤ n
  withinBudget : cycles ≤ fundingCycles (Occurrence.originState loss).stack.balances (fun _ => 0) (gainAt loss pilot)
  includesFunding : (fundingWord loss pilot.move cycles).IsPrefix word
  clock : (originalRaw loss).clock + (cycles : ℚ) * pilot.quantum ≤ (prefixRaw loss word).clock
  allPaid : WholeCleared loss answers word
  run : Realization loss answers (fun _ => True) word
  originalRows : (prefixRows loss answers word).map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst

/-- Calculate a finite original funding prefix, write the actual payments,
and restart the same production at the resulting protected inventory. -/
def produceClearance (channels : IndependentReceiptChannels loss answers)
    (grows : CoversEveryOriginalDebt loss pilot)
    (release : FundingRelease loss pilot answers (fundingBound loss pilot grows).val) :
    ProducedClearance loss answers pilot := by
  classical
  have bounded := a_finite_original_funding_prefix_covers_all_cells loss pilot answers grows release
  have canFund : ∃ n, NativeFundingApproved loss pilot answers n ∧ FundingCovers loss pilot answers n :=
    bounded.imp fun _ h => h.2
  let n := Nat.find canFund
  have paid := Nat.find_spec canFund
  have within : n ≤ (fundingBound loss pilot grows).val := by
    obtain ⟨m, affordable, enough⟩ := bounded
    exact (Nat.find_min' canFund enough).trans affordable
  let actual := actual_funding loss pilot answers paid.1
  let cleared := clearFundedPortfolio loss answers channels (originalRaw loss).stock
    pilot.reserve_nonnegative (fundingWord loss pilot.move n) actual.1 actual.2.1 paid.2
  let finish := prefixRaw loss cleared.word
  let start := originalRaw loss
  let extra := fun person good => finish.stock person good - start.stock person good
  have extra_nonnegative (person : Party) (good : Good) : 0 ≤ extra person good :=
    sub_nonneg.mpr (cleared.reserved person good)
  have law := pilot.accumulation
  have replay := pilot.move.paid.replay law.timing law.reserve law.accumulating _ law.positive law.duration n
  have restored : finish = (start.addReserve extra).retime finish.clock finish.round := by
    apply RawCurrent.ext
    · funext person good
      change finish.stock person good = start.stock person good + (finish.stock person good - start.stock person good)
      ring
    · exact cleared.claims.trans ((congrArg (fun raw : Raw => raw.claims) actual.2.2.1).trans replay.2.2.1)
    · exact cleared.technology.trans ((congrArg (fun raw : Raw => raw.technology) actual.2.2.1).trans replay.2.2.2.1)
    · rfl
    · rfl
  let route := restored.symm ▸
    pilot.move.trajectory_after_restoring law extra extra_nonnegative finish.clock finish.round pilot.registration
  let live : Realization loss answers (fun _ => True) cleared.word :=
    ⟨⟨Or.inr trivial, cleared.eligible⟩, cleared.ready, none, trivial, route, trivial⟩
  have origins := Occurrence.reached_origins answers loss cleared.word
  rw [Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers (Occurrence.history loss)
    (Occurrence.history loss) cleared.word cleared.eligible, ← Occurrence.originState_origins] at origins
  exact ⟨n, cleared.word, paid.1, paid.2, fun _ approved funded => Nat.find_min' canFund ⟨approved, funded⟩,
    within, cleared.beginsWith,
    actual.2.2.2.2.trans_eq cleared.clock.symm, cleared.cleared, live, origins⟩

theorem finite_original_losses_are_cleared_by_production
    (channels : IndependentReceiptChannels loss answers) (grows : CoversEveryOriginalDebt loss pilot)
    (release : FundingRelease loss pilot answers (fundingBound loss pilot grows).val) :
    let produced := produceClearance loss answers pilot channels grows release
    ∃ word run minimum shortest all fewest,
      source_generated_terminal_peace loss answers (fun _ => True) ProductionMenu.empty .wholePortfolio =
        .attained word run minimum shortest ∧
      compileWhole loss answers (fun _ => True) = .paid word run all fewest ∧
      word.length ≤ produced.word.length ∧
      (prefixRows loss answers word).map Prod.fst = (Occurrence.originState loss).stack.balances.map Prod.fst := by
  let produced := produceClearance loss answers pilot channels grows release
  have viable := realization_has_an_exactly_viable_source produced.run
  obtain ⟨word, run, minimum, shortest, all, fewest, first, whole⟩ :=
    both_portfolio_reports_select_the_same_whole_terminal loss answers (fun _ => True) ProductionMenu.empty
      ⟨produced.word, viable, produced.allPaid⟩
  have originals := Occurrence.reached_origins answers loss word
  rw [Occurrence.eligible_preserves_the_literal_original_loss_inventory community answers (Occurrence.history loss)
    (Occurrence.history loss) word run.allowed.2, ← Occurrence.originState_origins] at originals
  exact ⟨word, run, minimum, shortest, all, fewest, first, whole, fewest _ viable produced.allPaid, originals⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance
