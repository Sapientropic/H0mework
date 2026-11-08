import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers.Positions
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Deadline.Terminal

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction Execution
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Consumers (liveClock halfFee)

noncomputable section

private abbrev first := next lifeSource (some (.primitive halfFee))

private theorem first_clock : first.raw.clock = liveClock := by
  have before := the_actual_script_never_runs_the_clock_backwards lifeSource [some (.primitive halfFee)]
  have after := the_actual_script_never_runs_the_clock_backwards first [none]
  change liveClock ≤ first.raw.clock at before
  change first.raw.clock ≤ early.raw.clock at after
  exact le_antisymm (after.trans_eq early_commit) before

private theorem actual_cut_between_debits (time : ℚ) (started : liveClock ≤ time) (beforeLate : time < lateClock) :
    Liquidity.committedPrefix time lifeSource mixedScript = earlyScript := by
  have firstIncluded : first.raw.clock ≤ time := first_clock.symm ▸ started
  have earlyIncluded : early.raw.clock ≤ time := early_commit.symm ▸ started
  have lateExcluded : ¬ (next early (some (.execute lateWord))).raw.clock ≤ time := by
    rw [late_commit]
    exact not_le_of_gt beforeLate
  change Liquidity.committedPrefix time lifeSource
    (some (.primitive halfFee) :: none :: some (.execute lateWord) :: drain (next early (some (.execute lateWord)))) =
      [some (.primitive halfFee), none]
  rw [Liquidity.committedPrefix, if_pos firstIncluded]
  change some (.primitive halfFee) :: Liquidity.committedPrefix time first
    (none :: some (.execute lateWord) :: drain (next early (some (.execute lateWord)))) = _
  rw [Liquidity.committedPrefix]
  change some (.primitive halfFee) :: (if early.raw.clock ≤ time then
    none :: Liquidity.committedPrefix time early
      (some (.execute lateWord) :: drain (next early (some (.execute lateWord)))) else []) = _
  rw [if_pos earlyIncluded]
  rw [Liquidity.committedPrefix, if_neg lateExcluded]

theorem the_original_mixed_script_needs_no_extra_stock (schedule : Agenda Bool Bool Bool) (key : Bool × Bool) :
    (stockProfile schedule lifeSource mixedScript).rollingReserveThrough
      (Liquidity.beforeStock lifeSource mixedScript) (terminalTime lifeSource mixedScript) key ≤ 0 := by
  let stock := stockProfile schedule lifeSource mixedScript
  have nonnegative (time : ℚ) (started : liveClock ≤ time) : 0 ≤ stock.actualStock time key := by
    unfold stock stockProfile Settlement.stockView
    rw [Liquidity.profile_stock_is_original_stock_at_the_commit_cut]
    by_cases finished : lateClock ≤ time
    · rw [Liquidity.committedPrefix_all _ _ _ (mixed_terminal_clock.trans_le finished)]
      exact mixed_terminal_stock key.1 key.2
    · rw [actual_cut_between_debits time started (lt_of_not_ge finished)]
      exact early_stock key.1 key.2
  rw [Liquidity.Profile.rollingReserveThrough_fits_iff]
  refine ⟨le_rfl, ?_, ?_⟩
  · intro time started _
    change stock.outstandingDue time key - stock.actualStock time key ≤ 0
    rw [(Settlement.the_stock_view_has_no_due_rows time key).1, zero_sub]
    exact neg_nonpos.mpr (nonnegative time started)
  · intro position _
    change stock.pastDue (stock.commit position) key + stock.debit position key ≤
      Liquidity.beforeStock lifeSource mixedScript position key + 0
    rw [(Settlement.the_stock_view_has_no_due_rows (stock.commit position) key).2, zero_add, add_zero]
    exact Liquidity.actual_debit_uses_pre_credit_stock lifeSource mixedScript Settlement.address Settlement.deadline
      (fun _ => 0) (fun _ _ => 0) position (original_before_stock position) key

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Due.Service.Mixed.Consumers
