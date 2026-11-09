import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalPayment
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Renewal
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Amount

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Joint.OriginalExchange (claim)
open Supply.Consumers (refillWord)

noncomputable section

def afterClear : Original.Raw :=
  { afterTrial with stock := fun person good => if good then 2 else if person then 111 else 121 }

theorem payment_lands_at_the_actual_stock (paid : PaidWrite payerCut (signed true) claim 6) :
    paid.next.physical.raw = afterClear := by
  rw [paid.stock, actualTrial.revisedStock]
  apply RawCurrent.ext
  · funext person good
    cases person <;> cases good <;> decide +kernel
  · rfl
  · rfl
  · rfl
  · rfl

theorem the_revised_original_amount_is_tight :
    paymentUpper payerCut (signed true) claim = 6 := by
  have full := the_original_six_survive_the_new_production.2
  have funded : Funding payerCut (signed true) claim (liveBalance payerCut claim) := full.symm ▸ fullyFunded
  rw [a_funded_full_balance_is_the_exact_upper _ _ _ funded, full]
  norm_num

theorem the_amount_solver_selects_an_actual_six :
    ∃ (q : ℚ) (actual : AmountWritten payerCut (signed true) claim cells allCells q)
        (tight : (q : ℝ) = paymentUpper payerCut (signed true) claim),
      resolve payerCut (signed true) claim cells allCells = .attained q actual tight ∧
      q = 6 ∧ actual.actual.receipt.quantity = 6 := by
  have full := the_original_six_survive_the_new_production.2
  have funded : Funding payerCut (signed true) claim (liveBalance payerCut claim) := full.symm ▸ fullyFunded
  obtain ⟨actual, tight, selected⟩ := resolve_selects_the_funded_full_balance _ _ _ cells allCells funded
  exact ⟨_, actual, tight, selected, full, actual.actual.amount.trans full⟩

theorem the_cleared_actual_recipe_checks (paid : PaidWrite payerCut (signed true) claim 6) :
    FixedPoint.OpenPeace.Operational.RecipeConditions paid.next.programme (originalRaw loss)
      paid.next.physical.raw (people loss front)
      (codeFor _ (paid.sameProgramme.trans actualTrial.revisedProgramme) _) := by
  have stock := payment_lands_at_the_actual_stock paid
  apply checksFor
  · rw [stock]
    decide +kernel
  · intro person
    rw [stock]
    cases person <;> decide +kernel
  · rw [stock]
    decide +kernel
  · rw [stock]
    decide +kernel

theorem the_revised_original_root_clears_and_runs_cofinally :
    ∃ (paid : PaidWrite payerCut (signed true) claim 6) (opening : ClearedOpening paid.next),
      pay payerCut (signed true) claim 6 cells allCells = .inr paid ∧
      openRenewal paid.next (codeFor _ (paid.sameProgramme.trans actualTrial.revisedProgramme) _) = .inr opening ∧
      paid.next.physical.raw = afterClear ∧
      (∀ n, (renewal opening n).state.ledger.stack.balances.map Prod.fst = [loss] ∧
        ∀ row ∈ (renewal opening n).state.ledger.stack.balances, row.2.remaining = 0) ∧
      ∀ start : Nat, ∀ bound : ℚ, ∃ n ≥ start, bound < (renewal opening n).state.physical.raw.clock := by
  obtain ⟨paid, selected, _, _, addresses, cleared, _, _, _⟩ := the_new_interpreter_clears_the_original_six
  have law := paid.sameProgramme.trans actualTrial.revisedProgramme
  have stock := payment_lands_at_the_actual_stock paid
  have viable := the_cleared_actual_recipe_checks paid
  obtain ⟨opening, entered⟩ := openRenewal_writes_when_the_original_rows_and_recipe_are_paid
    paid.next (codeFor _ law _) cleared viable
  refine ⟨paid, opening, selected, entered, stock, fun n => ⟨?_, every_renewal_keeps_the_original_rows_paid opening n⟩,
    the_paid_original_clock_is_cofinal opening⟩
  rw [(renewal opening n).rows, addresses]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
