import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Work
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Tariff

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- Work at the original public cut fixes the tariff. Each request
elaborates to a native work word, whose quantities come from its ledger
effect. The productive slot is retained by the protected dispatcher. -/
structure Desk (law : RawLaw Party Good Port Technology Instrument)
    (before : RawCurrent Party Good Technology Instrument) (worker : Party) where
  port : Port
  filing : MeteredWork law before worker
  review : Request Party Good Port Technology Instrument → MeteredWork law before worker

namespace Desk

variable {law : RawLaw Party Good Port Technology Instrument}
  {before : RawCurrent Party Good Technology Instrument} {worker : Party}
  (desk : Desk law before worker)

def filingCheck : Bool :=
  desk.filing.bundle.any fun lot => decide (0 < amount Good desk.filing.bundle lot.1)

omit [DecidableEq Port] in
theorem filingCheck_iff :
    desk.filingCheck = true ↔ ∃ good, 0 < amount Good desk.filing.bundle good := by
  rw [filingCheck, List.any_eq_true]
  constructor
  · rintro ⟨lot, _, positive⟩
    exact ⟨lot.1, of_decide_eq_true positive⟩
  · rintro ⟨good, positive⟩
    have present : good ∈ desk.filing.bundle.map Prod.fst := by
      by_contra absent
      have zero := amount_zero_of_absent desk.filing.bundle good (fun lot listed equal =>
        absent (equal ▸ List.mem_map.mpr ⟨lot, listed, rfl⟩))
      exact (lt_irrefl 0) (zero ▸ positive)
    obtain ⟨lot, listed, equal⟩ := List.mem_map.mp present
    exact ⟨lot, listed, decide_eq_true (equal.symm ▸ positive)⟩

def tariff (ready : desk.filingCheck = true) : Tariff Party Good Port Technology Instrument where
  port := desk.port
  filing := desk.filing.bundle
  review := fun request => (desk.review request).bundle
  opportunity := fun _ => []
  filingNonnegative := desk.filing.nonnegative
  reviewNonnegative := fun request => (desk.review request).nonnegative
  opportunityNonnegative := fun _ _ listed => (List.not_mem_nil listed).elim
  filingPositive := desk.filingCheck_iff.mp ready

def quote? : Option (Tariff Party Good Port Technology Instrument) :=
  if ready : desk.filingCheck = true then some (desk.tariff ready) else none

omit [DecidableEq Port] in
theorem no_filing_cost_iff :
    desk.quote? = none ↔ ∀ good, amount Good desk.filing.bundle good = 0 := by
  unfold quote?
  by_cases ready : desk.filingCheck = true
  · rw [dif_pos ready]
    constructor
    · intro impossible; cases impossible
    · intro zero
      obtain ⟨good, positive⟩ := desk.filingCheck_iff.mp ready
      exact (lt_irrefl 0 (zero good ▸ positive)).elim
  · rw [dif_neg ready]
    refine ⟨fun _ good => ?_, fun _ => rfl⟩
    exact le_antisymm (le_of_not_gt fun positive => ready (desk.filingCheck_iff.mpr ⟨good, positive⟩))
      (amount_nonnegative _ desk.filing.nonnegative _)

def actualCost (word : RawEvent Party Good Port Technology Instrument) (good : Good) : ℚ :=
  law.totalDebit (law.rawItems before desk.filing.word) worker good +
    (word.map fun request => law.totalDebit (law.rawItems before (desk.review request).word) worker good).sum

omit [DecidableEq Port] in
theorem exact_quote (ready : desk.filingCheck = true)
    (word : RawEvent Party Good Port Technology Instrument) (good : Good) :
    amount Good ((desk.tariff ready).parts word).bundle good = desk.actualCost word good := by
  rw [ChargeParts.amount_bundle]
  have noOpportunity : word.flatMap (fun (_ : Request Party Good Port Technology Instrument) => ([] : Bundle Good)) = [] := by
    induction word with
    | nil => rfl
    | cons head tail previous => simp [previous]
  have audit (actions : RawEvent Party Good Port Technology Instrument) :
      amount Good (actions.flatMap fun request => (desk.review request).bundle) good =
        (actions.map fun request => law.totalDebit (law.rawItems before (desk.review request).word) worker good).sum := by
    induction actions with
    | nil => rfl
    | cons request rest previous =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [← previous, ← (desk.review request).actual_address good]
      simp [amount, List.map_append, List.sum_append]
  simp only [Tariff.parts, tariff, actualCost]
  rw [noOpportunity, audit, desk.filing.actual_address]
  exact add_zero _

omit [DecidableEq Port] in
theorem the_generated_fee_is_the_least_full_charge (ready : desk.filingCheck = true)
    (word : RawEvent Party Good Port Technology Instrument) :
    let posted := ((desk.tariff ready).parts word).bundle
    (∀ good, desk.actualCost word good ≤ amount Good posted good) ∧
    ∀ (other : Bundle Good), (∀ good, desk.actualCost word good ≤ amount Good other good) →
      ∀ good, amount Good posted good ≤ amount Good other good := by
  dsimp only
  exact ⟨fun good => (desk.exact_quote ready word good).ge,
    fun _ covers good => (desk.exact_quote ready word good).le.trans (covers good)⟩

end Desk

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing
