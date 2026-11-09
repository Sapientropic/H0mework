import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Quote
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Admission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Abolition.Material (inspectList)
open Prepayment
open private budgetCells outside_budgetCells from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Finitary

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "Law" => RawLaw Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Bill" => ReviewBid Party Good Port Technology Instrument

variable (law : RawLaw Party Good Port Technology Instrument)
  (base : RawCurrent Party Good Technology Instrument)
  (production : RawEvent Party Good Port Technology Instrument)
  (bid : ReviewBid Party Good Port Technology Instrument)

local notation "Gain" => Balance.gain law base production
local notation "Legal" => RawLaw.Valid law (ExecutionResult.final (RawLaw.execute law base 0 production))
  (reviewRequest bid.payer bid.port bid.expenses)
local notation "Cells" => budgetCells law base production bid

inductive BudgetIssue where
  | rejected (original : ¬ Legal)
  | excess (person : Party) (good : Good) (short : Gain person good < bid.fee person good)
  | noProgress (all : ∀ person good, Gain person good ≤ bid.fee person good)

omit [DecidableEq Port] in
theorem BudgetIssue.refutes (issue : BudgetIssue law base production bid) :
    ¬ BaseBudget law base production bid := by
  intro paid
  cases issue with
  | rejected forbidden => exact forbidden paid.legal
  | excess person good short => exact (not_le_of_gt short) (paid.fits person good)
  | noProgress all =>
    obtain ⟨person, good, strict⟩ := paid.surplus
    exact (not_lt_of_ge (all person good)) strict

private def compareSupport {Address : Type} [DecidableEq Address]
    (support : List Address) (first second : Address → ℚ)
    (absent : ∀ address, address ∉ support → first address = 0 ∧ second address = 0) :
    { address : Address // second address < first address } ⊕ PLift (∀ address, first address ≤ second address) :=
  match inspectList (fun address => first address ≤ second address) support with
  | .failure address _ bad => .inl ⟨address, lt_of_not_ge bad⟩
  | .clear safe => .inr ⟨fun address => by
      if listed : address ∈ support then
        exact safe _ listed
      else
        obtain ⟨left, right⟩ := absent address listed
        rw [left, right]⟩

/-- The original gain support and charged cells suffice to find a
physical shortfall or prove that a full debit would stop net production. -/
def inspectBudget (nonnegative : ∀ person good, 0 ≤ bid.fee person good) :
    BudgetIssue law base production bid ⊕ PLift (BaseBudget law base production bid) :=
  if legal : Legal then
    let fee := fun cell : Party × Good => bid.fee cell.1 cell.2
    let produced := fun cell : Party × Good => Gain cell.1 cell.2
    let absent := fun (cell : Party × Good) outside =>
      outside_budgetCells law base production bid cell.1 cell.2 outside
    match compareSupport Cells fee produced absent with
    | .inl short => .inl (.excess short.val.1 short.val.2 short.property)
    | .inr within =>
      match compareSupport Cells produced fee (fun cell outside => ⟨(absent cell outside).2, (absent cell outside).1⟩) with
      | .inl extra => .inr ⟨⟨legal, nonnegative, fun person good => within.down (person, good),
          extra.val.1, extra.val.2, extra.property⟩⟩
      | .inr stalled => .inl (.noProgress (fun person good => stalled.down (person, good)))
  else .inl (.rejected legal)

omit [DecidableEq Port] in
theorem inspection_finds_the_exact_original_budget (nonnegative : ∀ person good, 0 ≤ bid.fee person good) :
    (∃ ready, inspectBudget law base production bid nonnegative = .inr ready) ↔
      BaseBudget law base production bid := by
  constructor
  · rintro ⟨ready, _⟩
    exact ready.down
  · intro safe
    cases result : inspectBudget law base production bid nonnegative with
    | inl rejected => exact (rejected.refutes law base production bid safe).elim
    | inr ready => exact ⟨ready, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing
