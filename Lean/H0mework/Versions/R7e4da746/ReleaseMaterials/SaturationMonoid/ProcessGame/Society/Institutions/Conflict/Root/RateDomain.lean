import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Attached
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice.Rates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root

open Capitalism.Universal.Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument

/-- Keep the exact original row when evaluating a common rate on several
conflict branches from one cut. The words are generated from these rows. -/
structure ShiftCase (source : C) where
  front : Word
  levy : Req
  settlement : Req
  index : Nat
  shift : Shift source front levy settlement index

variable (source : Cut Party Good Port Technology Instrument)
  (read : Cut Party Good Port Technology Instrument → ℚ)
  (first : ShiftCase source) (others : List (ShiftCase source))
  (war peace : ℚ → List (RawEvent Party Good Port Technology Instrument))

def chargeWords (rate : ℚ) : List Word :=
  (first :: others).map (fun entry => entry.shift.returnedWord rate)

private def comparedAt (rate : ℚ) : Option ℚ :=
  pressure source read (chargeWords source first others rate ++ war rate) (peace rate)

inductive RateDecision (rate : ℚ)
  | refused (word : Word) (original : word ∈ chargeWords source first others rate)
      (issue : Failure source word)
  | noComparison (paid : ∀ word ∈ chargeWords source first others rate, Paid source word)
      (missing : comparedAt source read first others war peace rate = none)
  | compared (paid : ∀ word ∈ chargeWords source first others rate, Paid source word)
      (gap : ℚ) (exactGap : comparedAt source read first others war peace rate = some gap)

def inspectRate (rate : ℚ) : RateDecision source read first others war peace rate :=
  match Capitalism.Universal.Abolition.Material.inspectList
      (fun word => (inspect source word).accepted = true) (chargeWords source first others rate) with
  | .failure word original declined =>
      match found : inspect source word with
      | .rejected issue => .refused word original issue
      | .paid _ => False.elim (declined (by rw [found]; rfl))
  | .clear accepted =>
      have paid := fun word original => (inspect_accepts_iff source word).mp (accepted word original)
      match gap : comparedAt source read first others war peace rate with
      | none => .noComparison paid gap
      | some value => .compared paid value gap

/-- All required charge words must clear. War and peace each read their own
accepted menu at the rate, including any change of available candidates. -/
def admittedRates : Set ℝ :=
  { rate | ∃ quantity : ℚ, (quantity : ℝ) = rate ∧
      (∀ word ∈ chargeWords source first others quantity, Paid source word) ∧
      (comparedAt source read first others war peace quantity).isSome }

def rateGap (rate : ℝ) : ℝ := by
  classical
  exact if found : ∃ quantity : ℚ, (quantity : ℝ) = rate then
    ((comparedAt source read first others war peace (Classical.choose found)).getD 0 : ℝ)
  else 0

private theorem rateGap_cast (quantity : ℚ) :
    rateGap source read first others war peace (quantity : ℝ) =
      ((comparedAt source read first others war peace quantity).getD 0 : ℝ) := by
  unfold rateGap
  split
  · rename_i found
    have same : Classical.choose found = quantity := Rat.cast_injective (Classical.choose_spec found)
    rw [same]
  · rename_i missing
    exact (missing ⟨quantity, rfl⟩).elim

theorem safe_rates_are_exactly_paid_comparable_rates (rate : ℝ) :
    rate ∈ Choice.safeRates (admittedRates source read first others war peace)
      (rateGap source read first others war peace) ↔
      0 ≤ rate ∧ rate ≤ 1 ∧ ∃ quantity : ℚ, (quantity : ℝ) = rate ∧
        (∀ word ∈ chargeWords source first others quantity, Paid source word) ∧
        ∃ margin : ℚ, pressure source read
          (chargeWords source first others quantity ++ war quantity) (peace quantity) = some margin ∧
          margin ≤ 0 := by
  constructor
  · rintro ⟨nonnegative, within, ⟨quantity, rfl, paid, comparable⟩, deterrent⟩
    obtain ⟨margin, observed⟩ := Option.isSome_iff_exists.mp comparable
    rw [rateGap_cast, observed] at deterrent
    exact ⟨nonnegative, within, quantity, rfl, paid, margin, observed, by exact_mod_cast deterrent⟩
  · rintro ⟨nonnegative, within, quantity, rfl, paid, margin, observed, deterrent⟩
    change comparedAt source read first others war peace quantity = some margin at observed
    refine ⟨nonnegative, within, ⟨quantity, rfl, paid, by simp [observed]⟩, ?_⟩
    rw [rateGap_cast, observed]
    exact_mod_cast deterrent

theorem least_paid_rate_is_attained_approached_or_blocked :
    Choice.LeastRate (admittedRates source read first others war peace)
      (rateGap source read first others war peace) :=
  Choice.resolve_least_safe_rate _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root
