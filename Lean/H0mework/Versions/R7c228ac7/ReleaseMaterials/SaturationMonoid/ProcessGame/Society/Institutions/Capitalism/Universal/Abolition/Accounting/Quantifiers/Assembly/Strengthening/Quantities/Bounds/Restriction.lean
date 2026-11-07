import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Resolve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Restriction

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable {Issue : List (Option (Compile.RawInput Party Good Port Technology Instrument)) → Type u}
  {Value : Type v}

/-- The outer top means that the original task check failed. A real
source reading of top in Value is still a distinct, present reading. -/
def restrict (inspect : (script : Script) → Option (Issue script)) (read : Script → Value)
    (script : Script) : WithTop Value :=
  match inspect script with
  | none => read script
  | some _ => ⊤

theorem exact_qualified_image (source : C)
    (inspect : (script : Script) → Option (Issue script)) (read : Script → Value) (value : Value) :
    (value : WithTop Value) ∈ Bounds.values source (restrict inspect read) ↔
      ∃ script, Settled source script ∧ inspect script = none ∧ read script = value := by
  constructor
  · rintro ⟨script, feasible, exactValue⟩
    cases seen : inspect script with
    | none =>
        exact ⟨script, settle source script feasible, seen,
          WithTop.coe_injective (by simpa only [restrict, seen] using exactValue)⟩
    | some issue => simp only [restrict, seen, WithTop.top_ne_coe] at exactValue
  · rintro ⟨script, paid, seen, rfl⟩
    exact ⟨script, paid.toFeasible, by simp only [restrict, seen]⟩

variable [CompleteLinearOrder Value]

abbrev cutoff (source : C) (inspect : (script : Script) → Option (Issue script)) (read : Script → Value) :=
  Bounds.lower source (restrict inspect read)

theorem a_strict_limit_produces_a_paid_qualified_script
    (source : C) (inspect : (script : Script) → Option (Issue script)) (read : Script → Value)
    (limit : WithTop Value) (strict : cutoff source inspect read < limit) :
    ∃ script, Settled source script ∧ inspect script = none ∧ (read script : WithTop Value) < limit := by
  obtain ⟨script, paid, closer⟩ := Bounds.actual_below source (restrict inspect read) limit strict
  cases seen : inspect script with
  | none => exact ⟨script, paid, seen, by simpa only [restrict, seen] using closer⟩
  | some issue => simp only [restrict, seen, not_top_lt] at closer

inductive Minimum (source : C) (inspect : (script : Script) → Option (Issue script)) (read : Script → Value) : Prop
  | attained (script : Script) (paid : Settled source script) (passed : inspect script = none)
      (exactValue : (read script : WithTop Value) = cutoff source inspect read)
  | approached
      (strict : ∀ script, Settled source script → inspect script = none →
        cutoff source inspect read < (read script : WithTop Value))
      (near : ∀ limit, cutoff source inspect read < limit →
        ∃ script, Settled source script ∧ inspect script = none ∧ (read script : WithTop Value) < limit)
      (nonempty : ∃ script, Settled source script ∧ inspect script = none)
  | blocked (issues : ∀ script, Recorded source script ∧
      (Nonempty (Obstruction source script) ∨ ∃ issue, inspect script = some issue))

theorem resolve (source : C) (inspect : (script : Script) → Option (Issue script)) (read : Script → Value) :
    Minimum source inspect read := by
  classical
  by_cases available : ∃ script, Settled source script ∧ inspect script = none
  · have belowTop : cutoff source inspect read < ⊤ := by
      obtain ⟨script, paid, passed⟩ := available
      have bounded := Bounds.lower_le source (restrict inspect read) script paid.toFeasible
      rw [restrict, passed] at bounded
      exact bounded.trans_lt (WithTop.coe_lt_top (read script))
    cases Bounds.resolve_minimum source (restrict inspect read) with
    | attained script paid value =>
        cases seen : inspect script with
        | none => exact .attained script paid seen (by simpa only [restrict, seen] using value)
        | some issue =>
            simp only [restrict, seen] at value
            exact (not_lt_of_ge value.le belowTop).elim
    | approached _ strictly _ =>
        refine .approached ?_ (a_strict_limit_produces_a_paid_qualified_script source inspect read) available
        intro script paid passed
        simpa only [restrict, passed] using strictly script paid
    | obstructed issues =>
        obtain ⟨script, paid, _⟩ := available
        obtain ⟨_, ⟨issue⟩⟩ := issues script
        exact (issue.refutes paid.toFeasible).elim
  · refine .blocked (fun script => ⟨record source script, ?_⟩)
    cases decideAt source script with
    | blocked issue => exact .inl ⟨issue⟩
    | feasible paid =>
        cases seen : inspect script with
        | none => exact (available ⟨script, settle source script paid, seen⟩).elim
        | some issue => exact .inr ⟨issue, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Restriction
