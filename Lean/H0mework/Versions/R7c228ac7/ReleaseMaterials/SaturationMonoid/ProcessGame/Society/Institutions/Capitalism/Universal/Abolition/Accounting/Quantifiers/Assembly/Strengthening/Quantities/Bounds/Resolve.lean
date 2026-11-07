import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Scalar

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Value : Type u} [CompleteLinearOrder Value]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- A refusal keeps its exact source obstruction and the same recorded
ledger. Limits supply real finite completions at every strict tolerance. -/
inductive Minimum (source : C) (read : Script → Value) : Prop
  | attained (script : Script) (paid : Settled source script)
      (exactValue : read script = lower source read)
  | approached (existsPaid : ∃ script, Settled source script)
      (strict : ∀ script, Settled source script → lower source read < read script)
      (near : ∀ limit, lower source read < limit →
        ∃ script, Settled source script ∧ read script < limit)
  | obstructed (issues : ∀ script, Recorded source script ∧ Nonempty (Obstruction source script))

theorem resolve_minimum (source : C) (read : Script → Value) : Minimum source read := by
  classical
  by_cases reached : lower source read ∈ values source read
  · obtain ⟨script, paid, value⟩ := (observed_iff_settled source read _).mp reached
    exact .attained script paid value
  by_cases empty : values source read = ∅
  · have blocked := (empty_iff_original_obstructions source read).mp empty
    exact .obstructed (fun script => ⟨record source script, blocked script⟩)
  obtain ⟨value, present⟩ := Set.nonempty_iff_ne_empty.mpr empty
  obtain ⟨script, paid, _⟩ := (observed_iff_settled source read _).mp present
  refine .approached ⟨script, paid⟩ ?_ (actual_below source read)
  intro candidate settled
  apply lt_of_le_of_ne (lower_le source read candidate settled.toFeasible)
  intro eq
  exact reached ⟨candidate, settled.toFeasible, eq.symm⟩

abbrev Maximum (source : C) (read : Script → Value) : Prop :=
  Minimum (Value := Valueᵒᵈ) source read

theorem resolve_maximum (source : C) (read : Script → Value) : Maximum source read :=
  resolve_minimum (Value := Valueᵒᵈ) source read

theorem attaining_the_cut_iff_no_paid_alternative_is_lower
    (source : C) (read : Script → Value) (script : Script) (paid : Settled source script) :
    read script = lower source read ↔ ∀ alternative, Settled source alternative →
      read script ≤ read alternative := by
  constructor
  · intro exactValue alternative settled
    rw [exactValue]
    exact lower_le source read alternative settled.toFeasible
  · intro least
    apply le_antisymm _ (lower_le source read script paid.toFeasible)
    apply (lower_is_tight source read).2
    rintro value ⟨alternative, feasible, rfl⟩
    exact least alternative (settle source alternative feasible)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds
