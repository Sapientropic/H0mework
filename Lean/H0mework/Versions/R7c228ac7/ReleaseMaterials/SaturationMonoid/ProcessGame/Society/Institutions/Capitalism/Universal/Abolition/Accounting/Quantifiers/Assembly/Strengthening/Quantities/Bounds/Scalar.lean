import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Settlement
import Mathlib.Data.EReal.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds

open Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

universe u

variable {Value : Type u}

/-- Exact image of all finite completions through this source dispatcher. -/
def values (source : C) (read : Script → Value) : Set Value :=
  fun value => ∃ script : Script, Feasible source script ∧ read script = value

variable (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (read : List (Option (Compile.RawInput Party Good Port Technology Instrument)) → Value)

theorem observed_iff_settled (value : Value) :
    value ∈ values source read ↔ ∃ script, Settled source script ∧ read script = value := by
  constructor
  · rintro ⟨script, paid, exactValue⟩
    exact ⟨script, settle source script paid, exactValue⟩
  · rintro ⟨script, paid, exactValue⟩
    exact ⟨script, paid.toFeasible, exactValue⟩

variable [CompleteLinearOrder Value]

def lower : Value := sInf (values source read)
def upper : Value := sSup (values source read)

theorem lower_is_tight : IsGLB (values source read) (lower source read) :=
  isGLB_sInf _

theorem upper_is_tight : IsLUB (values source read) (upper source read) :=
  isLUB_sSup _

theorem lower_le (script : Script) (paid : Feasible source script) :
    lower source read ≤ read script :=
  sInf_le ⟨script, paid, rfl⟩

theorem le_upper (script : Script) (paid : Feasible source script) :
    read script ≤ upper source read :=
  le_sSup ⟨script, paid, rfl⟩

theorem actual_below (limit : Value) (strict : lower source read < limit) :
    ∃ script, Settled source script ∧ read script < limit := by
  obtain ⟨value, present, cheaper⟩ := sInf_lt_iff.mp strict
  obtain ⟨script, paid, rfl⟩ := (observed_iff_settled source read value).mp present
  exact ⟨script, paid, cheaper⟩

theorem actual_above (limit : Value) (strict : limit < upper source read) :
    ∃ script, Settled source script ∧ limit < read script := by
  obtain ⟨value, present, greater⟩ := lt_sSup_iff.mp strict
  obtain ⟨script, paid, rfl⟩ := (observed_iff_settled source read value).mp present
  exact ⟨script, paid, greater⟩

omit [CompleteLinearOrder Value] in
theorem empty_iff_original_obstructions :
    values source read = ∅ ↔ ∀ script : Script, Nonempty (Obstruction source script) := by
  constructor
  · intro empty script
    apply (infeasible_iff_original_obstruction source script).mp
    intro paid
    have present : read script ∈ values source read := ⟨script, paid, rfl⟩
    rw [empty] at present
    exact present
  · intro blocked
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro value ⟨script, paid, _⟩
    exact (infeasible_iff_original_obstruction source script).mpr (blocked script) paid

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds
