import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Inspection
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Restriction
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Root.Profile

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery

open Source.Program Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem elapsed_nonnegative (source : C) (script : Script) : 0 ≤ elapsed source script := by
  rw [← elapsed_is_original_clock_cost]
  exact Optimality.Programme.clockCost_nonnegative source.native.input
    (Evolving.Epoch.Source.originalState source.native) (Execution.programme source script)

theorem exact_elapsed_sum (origin : C) (exposure repair : Script) :
    elapsed origin (exposure ++ repair) =
      elapsed origin exposure + elapsed (Execution.endAt origin exposure) repair := by
  unfold elapsed
  rw [Execution.endAt_append]
  ring

def hourRatio (origin : C) (exposure repair : Script) : EReal :=
  (((elapsed origin (exposure ++ repair) / elapsed origin exposure : ℚ) : ℝ) : EReal)

theorem the_ratio_strictly_increases_exactly_with_real_repair_time
    (origin : C) (exposure repair : Script) (duration : 0 < elapsed origin exposure) :
    1 < hourRatio origin exposure repair ↔ 0 < elapsed (Execution.endAt origin exposure) repair := by
  unfold hourRatio
  change ((1 : ℝ) : EReal) < _ ↔ _
  rw [EReal.coe_lt_coe_iff, ← Rat.cast_one, Rat.cast_lt, lt_div_iff₀ duration, exact_elapsed_sum, one_mul]
  constructor <;> intro bound <;> linarith only [bound]

theorem exact_admitted_work_ratios (origin : C) (exposure : Script) (value : EReal) :
    (value : WithTop EReal) ∈ Bounds.values (Execution.endAt origin exposure)
      (Bounds.Restriction.restrict (inspect origin exposure) (hourRatio origin exposure)) ↔
    ∃ repair, Settled (Execution.endAt origin exposure) repair ∧
      Restored origin exposure repair ∧ hourRatio origin exposure repair = value := by
  rw [Bounds.Restriction.exact_qualified_image]
  simp only [cleared_exactly_when_no_original_actor_loses_stock]

theorem every_actual_recovery_preserves_the_exposure_and_its_whole_account
    (origin : C) (exposure repair : Script) (clear : inspect origin exposure repair = none) :
    Restored origin exposure repair ∧ Recorded origin (exposure ++ repair) :=
  ⟨(cleared_exactly_when_no_original_actor_loses_stock origin exposure repair).mp clear, record origin _⟩

/-- Hours for a work occurrence include the original exposure and the
actual time required to recover without moving a loss to a third party. -/
theorem the_original_work_cut_resolves_its_full_recovery_hour_conversion
    (origin : C) (exposure : Script) :
    (elapsed origin exposure = 0 ∧ Recorded origin exposure) ∨
    (0 < elapsed origin exposure ∧ Bounds.Restriction.Minimum (Execution.endAt origin exposure)
      (inspect origin exposure) (hourRatio origin exposure)) := by
  rcases eq_or_lt_of_le (elapsed_nonnegative origin exposure) with zero | positive
  · exact .inl ⟨zero.symm, record origin exposure⟩
  · exact .inr ⟨positive, Bounds.Restriction.resolve _ _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery
