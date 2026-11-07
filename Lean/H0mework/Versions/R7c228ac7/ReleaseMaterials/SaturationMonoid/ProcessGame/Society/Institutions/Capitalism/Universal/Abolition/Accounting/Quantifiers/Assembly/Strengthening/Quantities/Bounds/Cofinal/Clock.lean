import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Domain
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

theorem a_positive_paid_clock_quantum_crosses_every_physical_horizon
    (source : C) (policy : Nat → C → Script) (quantum : ℚ) (positive : 0 < quantum)
    (each : ∀ stage, quantum ≤ elapsed (stageAt source policy stage) (stageBody source policy stage)) :
    ClockCofinal source policy := by
  have clock (stage : Nat) :
      source.raw.clock + (stage : ℚ) * quantum ≤ (stageAt source policy stage).raw.clock := by
    induction stage with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; exact le_rfl
    | succ n previous =>
      have advanced := each n
      rw [next_stage_is_the_literal_original_next, Nat.cast_succ]
      unfold elapsed at advanced
      linarith
  intro horizon
  obtain ⟨stage, crosses⟩ := exists_nat_gt ((horizon - source.raw.clock) / quantum)
  have enough := (div_lt_iff₀ positive).mp crosses
  exact ⟨stage, le_of_lt (by linarith [clock stage])⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal
