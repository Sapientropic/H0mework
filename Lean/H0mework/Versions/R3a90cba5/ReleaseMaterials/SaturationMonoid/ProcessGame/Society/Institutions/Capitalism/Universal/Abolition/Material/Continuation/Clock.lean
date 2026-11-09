import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace
import Mathlib.Algebra.Order.Archimedean.Basic

/-! A local source duration bound generates real-clock cofinality. A growing
instruction ordinal alone supplies no such bound. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (program : RawProgram Party Good Port Technology Instrument)
  (quantum : ℚ)
  (sourceDuration : ∀ current, quantum ≤ max 0 (program.law.duration current))

include sourceDuration in
theorem real_clock_grows_by_source_periods (n : Nat) :
    program.initial.clock + (n : ℚ) * quantum ≤ (program.currentAt n).clock := by
  induction n with
  | zero => simp only [RawProgram.currentAt, Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n prior =>
      have actual := sourceDuration (program.currentAt n)
      change program.initial.clock + ((n + 1 : Nat) : ℚ) * quantum ≤
        (program.currentAt n).clock + max 0 (program.law.duration (program.currentAt n))
      push_cast
      nlinarith

include sourceDuration in
theorem generated_clock_exceeds_every_real_horizon (positive : 0 < quantum) (horizon : ℚ) :
    ∃ n : Nat, horizon < (program.currentAt n).clock := by
  obtain ⟨n, reaches⟩ := exists_nat_gt ((horizon - program.initial.clock) / quantum)
  have grows := real_clock_grows_by_source_periods program quantum sourceDuration n
  have enough : horizon - program.initial.clock < (n : ℚ) * quantum :=
    (div_lt_iff₀ positive).mp reaches
  exact ⟨n, by linarith⟩

#print axioms real_clock_grows_by_source_periods
#print axioms generated_clock_exceeds_every_real_horizon

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation
