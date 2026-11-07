import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.NativeRuntime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate

open Source.Program PublicFunction
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

def clockAt (bound : BoundSource base scope) (inputs : Inputs) (ordinal : Nat) : ℚ :=
  (OutstandingSource.History.currentAt bound.source inputs ordinal).clock

theorem clock_succ_is_its_original_paid_period_duration (bound : BoundSource base scope)
    (inputs : Inputs) (ordinal : Nat) :
    clockAt bound inputs (ordinal + 1) = clockAt bound inputs ordinal +
      max 0 ((law base scope).duration (OutstandingSource.History.currentAt bound.source inputs ordinal)) := by
  unfold clockAt
  rw [(OutstandingSource.History.actual_frame bound.source inputs (ordinal + 1)).1,
    (OutstandingSource.History.actual_frame bound.source inputs ordinal).1]
  change (OutstandingSource.History.trailAt bound.source inputs ordinal).frame.raw.clock +
      max 0 (bound.source.seed.law.duration (OutstandingSource.History.trailAt bound.source inputs ordinal).frame.raw) = _
  rw [bound.law_exact]

theorem real_clock_is_monotone (bound : BoundSource base scope) (inputs : Inputs) :
    Monotone (clockAt bound inputs) := by
  apply monotone_nat_of_le_succ
  intro ordinal
  rw [clock_succ_is_its_original_paid_period_duration]
  exact le_add_of_nonneg_right (le_max_left _ _)

theorem constant_source_duration_gives_the_literal_clock (bound : BoundSource base scope)
    (inputs : Inputs) (duration : ℚ) (positive : 0 < duration)
    (owned : ∀ current, (law base scope).duration current = duration) (ordinal : Nat) :
    clockAt bound inputs ordinal = bound.source.seed.initial.clock + (ordinal : ℚ) * duration := by
  induction ordinal with
  | zero =>
      change bound.source.seed.initial.clock = bound.source.seed.initial.clock + (0 : ℚ) * duration
      simp
  | succ ordinal ih =>
      rw [clock_succ_is_its_original_paid_period_duration, owned, max_eq_right positive.le, ih]
      push_cast
      ring

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate
