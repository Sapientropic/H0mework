import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Trace.Fees

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

theorem an_actual_primitive_does_not_create_an_extra_period
    (request : Request Party Good Port Technology Instrument) :
    (compile input before (.primitive request)).next.raw.clock = before.raw.clock ∧
      (compile input before (.primitive request)).next.raw.round = before.raw.round := by
  cases generated : compile input before (.primitive request) with
  | accepted word selected checked =>
      exact Review.execution_preserves_period (interpreter input) before.raw word 0
  | refused => exact ⟨rfl, rfl⟩
  | metadata _ => exact ⟨rfl, rfl⟩

theorem every_actual_input_keeps_its_inherited_programme
    (raw : Compile.RawInput Party Good Port Technology Instrument) :
    (compile input before raw).next.phase = before.phase ∧
      (compile input before raw).next.remaining = before.remaining := by
  cases compile input before raw <;> exact ⟨rfl, rfl⟩

private def ExactPeriodTime
    {raw : Compile.RawInput Party Good Port Technology Instrument} (result : ResultAt input before raw) : Prop :=
  if result.isAccepted then
    result.next.raw.clock = before.raw.clock + max 0 (input.law.duration before.raw) ∧
      result.next.raw.round = before.raw.round + 1
  else result.next = before

theorem the_actual_advance_is_one_real_period_or_the_original_state :
    ExactPeriodTime input before (compile input before .advance) := by
  cases compile input before .advance <;> first | exact ⟨rfl, rfl⟩ | rfl

theorem an_actual_complete_word_is_one_real_period_or_the_original_state
    (word : RawEvent Party Good Port Technology Instrument) :
    ExactPeriodTime input before (compile input before (.execute word)) := by
  cases compile input before (.execute word) <;> first | exact ⟨rfl, rfl⟩ | rfl

#print axioms an_actual_primitive_does_not_create_an_extra_period
#print axioms every_actual_input_keeps_its_inherited_programme
#print axioms the_actual_advance_is_one_real_period_or_the_original_state
#print axioms an_actual_complete_word_is_one_real_period_or_the_original_state

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public
