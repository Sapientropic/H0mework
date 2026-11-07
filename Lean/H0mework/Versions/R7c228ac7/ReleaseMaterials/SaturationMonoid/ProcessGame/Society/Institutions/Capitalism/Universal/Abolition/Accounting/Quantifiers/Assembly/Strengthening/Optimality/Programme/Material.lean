import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Folding
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

variable (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (code : Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem result_material_balance (raw : Compile.RawInput Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before raw) (party : Party) (good : Good) :
    result.next.raw.stock party good + (Physical.Public.interpreter input).totalDebit result.execution.items party good =
      before.raw.stock party good + (Physical.Public.interpreter input).totalCredit result.execution.items party good := by
  cases result with
  | accepted word selected checked =>
      cases raw <;> exact (Physical.Public.interpreter input).execute_material_balance before.raw 0 word party good
  | refused word selected item listed failed =>
      simp [Physical.Public.ResultAt.next,Physical.Public.ResultAt.execution,RawLaw.totalDebit,RawLaw.totalCredit]
  | metadata selected =>
      simp [Physical.Public.ResultAt.next,Physical.Public.ResultAt.execution,RawLaw.totalDebit,RawLaw.totalCredit]

theorem result_clock_nondecreasing (raw : Compile.RawInput Party Good Port Technology Instrument)
    (result : Physical.Public.ResultAt input before raw) : before.raw.clock ≤ result.next.raw.clock := by
  cases result with
  | accepted word selected checked =>
      cases raw <;> first
      | exact (Physical.Public.interpreter input).next_clock_nondecreasing before.raw word
      | exact le_of_eq (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
          (Physical.Public.interpreter input) before.raw 0 word).1.symm
  | refused => exact le_refl _
  | metadata => exact le_refl _

theorem the_entire_programme_has_its_original_material_balance (party : Party) (good : Good) :
    (run input before code).raw.stock party good +
      (Physical.Public.interpreter input).totalDebit (items input before code) party good =
      before.raw.stock party good + (Physical.Public.interpreter input).totalCredit (items input before code) party good := by
  induction code generalizing before with
  | nil => simp [run,items,RawLaw.totalDebit,RawLaw.totalCredit]
  | cons raw tail prior =>
      have first := result_material_balance input before raw (Physical.Public.compile input before raw) party good
      have rest := prior (Physical.Public.compile input before raw).next
      simp only [run,items,RawLaw.totalDebit,RawLaw.totalCredit,List.map_append,List.sum_append] at *
      linarith

theorem programme_clock_never_runs_backwards : before.raw.clock ≤ (run input before code).raw.clock := by
  induction code generalizing before with
  | nil => exact le_refl _
  | cons raw tail prior =>
      exact (result_clock_nondecreasing input before raw (Physical.Public.compile input before raw)).trans (prior _)

theorem clockCost_nonnegative : 0 ≤ clockCost input before code :=
  sub_nonneg.mpr (programme_clock_never_runs_backwards input before code)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
