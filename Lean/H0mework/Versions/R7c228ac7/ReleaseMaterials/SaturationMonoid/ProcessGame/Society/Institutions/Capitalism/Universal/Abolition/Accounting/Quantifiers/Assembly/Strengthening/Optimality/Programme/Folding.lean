import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (first second : Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem run_append : run input before (first ++ second) = run input (run input before first) second := by
  induction first generalizing before with
  | nil => rfl
  | cons raw tail ih => exact ih _

theorem items_append : items input before (first ++ second) =
    items input before first ++ items input (run input before first) second := by
  induction first generalizing before with
  | nil => rfl
  | cons raw tail ih => simp only [List.cons_append,items,run,ih,List.append_assoc]

theorem elapsed_append : clockCost input before (first ++ second) =
    clockCost input before first + clockCost input (run input before first) second := by
  simp only [clockCost,run_append]
  ring

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
