import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme.Folding
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current

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
  (code : Submission (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

theorem run_is_the_original_compiler_fold :
    run input before code = code.foldl (fun current raw => (Physical.Public.compile input current raw).next) before := by
  induction code generalizing before with
  | nil => rfl
  | cons raw tail prior => exact prior _

theorem the_comparison_programme_is_the_literal_original_source_suffix [DecidableEq Port]
    (depth count prefixLimit renewalLimit : Nat)
    (oldPast history : List (Compile.RawInput Party Good Port Technology Instrument)) :
    run input (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast history) code =
      Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast (history ++ code) := by
  rw [run_is_the_original_compiler_fold]
  simp only [Physical.Public.stateAt,List.foldl_append]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
