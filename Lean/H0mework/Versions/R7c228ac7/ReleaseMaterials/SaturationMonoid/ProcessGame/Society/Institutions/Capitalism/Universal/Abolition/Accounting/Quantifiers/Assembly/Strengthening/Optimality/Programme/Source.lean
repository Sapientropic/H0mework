import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Result

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Abolition.Root Abolition.Root.Registered
noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- Unbounded finite source syntax. No menu, permutation, horizon or action
alphabet is a parameter. Source refusal is interpreted by the original compiler. -/
abbrev Submission := List (Compile.RawInput Party Good Port Technology Instrument)

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
local notation "Code" => Submission (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)

def run (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Code →
    Actual.Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  | [] => before
  | raw :: tail => run (Physical.Public.compile input before raw).next tail

def items (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) : Code →
    List (ExecutionItem Party Good Port Technology Instrument)
  | [] => []
  | raw :: tail => (Physical.Public.compile input before raw).execution.items ++
      items (Physical.Public.compile input before raw).next tail

/-- This observation does not flatten a primitive into a period: original
microsteps, period time, metadata and atomic refusal keep their exact effects. -/
def clockCost (before : Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (code : Code) : ℚ :=
  (run input before code).raw.clock - before.raw.clock

attribute [local simp] run items
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Programme
