import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Native
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear.Solve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (word : List (Option (Compile.RawInput Party Good Port Technology Instrument)))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)

local notation "Assignment" => Due.Service.Need ordered.toFinset task →
  Due.Service.Supply source word ordered.toFinset task → ℚ

inductive Decision where
  | paid (allocation : Assignment) (fits : Fits source word ordered task reserved held budget allocation)
  | blocked (impossible : ¬ ∃ allocation, Fits source word ordered task reserved held budget allocation)

def decideAllocation : Decision source word ordered task reserved held budget :=
  match solve (constraints source word ordered task reserved held budget) with
  | .feasible values checked =>
    .paid (decode (index source word ordered task) values)
      ((constraints_exact source word ordered task reserved held budget values).mp checked)
  | .infeasible impossible =>
    .blocked (by
      rintro ⟨allocation, fits⟩
      let values := encode (index source word ordered task) allocation
      exact impossible ⟨values, (constraints_exact source word ordered task reserved held budget values).mpr
        (by simpa only [values, decode_encode] using fits)⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation
