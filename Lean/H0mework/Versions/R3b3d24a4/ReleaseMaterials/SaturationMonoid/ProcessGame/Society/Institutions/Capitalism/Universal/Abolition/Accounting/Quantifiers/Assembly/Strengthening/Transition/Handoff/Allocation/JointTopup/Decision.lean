import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Native

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Allocation.Linear
open Diagnostics

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
  (limits : Limits Party Good)

local notation "Allocation" => Due.Service.Need ordered.toFinset task →
  Due.Service.Supply source word ordered.toFinset task → ℚ
local notation "Original" => system source word ordered task reserved held budget limits

inductive Decision where
  | feasible (extra : Party × Good → ℚ) (allocation : Allocation)
      (admitted : FitsJoint source word ordered task reserved held budget limits extra allocation)
  | blocked (conflict : Conflict Original)

def decideJoint : Decision source word ordered task reserved held budget limits :=
  match diagnose Original with
  | .feasible values checked =>
      .feasible (readExtra source word ordered task values) (readAllocation source word ordered task values)
        ((system_exact source word ordered task reserved held budget limits values).mp checked)
  | .blocked conflict => .blocked conflict

theorem jointConflict_refutes (conflict : Conflict Original) :
    ¬ ∃ extra allocation, FitsJoint source word ordered task reserved held budget limits extra allocation := by
  rintro ⟨extra, allocation, admitted⟩
  exact conflict.refutes ⟨_, original_candidate_enters_system
    source word ordered task reserved held budget limits extra allocation admitted⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
