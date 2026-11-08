import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Decision
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup.Optimize

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

local notation "Assignment" => Due.Service.Need ordered.toFinset task →
  Due.Service.Supply source word ordered.toFinset task → ℚ
local notation "Keys" => watched source word ordered task
local notation "Width" => List.length (edgeList source word ordered task)
local notation "Original" => system source word ordered task reserved held budget limits

variable (weights : Party × Good → ℚ)

inductive WeightedDecision where
  | attained (extra : Party × Good → ℚ) (allocation : Assignment)
      (admitted : FitsJoint source word ordered task reserved held budget limits extra allocation)
      (least : ∀ other otherAllocation,
        FitsJoint source word ordered task reserved held budget limits other otherAllocation →
        weightedTotal Keys weights extra ≤ weightedTotal Keys weights other)
  | blocked (conflict : Conflict Original)

/-- The hard joint domain uses only physical capacities. Chosen weights
compare its members and leave the entire original assignment attached. -/
def leastWeighted (weightsNonnegative : ∀ key ∈ Keys, 0 ≤ weights key) :
    WeightedDecision source word ordered task reserved held budget limits weights :=
  let score := weightedForm Keys (watched_distinct source word ordered task) Width weights
  match minimize Original score (fun values checked => by
    rw [weightedForm_exact]
    have fit := (system_exact source word ordered task reserved held budget limits values).mp checked
    exact weightedTotal_nonnegative _ _ _ weightsNonnegative (fun key listed => (fit.2.1.1 key listed).1)) with
  | .blocked conflict => .blocked conflict
  | .attained values checked least =>
    let admitted := (system_exact source word ordered task reserved held budget limits values).mp checked
    .attained (readExtra source word ordered task values) (readAllocation source word ordered task values) admitted
      (fun other otherAllocation fit => by
        let candidate := encodeJoint source word ordered task other otherAllocation
        have included := original_candidate_enters_system source word ordered task reserved held budget limits
          other otherAllocation fit
        have minimum := least candidate included
        simpa only [score, candidate, weightedForm_exact, readExtra, encodeJoint, extraAt_join _ _ _ _ fit.1] using minimum)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.JointTopup
