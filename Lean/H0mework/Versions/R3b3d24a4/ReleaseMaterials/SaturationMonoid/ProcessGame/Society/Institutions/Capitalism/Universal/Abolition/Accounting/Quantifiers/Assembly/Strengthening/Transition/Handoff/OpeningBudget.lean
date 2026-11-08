import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Readings
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Allocation.Objective

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Abolition.Root Abolition.Root.Registered PublicFunction Quantities

noncomputable section

variable {Party Good Port Technology Instrument TaskId : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq TaskId]
  (source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
  (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
    Finset (Due.Service.Ordinal source word))
  (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ)
  (deadline : WithTop ℚ)

local notation "Plan" => Proposal Party Good Port Technology Instrument

/-- A computed allocation can enter the original payment directly once its
required stock is present. Its projected quantity alone carries no credit. -/
theorem an_opening_witness_is_consumed_by_the_original_handoff
    (proposal : Plan) (target : Party × Good) (amount : ℚ)
    (allocation : Assignment source ordered task proposal)
    (projected : Allocation.FitsAt source (script source proposal) ordered task
      (reserved (script source proposal)) held budget target amount allocation)
    (funded : amount ≤ Allocation.opening source budget target)
    (route : Checked source proposal) (demands : Due.Service.OriginalDemands ordered.toFinset task)
    (whole : Settled source (script source proposal)) (timely : (handoffTime source proposal : WithTop ℚ) ≤ deadline) :
    valid source ordered task reserved held budget deadline ⟨proposal, allocation⟩ ∧
      Evolving.Epoch.Current.ClosedAt (completed source proposal) := by
  have fits : Fits source ordered task reserved held budget proposal allocation :=
    ((Allocation.with_available_stock_at_the_target_uses_the_same_joint_contract _ _ _ _ _ _ _ _ _).mp
      (Allocation.fitsAt_increases_with_real_stock _ _ _ _ _ _ _ _ _ _ _ projected funded)).1
  have admitted : Admitted source ordered task reserved held budget deadline proposal :=
    ⟨(inspection_is_complete source ordered task reserved held budget proposal).mpr
      ⟨route, demands, whole, allocation, fits⟩, timely⟩
  exact ⟨⟨admitted, fits⟩, whole.toRecorded.next⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
