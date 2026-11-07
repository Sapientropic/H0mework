import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Nature : Type u} {Observation : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

/-- A common numerical allowance is implementable before the event exactly
when every observation fibre admits one shared paid repair at that allowance. -/
theorem a_precommitted_allowance_is_exactly_jointly_feasible_in_each_observation
    (origin : C) (expose : Nature → Script) (observe : C → Observation) (allowance : EReal) :
    (∃ policy, ValidPolicy origin expose observe policy ∧ worst origin expose observe policy ≤ allowance) ↔
    ∀ signal : Observation, ∃ repair : Script, ∀ event,
      observe (Execution.endAt origin (expose event)) = signal →
      BranchPaid origin (expose event) repair ∧ hourRatio origin (expose event) repair ≤ allowance := by
  constructor
  · rintro ⟨policy, paid, bounded⟩ signal
    have each := (worst_le_iff_every_original_event origin expose observe policy allowance).mp bounded
    refine ⟨policy signal, fun event seen => ?_⟩
    simpa only [response, seen] using And.intro (paid event) (each event)
  · intro feasible
    classical
    choose policy shared using feasible
    have actual (event : Nature) :=
      shared (observe (Execution.endAt origin (expose event))) event rfl
    exact ⟨policy, fun event => (actual event).1,
      (worst_le_iff_every_original_event origin expose observe policy allowance).mpr (fun event => (actual event).2)⟩

theorem indistinguishable_events_with_no_common_repair_block_every_policy
    (origin : C) (expose : Nature → Script) (observe : C → Observation)
    (first second : Nature)
    (same : observe (Execution.endAt origin (expose first)) =
      observe (Execution.endAt origin (expose second)))
    (conflict : ∀ repair, BranchPaid origin (expose first) repair → ¬ BranchPaid origin (expose second) repair) :
    ∀ policy, ¬ ValidPolicy origin expose observe policy := by
  intro policy valid
  have sameRepair := same_actual_observation_forces_the_same_repair origin observe policy (expose first) (expose second) same
  exact conflict _ (valid first) (sameRepair.symm ▸ valid second)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust
