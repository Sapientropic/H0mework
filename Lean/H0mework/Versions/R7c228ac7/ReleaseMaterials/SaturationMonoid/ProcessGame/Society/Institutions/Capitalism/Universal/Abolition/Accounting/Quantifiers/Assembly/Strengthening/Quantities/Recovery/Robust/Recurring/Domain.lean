import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.History
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Clock

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event : Type u} {Signal : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal

inductive Failure (source : C) (expose : Exposure) (observe : Observation) (policy : Policy) : Prop
  | repair (events : Nat → Event) (stage : Nat) (issue :
      let current := currentAt source expose observe policy events stage
      let exposure := exposureAt source expose observe policy events stage
      Nonempty (BranchIssue current exposure (repairAt observe policy stage current exposure)))
      (original : Recorded source (stageScript source (run expose observe policy events) (stage + 1)))
  | boundedClock (events : Nat → Event) (bound : ℚ)
      (bounded : ∀ stage, (currentAt source expose observe policy events stage).raw.clock < bound)
      (original : ∀ stage, Recorded source (stageScript source (run expose observe policy events) stage))

theorem policy_fails_iff_an_actual_history_has_an_original_obstruction
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy) :
    ¬ PolicyPaid source expose observe policy ↔ Failure source expose observe policy := by
  constructor
  · intro failed
    classical
    by_cases restored : ∀ events stage, PaidAt source expose observe policy events stage
    · have bounded : ¬ ∀ events, Bounds.Cofinal.ClockCofinal source (run expose observe policy events) :=
        fun time => failed ⟨restored, time⟩
      obtain ⟨events, tooShort⟩ := not_forall.mp bounded
      obtain ⟨limit, never⟩ := not_forall.mp tooShort
      exact .boundedClock events limit (fun stage => lt_of_not_ge (fun enough => never ⟨stage, enough⟩))
        (fun stage => record source _)
    · obtain ⟨events, needs⟩ := not_forall.mp restored
      obtain ⟨stage, missing⟩ := not_forall.mp needs
      exact .repair events stage (failed_branch_has_original_issue _ _ _ missing) (record source _)
  · intro failure paid
    cases failure with
    | repair events stage issue original =>
      obtain ⟨blocked⟩ := issue
      exact blocked.refutes (paid.restoration events stage)
    | boundedClock events limit bounded original =>
      obtain ⟨stage, beyond⟩ := paid.clock events limit
      exact (not_lt_of_ge beyond) (bounded stage)

theorem a_uniform_actual_exposure_quantum_makes_paid_repairs_cofinal
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (quantum : ℚ) (positive : 0 < quantum)
    (restored : ∀ events stage, PaidAt source expose observe policy events stage)
    (duration : ∀ events stage,
      quantum ≤ elapsed (currentAt source expose observe policy events stage)
        (exposureAt source expose observe policy events stage)) :
    PolicyPaid source expose observe policy := by
  refine ⟨restored, fun events => Bounds.Cofinal.a_positive_paid_clock_quantum_crosses_every_physical_horizon
    source (run expose observe policy events) quantum positive ?_⟩
  intro stage
  let current := currentAt source expose observe policy events stage
  let exposure := exposureAt source expose observe policy events stage
  let repair := repairAt observe policy stage current exposure
  change quantum ≤ elapsed current (exposure ++ repair)
  rw [exact_elapsed_sum]
  exact (duration events stage).trans (le_add_of_nonneg_right (elapsed_nonnegative (endAt current exposure) repair))

def worst (source : C) (expose : Exposure) (observe : Observation) (policy : Policy) : EReal :=
  ⨆ events, ⨆ stage, ratioAt source expose observe policy events stage

theorem every_original_exposure_and_repair_fits_the_uniform_conversion
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy) (limit : EReal) :
    worst source expose observe policy ≤ limit ↔
      ∀ events stage, ratioAt source expose observe policy events stage ≤ limit := by
  simp only [worst, iSup_le_iff]

def values (source : C) (expose : Exposure) (observe : Observation) : Set EReal :=
  { amount | ∃ policy, PolicyPaid source expose observe policy ∧ worst source expose observe policy = amount }

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring
