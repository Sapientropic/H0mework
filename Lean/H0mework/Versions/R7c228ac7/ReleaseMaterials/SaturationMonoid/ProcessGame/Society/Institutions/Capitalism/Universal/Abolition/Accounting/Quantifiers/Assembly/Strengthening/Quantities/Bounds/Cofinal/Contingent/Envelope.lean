import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Domain
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent

open Abolition.Root Abolition.Root.Registered Execution
open Recovery.Robust.Recurring (run)

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event Signal Address : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal
local notation "Reading" => Nat → C → Script → Address → EReal

def peak (source : C) (expose : Exposure) (observe : Observation)
    (policy : Policy) (read : Reading) (address : Address) : EReal :=
  ⨆ events, Cofinal.peak source (run expose observe policy events) read address

theorem the_joint_budget_iff_every_actual_input_stage_and_address_fits
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (read : Reading) (limit : Address → EReal) :
    peak source expose observe policy read ≤ limit ↔
      ∀ address events stage,
        let branch := run expose observe policy events
        read stage (stageAt source branch stage) (stageBody source branch stage) address ≤ limit address := by
  change (∀ address, peak source expose observe policy read address ≤ limit address) ↔ _
  simp only [peak, Cofinal.peak, iSup_le_iff]

def values (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) : Set (Address → EReal) :=
  { profile | ∃ policy, Paid source expose observe inspect policy ∧ peak source expose observe policy read = profile }

theorem every_contingent_profile_has_one_policy_and_actual_whole_ledger_writes
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (profile : Address → EReal) :
    profile ∈ values source expose observe inspect read ↔
      ∃ policy, Paid source expose observe inspect policy ∧ peak source expose observe policy read = profile ∧
        ∀ events stage,
          let branch := run expose observe policy events
          let current := stageAt source branch stage
          let word := stageBody source branch stage
          Recorded source (stageScript source branch stage) ∧ Settled current word ∧
            stageAt source branch (stage + 1) = endAt current word := by
  constructor
  · rintro ⟨policy, paid, rfl⟩
    exact ⟨policy, paid, rfl, fun events stage =>
      a_paid_stage_writes_the_original_whole_ledger_into_the_next_stage source _ inspect (paid.actual events) stage⟩
  · rintro ⟨policy, paid, rfl, _⟩
    exact ⟨policy, paid, rfl⟩

def Exceeds (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (read : Reading) (limit : Address → EReal) : Prop :=
  ∃ address events stage,
    let branch := run expose observe policy events
    let current := stageAt source branch stage
    let word := stageBody source branch stage
    Recorded source (stageScript source branch stage) ∧ Settled current word ∧
      limit address < read stage current word address

theorem an_excess_has_its_original_input_stage_and_bearer
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (limit : Address → EReal) (paid : Paid source expose observe inspect policy) :
    ¬ peak source expose observe policy read ≤ limit ↔ Exceeds source expose observe policy read limit := by
  classical
  rw [the_joint_budget_iff_every_actual_input_stage_and_address_fits]
  constructor
  · intro outside
    obtain ⟨address, outside⟩ := not_forall.mp outside
    obtain ⟨events, outside⟩ := not_forall.mp outside
    obtain ⟨stage, outside⟩ := not_forall.mp outside
    exact ⟨address, events, stage, record source _, (paid.actual events).allStages stage, lt_of_not_ge outside⟩
  · rintro ⟨address, events, stage, _, _, outside⟩ fits
    exact (not_le_of_gt outside) (fits address events stage)

inductive BoxDecision (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (limit : Address → EReal)
  | paid (policy : Policy) (actual : Paid source expose observe inspect policy)
      (fits : peak source expose observe policy read ≤ limit)
  | blocked (each : ∀ policy, Failure source expose observe inspect policy ∨
      Exceeds source expose observe policy read limit)

def decideBox (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (limit : Address → EReal) :
    BoxDecision source expose observe inspect read limit := by
  classical
  by_cases fits : ∃ policy, Paid source expose observe inspect policy ∧ peak source expose observe policy read ≤ limit
  · exact .paid (Classical.choose fits) (Classical.choose_spec fits).1 (Classical.choose_spec fits).2
  · refine .blocked fun policy => ?_
    by_cases paid : Paid source expose observe inspect policy
    · exact .inr ((an_excess_has_its_original_input_stage_and_bearer _ _ _ _ _ _ _ paid).mp
        fun within => fits ⟨policy, paid, within⟩)
    · exact .inl ((every_failed_policy_has_an_original_branch_or_no_possible_input _ _ _ _ _).mp paid)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent
