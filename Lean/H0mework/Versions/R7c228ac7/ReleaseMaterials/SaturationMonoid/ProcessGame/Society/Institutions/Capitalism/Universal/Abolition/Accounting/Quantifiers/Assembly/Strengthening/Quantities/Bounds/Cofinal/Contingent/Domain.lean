import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent

open Abolition.Root Abolition.Root.Registered Execution
open Recovery.Robust.Recurring (repairAt run)

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event Signal : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal

/-- One observation policy is committed for every input sequence. Each
branch uses the original actual cofinal stage checks and settlement. -/
structure Paid (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (policy : Policy) : Prop where
  hasInput : Nonempty (Nat → Event)
  actual : ∀ events, Cofinal.Paid source (run expose observe policy events) Issue inspect

inductive Failure (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (policy : Policy) : Prop
  | noInput (missing : ¬ Nonempty (Nat → Event)) (original : Recorded source [])
  | branch (events : Nat → Event)
      (issue : Cofinal.Failure source (run expose observe policy events) Issue inspect)
      (original : ∀ stage, Recorded source (stageScript source (run expose observe policy events) stage))

theorem failure_refutes {source : C} {expose : Exposure} {observe : Observation}
    {Issue : Nat → C → Script → Type u}
    {inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word)}
    {policy : Policy} (failure : Failure source expose observe inspect policy) :
    ¬ Paid source expose observe inspect policy := by
  intro paid
  cases failure with
  | noInput missing _ => exact missing paid.hasInput
  | branch events issue _ => exact Cofinal.failure_refutes issue (paid.actual events)

theorem every_failed_policy_has_an_original_branch_or_no_possible_input
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (policy : Policy) :
    ¬ Paid source expose observe inspect policy ↔ Failure source expose observe inspect policy := by
  constructor
  · intro failed
    classical
    by_cases input : Nonempty (Nat → Event)
    · have blocked : ¬ ∀ events, Cofinal.Paid source (run expose observe policy events) Issue inspect :=
        fun actual => failed ⟨input, actual⟩
      obtain ⟨events, fails⟩ := not_forall.mp blocked
      exact .branch events ((a_policy_fails_iff_an_actual_stage_or_clock_bound_explains_it
        source (run expose observe policy events) inspect).mp fails) (fun stage => record source _)
    · exact .noInput input (record source [])
  · exact failure_refutes

def responsive (expose : Exposure) (observe : Observation) (policy : Policy)
    (choose : Nat → C → Event) : Nat → C → Script :=
  fun stage current =>
    let exposure := expose stage current (choose stage current)
    exposure ++ repairAt observe policy stage current exposure

def emitted (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (choose : Nat → C → Event) : Nat → Event :=
  fun stage => choose stage (stageAt source (responsive expose observe policy choose) stage)

/-- Even an input source reacting to the original current has an exact
unfolding. The controller still sees only its current observation. -/
theorem an_adaptive_input_generates_the_same_actual_prefix_as_its_own_emissions
    (source : C) (expose : Exposure) (observe : Observation) (policy : Policy)
    (choose : Nat → C → Event) (stage : Nat) :
    stageScript source (run expose observe policy (emitted source expose observe policy choose)) stage =
      stageScript source (responsive expose observe policy choose) stage := by
  induction stage with
  | zero => rfl
  | succ stage previous =>
    simp only [stageScript, previous, run, responsive, emitted, stageAt]

theorem precommitment_pays_every_adaptive_source_branch
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (policy : Policy) (paid : Paid source expose observe inspect policy)
    (choose : Nat → C → Event) :
    Cofinal.Paid source (responsive expose observe policy choose) Issue inspect := by
  let events := emitted source expose observe policy choose
  have samePrefix (stage : Nat) := an_adaptive_input_generates_the_same_actual_prefix_as_its_own_emissions
    source expose observe policy choose stage
  have current (stage : Nat) :
      stageAt source (run expose observe policy events) stage =
        stageAt source (responsive expose observe policy choose) stage :=
    congrArg (endAt source) (samePrefix stage)
  have body (stage : Nat) :
      stageBody source (run expose observe policy events) stage =
        stageBody source (responsive expose observe policy choose) stage := by
    unfold stageBody
    rw [current]
    rfl
  exact {
    allStages := fun stage => by
      simpa only [current stage, body stage] using (paid.actual events).allStages stage
    passes := fun stage => by
      have same := congrArg (fun atCut : C × Script => inspect stage atCut.1 atCut.2 = none)
        (congrArg₂ Prod.mk (current stage) (body stage))
      exact same.mp ((paid.actual events).passes stage)
    time := fun horizon => by
      obtain ⟨stage, crossed⟩ := (paid.actual events).time horizon
      exact ⟨stage, current stage ▸ crossed⟩ }

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent
