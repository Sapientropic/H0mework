import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent

open Abolition.Root Abolition.Root.Registered

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Event Signal Address Value : Type*}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → Signal → Script
local notation "Exposure" => Nat → C → Event → Script
local notation "Observation" => Nat → C → Signal
local notation "Reading" => Nat → C → Script → Address → EReal

theorem the_joint_contingent_ideal_is_paid_or_every_paid_policy_exceeds_it_at_a_real_cut
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) :
    let domain := values source expose observe inspect read
    IsGLB domain (sInf domain) ∧ IsLUB domain (sSup domain) ∧
      ((∃ policy, Paid source expose observe inspect policy ∧ peak source expose observe policy read = sInf domain) ∨
        ∀ policy, Paid source expose observe inspect policy →
          Exceeds source expose observe policy read (sInf domain)) := by
  let domain := values source expose observe inspect read
  refine ⟨isGLB_sInf domain, isLUB_sSup domain, ?_⟩
  cases decideBox source expose observe inspect read (sInf domain) with
  | paid policy actual within =>
    have observed : peak source expose observe policy read ∈ domain := ⟨policy, actual, rfl⟩
    exact .inl ⟨policy, actual, le_antisymm within (sInf_le observed)⟩
  | blocked every =>
    exact .inr fun policy paid => (every policy).resolve_left (fun failure => failure_refutes failure paid)

theorem contingent_incomparability_keeps_each_actual_excess
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) {first second : Policy}
    (paidFirst : Paid source expose observe inspect first) (paidSecond : Paid source expose observe inspect second)
    (incomparable : ¬ peak source expose observe first read ≤ peak source expose observe second read ∧
      ¬ peak source expose observe second read ≤ peak source expose observe first read) :
    Exceeds source expose observe first read (peak source expose observe second read) ∧
      Exceeds source expose observe second read (peak source expose observe first read) :=
  ⟨(an_excess_has_its_original_input_stage_and_bearer _ _ _ _ _ _ _ paidFirst).mp incomparable.1,
    (an_excess_has_its_original_input_stage_and_bearer _ _ _ _ _ _ _ paidSecond).mp incomparable.2⟩

def objectiveValues (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (objective : (Address → EReal) → Value) : Set Value :=
  { amount | ∃ policy, Paid source expose observe inspect policy ∧
    objective (peak source expose observe policy read) = amount }

variable [CompleteLinearOrder Value]

inductive Minimum (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (objective : (Address → EReal) → Value) : Type _
  | attained (policy : Policy) (paid : Paid source expose observe inspect policy)
      (exactValue : objective (peak source expose observe policy read) =
        sInf (objectiveValues source expose observe inspect read objective))
  | approached (actual : (objectiveValues source expose observe inspect read objective).Nonempty)
      (notReached : sInf (objectiveValues source expose observe inspect read objective) ∉
        objectiveValues source expose observe inspect read objective)
      (near : ∀ limit, sInf (objectiveValues source expose observe inspect read objective) < limit →
        ∃ policy, Paid source expose observe inspect policy ∧
          objective (peak source expose observe policy read) < limit)
  | blocked (each : ∀ policy, Failure source expose observe inspect policy)

/-- The policy in every approximant and at an attained endpoint is fixed
before any of its original events occur. -/
def resolveMinimum
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (objective : (Address → EReal) → Value) :
    Minimum source expose observe inspect read objective := by
  classical
  let domain := objectiveValues source expose observe inspect read objective
  by_cases reaches : sInf domain ∈ domain
  · exact .attained (Classical.choose reaches) (Classical.choose_spec reaches).1 (Classical.choose_spec reaches).2
  by_cases existsPaid : domain.Nonempty
  · refine .approached existsPaid reaches ?_
    intro limit higher
    obtain ⟨_, ⟨policy, paid, rfl⟩, close⟩ := sInf_lt_iff.mp higher
    exact ⟨policy, paid, close⟩
  · exact .blocked fun policy =>
      (every_failed_policy_has_an_original_branch_or_no_possible_input _ _ _ _ _).mp
        fun paid => existsPaid ⟨_, policy, paid, rfl⟩

theorem the_contingent_root_resolves_both_tight_objective_bounds
    (source : C) (expose : Exposure) (observe : Observation)
    {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Reading) (objective : (Address → EReal) → Value) :
    let domain := objectiveValues source expose observe inspect read objective
    IsGLB domain (sInf domain) ∧ IsLUB domain (sSup domain) ∧
      Nonempty (Minimum source expose observe inspect read objective) ∧
      Nonempty (Minimum source expose observe inspect read (fun amounts => OrderDual.toDual (objective amounts))) :=
  ⟨isGLB_sInf _, isLUB_sSup _, ⟨resolveMinimum _ _ _ _ _ _⟩, ⟨resolveMinimum _ _ _ _ _ _⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Contingent
