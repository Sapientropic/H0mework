import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Domain

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Address : Type v}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → C → Script

def peak (source : C) (policy : Policy) (read : Nat → C → Script → Address → EReal) (address : Address) :
    EReal :=
  ⨆ stage, read stage (stageAt source policy stage) (stageBody source policy stage) address

theorem a_uniform_allowance_iff_every_actual_reading
    (source : C) (policy : Policy) (read : Nat → C → Script → Address → EReal) (limit : Address → EReal) :
    peak source policy read ≤ limit ↔ ∀ address stage,
      read stage (stageAt source policy stage) (stageBody source policy stage) address ≤ limit address := by
  change (∀ address, peak source policy read address ≤ limit address) ↔ _
  simp only [peak, iSup_le_iff]

def values (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) : Set (Address → EReal) :=
  { profile | ∃ policy, Paid source policy Issue inspect ∧ peak source policy read = profile }

theorem every_cofinal_profile_has_the_actual_origins_and_successors
    (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (profile : Address → EReal) :
    profile ∈ values source inspect read ↔
      ∃ policy, Paid source policy Issue inspect ∧ peak source policy read = profile ∧
        ∀ stage, Recorded source (stageScript source policy stage) ∧
          Settled (stageAt source policy stage) (stageBody source policy stage) ∧
          stageAt source policy (stage + 1) = endAt (stageAt source policy stage) (stageBody source policy stage) := by
  constructor
  · rintro ⟨policy, paid, rfl⟩
    exact ⟨policy, paid, rfl, a_paid_stage_writes_the_original_whole_ledger_into_the_next_stage source policy inspect paid⟩
  · rintro ⟨policy, paid, exactProfile, _⟩
    exact ⟨policy, paid, exactProfile⟩

inductive BoxDecision (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (limit : Address → EReal)
  | paid (policy : Policy) (whole : Paid source policy Issue inspect) (fits : peak source policy read ≤ limit)
  | blocked (every : ∀ policy,
      (∀ stage, Recorded source (stageScript source policy stage)) ∧
        (Failure source policy Issue inspect ∨
          ∃ address stage, Settled (stageAt source policy stage) (stageBody source policy stage) ∧
            limit address < read stage (stageAt source policy stage) (stageBody source policy stage) address))

/-- One policy pays the whole vector in every actual stage. A failed box
retains the addressed excess at the stage where it really occurs. -/
def decideBox (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (limit : Address → EReal) :
    BoxDecision source inspect read limit := by
  classical
  by_cases feasible : ∃ policy, Paid source policy Issue inspect ∧ peak source policy read ≤ limit
  · let selected := Classical.choose feasible
    have paid := Classical.choose_spec feasible
    exact .paid selected paid.1 paid.2
  · refine .blocked (fun policy => ⟨fun stage => record source (stageScript source policy stage), ?_⟩)
    by_cases legal : Paid source policy Issue inspect
    · have outside : ¬ ∀ address stage,
          read stage (stageAt source policy stage) (stageBody source policy stage) address ≤ limit address :=
        fun all => feasible ⟨policy, legal, (a_uniform_allowance_iff_every_actual_reading _ _ _ _).mpr all⟩
      obtain ⟨address, exceeds⟩ := not_forall.mp outside
      obtain ⟨stage, earlier⟩ := not_forall.mp exceeds
      exact .inr ⟨address, stage, legal.allStages stage, lt_of_not_ge earlier⟩
    · exact .inl ((a_policy_fails_iff_an_actual_stage_or_clock_bound_explains_it source policy inspect).mp legal)

theorem the_joint_cofinal_ideal_is_paid_or_every_paid_policy_has_an_addressed_excess
    (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) :
    (∃ policy, Paid source policy Issue inspect ∧ peak source policy read = sInf (values source inspect read)) ∨
      ∀ policy, Paid source policy Issue inspect → ∃ address stage,
        Settled (stageAt source policy stage) (stageBody source policy stage) ∧
          sInf (values source inspect read) address <
            read stage (stageAt source policy stage) (stageBody source policy stage) address := by
  cases decideBox source inspect read (sInf (values source inspect read)) with
  | paid policy whole fits =>
    exact .inl ⟨policy, whole, le_antisymm fits (sInf_le (show peak source policy read ∈ values source inspect read
      from ⟨policy, whole, rfl⟩))⟩
  | blocked every =>
    refine .inr fun policy paid => ?_
    rcases (every policy).2 with failure | excess
    · exact (failure_refutes failure paid).elim
    · exact excess

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal
