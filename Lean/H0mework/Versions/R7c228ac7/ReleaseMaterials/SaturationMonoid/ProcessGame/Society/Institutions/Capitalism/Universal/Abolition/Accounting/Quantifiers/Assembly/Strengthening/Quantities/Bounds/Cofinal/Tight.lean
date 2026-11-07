import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal

open Abolition.Root Abolition.Root.Registered Execution

noncomputable section

universe u v w

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Address : Type v} {Value : Type w}

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Policy" => Nat → C → Script

theorem the_cofinal_envelope_is_tight
    (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) :
    IsGLB (values source inspect read) (sInf (values source inspect read)) ∧
      IsLUB (values source inspect read) (sSup (values source inspect read)) :=
  ⟨isGLB_sInf _, isLUB_sSup _⟩

def objectiveValues (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (objective : (Address → EReal) → Value) : Set Value :=
  objective '' values source inspect read

private theorem actual_objective_iff (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (objective : (Address → EReal) → Value) (value : Value) :
    value ∈ objectiveValues source inspect read objective ↔
      ∃ policy, Paid source policy Issue inspect ∧ objective (peak source policy read) = value := by
  constructor
  · rintro ⟨_, ⟨policy, paid, rfl⟩, rfl⟩
    exact ⟨policy, paid, rfl⟩
  · rintro ⟨policy, paid, rfl⟩
    exact ⟨_, ⟨policy, paid, rfl⟩, rfl⟩

variable [CompleteLinearOrder Value]

inductive Minimum (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (objective : (Address → EReal) → Value)
  | attained (policy : Policy) (paid : Paid source policy Issue inspect)
      (exactValue : objective (peak source policy read) = sInf (objectiveValues source inspect read objective))
  | approached (nonempty : (objectiveValues source inspect read objective).Nonempty)
      (strict : ∀ policy, Paid source policy Issue inspect →
        sInf (objectiveValues source inspect read objective) < objective (peak source policy read))
      (near : ∀ limit, sInf (objectiveValues source inspect read objective) < limit →
        ∃ policy, Paid source policy Issue inspect ∧ objective (peak source policy read) < limit)
  | blocked (each : ∀ policy, Failure source policy Issue inspect)

/-- The coordinate or joint objective is evaluated on one cofinal paid
policy. Each approximant supplies all its own actual stages. -/
def resolveMinimum (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) (objective : (Address → EReal) → Value) :
    Minimum source inspect read objective := by
  classical
  let feasible := objectiveValues source inspect read objective
  have actual := actual_objective_iff source inspect read objective
  by_cases attained : sInf feasible ∈ feasible
  · let selected := Classical.choose ((actual _).mp attained)
    have paid := Classical.choose_spec ((actual _).mp attained)
    exact .attained selected paid.1 paid.2
  by_cases payable : feasible.Nonempty
  · refine .approached payable ?_ ?_
    · intro policy paid
      have present := (actual _).mpr ⟨policy, paid, rfl⟩
      exact lt_of_le_of_ne (sInf_le present) (fun same => attained (same.symm ▸ present))
    · intro limit higher
      obtain ⟨amount, present, below⟩ := sInf_lt_iff.mp higher
      obtain ⟨policy, paid, rfl⟩ := (actual amount).mp present
      exact ⟨policy, paid, below⟩
  · exact .blocked (fun policy =>
      (a_policy_fails_iff_an_actual_stage_or_clock_bound_explains_it source policy inspect).mp
        (fun paid => payable ⟨_, (actual _).mpr ⟨policy, paid, rfl⟩⟩))

theorem an_original_stage_witnesses_each_crossing_of_paid_cofinal_profiles
    (source : C) {Issue : Nat → C → Script → Type u}
    (inspect : (stage : Nat) → (current : C) → (word : Script) → Option (Issue stage current word))
    (read : Nat → C → Script → Address → EReal) {first second : Policy}
    (paidFirst : Paid source first Issue inspect) (paidSecond : Paid source second Issue inspect)
    (incomparable : ¬ peak source first read ≤ peak source second read ∧
      ¬ peak source second read ≤ peak source first read) :
    (∃ address stage, Settled (stageAt source first stage) (stageBody source first stage) ∧
      peak source second read address < read stage (stageAt source first stage) (stageBody source first stage) address) ∧
    (∃ address stage, Settled (stageAt source second stage) (stageBody source second stage) ∧
      peak source first read address < read stage (stageAt source second stage) (stageBody source second stage) address) := by
  classical
  have crossing (left right : Policy) (paid : Paid source left Issue inspect)
      (ordered : ¬ peak source left read ≤ peak source right read) :
      ∃ address stage, Settled (stageAt source left stage) (stageBody source left stage) ∧
        peak source right read address < read stage (stageAt source left stage) (stageBody source left stage) address := by
    have someStage := fun fits => ordered ((a_uniform_allowance_iff_every_actual_reading source left read _).mpr fits)
    obtain ⟨address, exceeded⟩ := not_forall.mp someStage
    obtain ⟨stage, below⟩ := not_forall.mp exceeded
    exact ⟨address, stage, paid.allStages stage, lt_of_not_ge below⟩
  exact ⟨crossing first second paidFirst incomparable.1, crossing second first paidSecond incomparable.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.Cofinal
