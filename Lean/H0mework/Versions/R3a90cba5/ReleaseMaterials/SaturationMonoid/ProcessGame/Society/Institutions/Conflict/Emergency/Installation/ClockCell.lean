import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Replay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm
open PublicFunction.Mandate

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Req" => Request Party Good Port (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port)

variable (base : RawLaw Party Good Port Technology Instrument)
  (scope : PublicFunction.Mandate.Scope (Party := Party) (Good := Good) (Port := Port))

local notation "scopeGuard" => SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.guard

omit [DecidableEq Good] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem guard_uses_the_original_clock (current : Raw) (action : Req) :
    scopeGuard base scope current action = Guard.any ∨ scopeGuard base scope current action = Guard.atLeast current.clock ∨
      scopeGuard base scope current action = Guard.below current.clock := by
  cases operation : action.operation <;> simp only [SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.guard, operation]
  case revise actor target =>
    cases last : target.last with
    | none => exact Or.inl rfl
    | some command =>
      cases command
      case propose | accept | renew => exact Or.inr (Or.inl rfl)
      case exit | revoke => exact Or.inl rfl
      case review =>
        simp only [commandGuard]
        split
        · exact Or.inl rfl
        · split
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl rfl)
  all_goals
    unfold ordinaryGuard
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl

omit [DecidableEq Good] [DecidableEq Technology] [DecidableEq Instrument] in
private theorem same_cell_holds (current : Raw) (action : Req) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (scopeGuard base scope current action).Holds a ↔ (scopeGuard base scope current action).Holds b := by
  rcases guard_uses_the_original_clock base scope current action with h | h | h
  · simp only [h, Guard.Holds]
  · simpa only [h, Guard.Holds] using same
  · simpa only [h, Guard.Holds, not_le] using not_congr same

omit [DecidableEq Instrument] in
/-- A single operation reads only the side of its physical clock on
which the proposed authorization deadline lies. This also covers refusal. -/
theorem valid_iff_same_cell (current : Raw) (action : Req) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).Valid current action ↔
      (law base (withCutoff scope b)).Valid current action := by
  have forward (first second : ℚ) (cell : current.clock ≤ first ↔ current.clock ≤ second)
      (valid : (law base (withCutoff scope first)).Valid current action) :
      (law base (withCutoff scope second)).Valid current action := by
    let firstScope := withCutoff scope first
    have own := (original_valid_iff_guard base firstScope current action first valid).mp valid
    exact (original_valid_iff_guard base firstScope current action second valid).mpr
      ((same_cell_holds base firstScope current action cell).mp own)
  exact ⟨forward a b same, forward b a same.symm⟩

theorem step_same_cell (current : Raw) (action : Req) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).step current action =
      (law base (withCutoff scope b)).step current action := by
  have valid := valid_iff_same_cell base scope current action same
  by_cases paid : (law base (withCutoff scope a)).Valid current action
  · rw [RawLaw.step, if_pos paid, RawLaw.step, if_pos (valid.mp paid)]
    rfl
  · rw [RawLaw.step, if_neg paid, RawLaw.step, if_neg (fun h => paid (valid.mpr h))]

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem step_clock (law : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Raw) (action : Req) : (law.step current action).clock = current.clock := by
  unfold RawLaw.step
  split <;> rfl

/-- Every item and post-state, including the physical successor of a
refused word, is constant inside its original clock cell. -/
theorem execute_same_cell (current : Raw) (index : Nat) (word : Word) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).execute current index word =
      (law base (withCutoff scope b)).execute current index word := by
  induction word generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    have clock := step_clock (law base (withCutoff scope b)) current action
    simp only [RawLaw.execute, step_same_cell base scope current action same,
      ih _ _ (clock.symm ▸ same)]

theorem next_same_cell (current : Raw) (word : Word) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).next current word =
      (law base (withCutoff scope b)).next current word := by
  simp only [RawLaw.next, execute_same_cell base scope current 0 word same]
  rfl

omit [DecidableEq Instrument] in
theorem actual_debit_same_cell (current : Raw) (action : Req) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).actualDebit current action =
      (law base (withCutoff scope b)).actualDebit current action := by
  have valid := valid_iff_same_cell base scope current action same
  by_cases paid : (law base (withCutoff scope a)).Valid current action
  · simp only [RawLaw.actualDebit, if_pos paid, if_pos (valid.mp paid)]
    rfl
  · simp only [RawLaw.actualDebit, if_neg paid, if_neg (fun h => paid (valid.mpr h))]

omit [DecidableEq Instrument] in
theorem actual_credit_same_cell (current : Raw) (action : Req) {a b : ℚ}
    (same : current.clock ≤ a ↔ current.clock ≤ b) :
    (law base (withCutoff scope a)).actualCredit current action =
      (law base (withCutoff scope b)).actualCredit current action := by
  have valid := valid_iff_same_cell base scope current action same
  by_cases paid : (law base (withCutoff scope a)).Valid current action
  · simp only [RawLaw.actualCredit, if_pos paid, if_pos (valid.mp paid)]
    rfl
  · simp only [RawLaw.actualCredit, if_neg paid, if_neg (fun h => paid (valid.mpr h))]

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency.Installation
