import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Entry

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal

open Reparation.Actual (ReceiptAnswers Script)
open Occurrence.Unbounded (value value_nonnegative)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Reparation.Actual.Occurrence seed community) (answers : ReceiptAnswers seed)
  (registered : Script Party Good Port Technology Instrument → Prop)
  (offers : ProductionMenu Party Good Port Technology Instrument := ProductionMenu.empty)

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Entry" => (fun word => ViableEntry loss answers registered word offers)

def WholeCleared (word : Word) : Prop :=
  ∀ row ∈ (Occurrence.reached answers loss word).stack.balances, row.2.remaining = 0

inductive SettlementTarget
  | originalClaim
  | wholePortfolio

/-- The portfolio objective checks simultaneous clearance. Its score
compares no quantities with different material units. -/
def settlementValue (target : SettlementTarget) (word : Word) : ℝ := by
  classical
  exact match target with
  | .originalClaim => value answers loss word
  | .wholePortfolio => if WholeCleared loss answers word then 0 else 1

theorem settlementValue_nonnegative (target : SettlementTarget) (word : Word) :
    0 ≤ settlementValue loss answers target word := by
  classical
  cases target
  · exact value_nonnegative answers loss word
  · by_cases cleared : WholeCleared loss answers word <;> simp [settlementValue, cleared]

theorem portfolio_value_is_zero_iff (word : Word) :
    settlementValue loss answers .wholePortfolio word = 0 ↔ WholeCleared loss answers word := by
  classical
  by_cases cleared : WholeCleared loss answers word <;> simp [settlementValue, cleared]

variable (target : SettlementTarget := .originalClaim)

def liveValues : Set ℝ :=
  {amount | ∃ word : Word, Entry word ∧ settlementValue loss answers target word = amount}

def liveInfimum : ℝ := sInf (liveValues loss answers registered offers target)

theorem liveValues_bddBelow : BddBelow (liveValues loss answers registered offers target) := by
  refine ⟨0, ?_⟩
  rintro amount ⟨word, _, rfl⟩
  exact settlementValue_nonnegative loss answers target word

theorem liveInfimum_le_every_actual_terminal (word : Word)
    (live : Entry word) :
    liveInfimum loss answers registered offers target ≤ settlementValue loss answers target word :=
  csInf_le (liveValues_bddBelow loss answers registered offers target) ⟨word, live, rfl⟩

private theorem exists_terminal_word_near (feasible : ∃ word, Entry word)
    (precision : ℝ) (positive : 0 < precision) :
    ∃ word : Word, Entry word ∧ settlementValue loss answers target word < liveInfimum loss answers registered offers target + precision := by
  obtain ⟨first, viable⟩ := feasible
  have someValue : (liveValues loss answers registered offers target).Nonempty :=
    ⟨_, first, viable, rfl⟩
  obtain ⟨_, ⟨word, live, rfl⟩, near⟩ :=
    exists_lt_of_csInf_lt someValue (lt_add_of_pos_right (liveInfimum loss answers registered offers target) positive)
  exact ⟨word, live, near⟩

def shortestWord {A : Type} (eligible : List A → Prop) (available : ∃ word, eligible word) :
    {word : List A // eligible word ∧ ∀ other, eligible other → word.length ≤ other.length} := by
  classical
  have widths : ∃ visits, ∃ word, eligible word ∧ word.length = visits := by
    obtain ⟨word, actual⟩ := available
    exact ⟨word.length, word, actual, rfl⟩
  let word := Classical.choose (Nat.find_spec widths)
  have checked := Classical.choose_spec (Nat.find_spec widths)
  refine ⟨word, checked.1, fun other accepted => checked.2.trans_le ?_⟩
  exact Nat.find_min' widths ⟨other, accepted, rfl⟩

inductive Outcome where
  | attained (word : Word) (run : Realization loss answers registered word offers)
      (minimum : settlementValue loss answers target word = liveInfimum loss answers registered offers target)
      (fewestVisits : ∀ other : Word, Entry other →
        settlementValue loss answers target other = liveInfimum loss answers registered offers target → word.length ≤ other.length)
  | approached (unattained : liveInfimum loss answers registered offers target ∉ liveValues loss answers registered offers target)
      (atPrecision : ∀ precision : ℝ, 0 < precision →
        (word : Word) × {_run : Realization loss answers registered word offers //
          liveInfimum loss answers registered offers target < settlementValue loss answers target word ∧
          settlementValue loss answers target word < liveInfimum loss answers registered offers target + precision ∧
          ∀ other : Word, Entry other →
            settlementValue loss answers target other < liveInfimum loss answers registered offers target + precision → word.length ≤ other.length})
  | obstructed (failure : ∀ word : Word, ¬ Nonempty (Realization loss answers registered word offers))
      (originalRow : ∃ row, (Occurrence.reached answers loss []).read row =
        .inr (loss, Occurrence.balance answers loss []))

/-- Optimize reparation over the finite prefixes that actually leave a
cofinal living strategy. A better paper balance cannot outrank viability. -/
def source_generated_terminal_peace : Outcome loss answers registered offers target := by
  classical
  by_cases feasible : ∃ word : Word, Entry word
  · by_cases attained : liveInfimum loss answers registered offers target ∈ liveValues loss answers registered offers target
    · let selected := shortestWord (fun word : Word => Entry word ∧
          settlementValue loss answers target word = liveInfimum loss answers registered offers target) attained
      exact .attained selected.val (realize selected.property.1.1) selected.property.1.2
        (fun other live amount => selected.property.2 other ⟨live, amount⟩)
    · refine .approached attained fun precision positive => ?_
      have near := exists_terminal_word_near loss answers registered offers target feasible precision positive
      let selected := shortestWord (fun word : Word => Entry word ∧
          settlementValue loss answers target word < liveInfimum loss answers registered offers target + precision) near
      have exactValue := selected.property.1
      have above : liveInfimum loss answers registered offers target < settlementValue loss answers target selected.val :=
        lt_of_le_of_ne (liveInfimum_le_every_actual_terminal loss answers registered offers target selected.val exactValue.1)
          (fun same => attained ⟨selected.val, exactValue.1, same.symm⟩)
      exact ⟨selected.val, ⟨realize exactValue.1, above, exactValue.2,
        fun other live amount => selected.property.2 other ⟨live, amount⟩⟩⟩
  · refine .obstructed (fun word actual =>
      feasible ⟨word, viable_entry_iff_actual_terminal.mpr actual⟩) ?_
    exact Occurrence.reached_reads_exact_origin answers loss []

theorem full_actual_reparation_and_living_peace_iff_zero_is_attained :
    (∃ word : Word, Nonempty (Realization loss answers registered word offers) ∧
      (Occurrence.balance answers loss word).remaining = 0) ↔
      liveInfimum loss answers registered offers = 0 ∧
        liveInfimum loss answers registered offers ∈ liveValues loss answers registered offers := by
  constructor
  · rintro ⟨word, ⟨run⟩, zero⟩
    have live := realization_has_an_exactly_viable_source run
    have exactZero : value answers loss word = 0 := by
      simp [Occurrence.Unbounded.value, zero]
    have lower : 0 ≤ liveInfimum loss answers registered offers := by
      apply le_csInf
      · exact ⟨_, word, live, rfl⟩
      · rintro amount ⟨candidate, _, rfl⟩
        exact value_nonnegative answers loss candidate
    have minimum := le_antisymm ((liveInfimum_le_every_actual_terminal loss answers registered offers .originalClaim word live).trans_eq exactZero) lower
    exact ⟨minimum, word, live, exactZero.trans minimum.symm⟩
  · rintro ⟨zero, word, live, exactValue⟩
    refine ⟨word, ⟨realize live⟩, ?_⟩
    have exactZero : ((Occurrence.balance answers loss word).remaining : ℝ) = 0 := exactValue.trans zero
    exact_mod_cast exactZero

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal
