import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Minimum
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
The exact reparation bound ranges over all eligible finite original words.
The real infimum separates an actual whole-ledger write from approach by
successive precision requests. A limit does not supply a paid receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

variable (answers : ReceiptAnswers seed) (loss : Reparation.Actual.Occurrence seed community)
  (registered : Reparation.Actual.Script Party Good Port Technology Instrument → Prop)

/-- The registered predicate may be unrestricted. Retention remains a
legal comparison independently of the register. -/
def Allowed (word : Word) : Prop :=
  (word = [] ∨ registered word) ∧ Eligible answers loss word

theorem retain_is_allowed : Allowed answers loss registered [] :=
  ⟨Or.inl rfl, retain_is_eligible answers loss⟩

def value (word : Word) : ℝ := ((balance answers loss word).remaining : ℝ)

/-- Only balances of the original row on its actual whole-ledger
successors enter the value set. -/
def values : Set ℝ :=
  fun amount => ∃ word : Word, Allowed answers loss registered word ∧ value answers loss word = amount

def infimum : ℝ := sInf (values answers loss registered)

theorem values_nonempty : (values answers loss registered).Nonempty :=
  ⟨value answers loss [], [], retain_is_allowed answers loss registered, rfl⟩

theorem value_nonnegative (word : Word) : 0 ≤ value answers loss word := by
  change (0 : ℝ) ≤ ((balance answers loss word).remaining : ℝ)
  exact_mod_cast (balance answers loss word).nonnegative

theorem values_bddBelow : BddBelow (values answers loss registered) := by
  refine ⟨0, ?_⟩
  rintro amount ⟨word, _, rfl⟩
  exact value_nonnegative answers loss word

theorem infimum_is_the_greatest_lower_bound :
    IsGLB (values answers loss registered) (infimum answers loss registered) :=
  isGLB_csInf (values_nonempty answers loss registered) (values_bddBelow answers loss registered)

theorem infimum_nonnegative : 0 ≤ infimum answers loss registered := by
  apply le_csInf (values_nonempty answers loss registered)
  rintro amount ⟨word, _, rfl⟩
  exact value_nonnegative answers loss word

theorem infimum_le_actual_word (word : Word) (allowed : Allowed answers loss registered word) :
    infimum answers loss registered ≤ value answers loss word :=
  csInf_le (values_bddBelow answers loss registered) ⟨word, allowed, rfl⟩

/-- Proofs for the existing successor of a word. The record does not carry
a separately constructed successor or responsibility portfolio. -/
structure ActualWrite (word : Word) : Prop where
  recorded : Quantities.Recorded seed (history loss ++ word)
  authority : SourceAuthority (endAt seed (history loss)) word
  lossInventory : (reached answers loss word).stack.balances.map Prod.fst =
    originalLosses seed community (history loss)
  originalRow : ∃ row, (reached answers loss word).read row = .inr (loss, balance answers loss word)

theorem an_eligible_word_has_its_actual_whole_write (word : Word)
    (eligible : Eligible answers loss word) : ActualWrite answers loss word :=
  ⟨reached_records_the_whole_history loss word,
    an_eligible_word_has_original_source_authority community answers _ _ _ eligible,
    (reached_origins answers loss word).trans
      (eligible_preserves_the_literal_original_loss_inventory community answers _ _ _ eligible),
    reached_reads_exact_origin answers loss word⟩

theorem every_positive_precision_has_an_actual_eligible_word (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ word : Word, Allowed answers loss registered word ∧
      infimum answers loss registered ≤ value answers loss word ∧
      value answers loss word < infimum answers loss registered + epsilon ∧
      ActualWrite answers loss word := by
  have close : infimum answers loss registered < infimum answers loss registered + epsilon :=
    lt_add_of_pos_right _ positive
  obtain ⟨amount, ⟨word, allowed, rfl⟩, below⟩ :=
    exists_lt_of_csInf_lt (values_nonempty answers loss registered) close
  exact ⟨word, allowed, infimum_le_actual_word answers loss registered word allowed, below,
    an_eligible_word_has_its_actual_whole_write answers loss word allowed.2⟩

theorem an_unattained_infimum_is_strict_at_each_actual_word
    (unattained : infimum answers loss registered ∉ values answers loss registered)
    (word : Word) (allowed : Allowed answers loss registered word) :
    infimum answers loss registered < value answers loss word :=
  lt_of_le_of_ne (infimum_le_actual_word answers loss registered word allowed)
    (fun same => unattained ⟨word, allowed, same.symm⟩)

/-- Either an original word achieves the bound or every positive precision
has a strictly higher original successor within that precision. -/
theorem resolve :
    (∃ word : Word, Allowed answers loss registered word ∧
      value answers loss word = infimum answers loss registered ∧ ActualWrite answers loss word) ∨
    (infimum answers loss registered ∉ values answers loss registered ∧
      (∀ word : Word, Allowed answers loss registered word →
        infimum answers loss registered < value answers loss word) ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ word : Word, Allowed answers loss registered word ∧
        infimum answers loss registered < value answers loss word ∧
        value answers loss word < infimum answers loss registered + epsilon ∧ ActualWrite answers loss word) := by
  classical
  by_cases attained : infimum answers loss registered ∈ values answers loss registered
  · obtain ⟨word, allowed, exactValue⟩ := attained
    exact Or.inl ⟨word, allowed, exactValue, an_eligible_word_has_its_actual_whole_write answers loss word allowed.2⟩
  · refine Or.inr ⟨attained, an_unattained_infimum_is_strict_at_each_actual_word answers loss registered attained, ?_⟩
    intro epsilon positive
    obtain ⟨word, allowed, _, below, written⟩ :=
      every_positive_precision_has_an_actual_eligible_word answers loss registered epsilon positive
    exact ⟨word, allowed,
      an_unattained_infimum_is_strict_at_each_actual_word answers loss registered attained word allowed, below, written⟩

theorem can_clear_iff_attains_zero :
    (∃ word : Word, Allowed answers loss registered word ∧
      Nonempty (Paid (.live (balance answers loss word))) ∧ ActualWrite answers loss word) ↔
    infimum answers loss registered = 0 ∧ infimum answers loss registered ∈ values answers loss registered := by
  constructor
  · rintro ⟨word, allowed, ⟨paid⟩, _⟩
    have zero : value answers loss word = 0 := by
      change ((balance answers loss word).remaining : ℝ) = 0
      exact_mod_cast paid.down
    have minimumZero := le_antisymm ((infimum_le_actual_word answers loss registered word allowed).trans_eq zero)
      (infimum_nonnegative answers loss registered)
    exact ⟨minimumZero, word, allowed, zero.trans minimumZero.symm⟩
  · rintro ⟨zero, word, allowed, amount⟩
    have exactZero : (balance answers loss word).remaining = 0 := by
      have castZero : ((balance answers loss word).remaining : ℝ) = 0 := amount.trans zero
      exact_mod_cast castZero
    exact ⟨word, allowed, ⟨⟨exactZero⟩⟩, an_eligible_word_has_its_actual_whole_write answers loss word allowed.2⟩

theorem unattained_zero_keeps_every_original_residual
    (zero : infimum answers loss registered = 0)
    (unattained : infimum answers loss registered ∉ values answers loss registered)
    (word : Word) (allowed : Allowed answers loss registered word) :
    Nonempty (Obstruction (.live (balance answers loss word))) ∧
      IsEmpty (Paid (.live (balance answers loss word))) ∧
      0 < (residual answers loss word).2.2 ∧ ActualWrite answers loss word := by
  have positive := an_unattained_infimum_is_strict_at_each_actual_word answers loss registered unattained word allowed
  rw [zero] at positive
  have oldPositive : 0 < (balance answers loss word).remaining := by
    change (0 : ℝ) < ((balance answers loss word).remaining : ℝ) at positive
    exact_mod_cast positive
  exact ⟨⟨⟨oldPositive⟩⟩, ⟨fun paid => (ne_of_gt oldPositive) paid.down⟩, oldPositive,
    an_eligible_word_has_its_actual_whole_write answers loss word allowed.2⟩

#print axioms infimum_is_the_greatest_lower_bound
#print axioms resolve
#print axioms can_clear_iff_attains_zero
#print axioms unattained_zero_keeps_every_original_residual

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Unbounded
