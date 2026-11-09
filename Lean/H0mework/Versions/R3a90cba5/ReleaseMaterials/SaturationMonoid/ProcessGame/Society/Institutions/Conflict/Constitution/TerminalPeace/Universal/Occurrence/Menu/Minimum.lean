import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.Menu.Eligibility
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence.BirthBalance
import Mathlib.Data.List.MinMax

/-!
Select the least actual outstanding reparation on a finite registered menu.
Only native authorized damage-free words are scored. Retention is always
a candidate and is first in the tie order.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Loss" => Reparation.Actual.Occurrence seed community

variable (answers : ReceiptAnswers seed) (loss : Reparation.Actual.Occurrence seed community)
  (menu : List (Reparation.Actual.Script Party Good Port Technology Instrument))

/-- An actual authorized word attaining the menu's least old balance. -/
structure MenuChoice where
  word : Word
  eligible : Eligible answers loss word
  registered : word = [] ∨ word ∈ menu
  least : ∀ candidate : Word, (candidate = [] ∨ candidate ∈ menu) → Eligible answers loss candidate →
    (balance answers loss word).remaining ≤ (balance answers loss candidate).remaining

local notation "Candidate" => {word : Word // Eligible answers loss word}

private def retain : Candidate := ⟨[], retain_is_eligible answers loss⟩

private def entries : List Candidate :=
  menu.filterMap fun word =>
    if checked : Eligible answers loss word then some ⟨word, checked⟩ else none

private theorem mem_entries (candidate : Candidate) :
    candidate ∈ entries answers loss menu ↔ candidate.val ∈ menu := by
  unfold entries
  constructor
  · intro listed
    obtain ⟨word, registered, tested⟩ := List.mem_filterMap.mp listed
    split at tested
    · exact (congrArg Subtype.val (Option.some.inj tested)) ▸ registered
    · cases tested
  · intro listed
    refine List.mem_filterMap.mpr ⟨candidate.val, listed, ?_⟩
    rw [dif_pos candidate.property]

private def candidates : List Candidate :=
  retain answers loss :: entries answers loss menu

private theorem mem_candidates (candidate : Candidate) :
    candidate ∈ candidates answers loss menu ↔ candidate.val = [] ∨ candidate.val ∈ menu := by
  unfold candidates
  rw [List.mem_cons, mem_entries]
  refine or_congr ⟨fun same => congrArg Subtype.val same, ?_⟩ Iff.rfl
  intro empty
  exact Subtype.ext (show candidate.val = (retain answers loss).val from empty)

private def score (candidate : Candidate) : ℚ :=
  (balance answers loss candidate.val).remaining

private theorem minimum_exists :
    ((candidates answers loss menu).argmin (score answers loss)).isSome :=
  Option.ne_none_iff_isSome.mp fun empty =>
    List.cons_ne_nil _ _ (List.argmin_eq_none.mp empty)

private def winningCandidate : Candidate :=
  ((candidates answers loss menu).argmin (score answers loss)).get (minimum_exists answers loss menu)

private theorem winner_is_the_argmin :
    winningCandidate answers loss menu ∈ (candidates answers loss menu).argmin (score answers loss) := by
  have same := (Option.some_get (minimum_exists answers loss menu)).symm
  change (candidates answers loss menu).argmin (score answers loss) = some (winningCandidate answers loss menu) at same
  rw [same]
  simp

/-- Filter the menu using the actual dispatcher, then minimize the original
row's balance after each eligible whole write. -/
def choose : MenuChoice answers loss menu := by
  let winner := winningCandidate answers loss menu
  have selected := winner_is_the_argmin answers loss menu
  refine ⟨winner.val, winner.property, (mem_candidates answers loss menu winner).mp (List.argmin_mem selected), ?_⟩
  intro word listed checked
  let other : Candidate := ⟨word, checked⟩
  have member := (mem_candidates answers loss menu other).mpr listed
  change score answers loss winner ≤ score answers loss other
  exact List.le_of_mem_argmin (f := score answers loss) member selected

theorem retain_wins_when_no_eligible_offer_improves
    (unimproved : ∀ word ∈ menu, Eligible answers loss word →
      (balance answers loss []).remaining ≤ (balance answers loss word).remaining) :
    (choose answers loss menu).word = [] := by
  have kept : (candidates answers loss menu).argmin (score answers loss) = some (retain answers loss) := by
    unfold candidates
    rw [List.argmin_cons]
    cases picked : (entries answers loss menu).argmin (score answers loss) with
    | none => rfl
    | some candidate =>
      have chosen : candidate ∈ (entries answers loss menu).argmin (score answers loss) := by
        rw [picked]
        simp
      have listed := (mem_entries answers loss menu candidate).mp (List.argmin_mem chosen)
      have noBetter : ¬ score answers loss candidate < score answers loss (retain answers loss) :=
        not_lt_of_ge (unimproved candidate.val listed candidate.property)
      simp [noBetter]
  have same : winningCandidate answers loss menu = retain answers loss :=
    Option.some.inj ((Option.some_get (minimum_exists answers loss menu)).trans kept)
  change (winningCandidate answers loss menu).val = []
  rw [same]
  rfl

namespace MenuChoice

variable {answers loss menu} (choice : MenuChoice answers loss menu)

/-- Consume the selected word from the original publication and return the
same ledger successor used to compute its score. -/
def state : State seed community (history loss ++ choice.word) :=
  reached answers loss choice.word

def minimum : ℚ := (balance answers loss choice.word).remaining

def outcome : Paid (.live (balance answers loss choice.word)) ⊕ Obstruction (.live (balance answers loss choice.word)) :=
  inspect answers loss choice.word

theorem state_has_original_authority : SourceAuthority (endAt seed (history loss)) choice.word :=
  an_eligible_word_has_original_source_authority community answers _ _ _ choice.eligible

theorem chosen_has_no_new_losses :
    choice.state.stack.balances.map Prod.fst = originalLosses seed community (history loss) :=
  (reached_origins answers loss choice.word).trans
    (eligible_preserves_the_literal_original_loss_inventory community answers _ _ _ choice.eligible)

theorem chosen_keeps_the_original_row_on_its_recorded_successor :
    Quantities.Recorded seed (history loss ++ choice.word) ∧
      ∃ row, choice.state.read row = .inr (loss, balance answers loss choice.word) :=
  ⟨reached_records_the_whole_history loss choice.word, reached_reads_exact_origin answers loss choice.word⟩

theorem minimum_zero_iff_eligible_word_clears :
    choice.minimum = 0 ↔
      ∃ word : Word, (word = [] ∨ word ∈ menu) ∧ Eligible answers loss word ∧
        (balance answers loss word).remaining = 0 := by
  constructor
  · intro zero
    exact ⟨choice.word, choice.registered, choice.eligible, zero⟩
  · rintro ⟨word, listed, eligible, zero⟩
    exact le_antisymm ((choice.least word listed eligible).trans_eq zero)
      (balance answers loss choice.word).nonnegative

theorem minimum_positive_iff_every_eligible_word_is_still_due :
    0 < choice.minimum ↔ ∀ word : Word, (word = [] ∨ word ∈ menu) → Eligible answers loss word →
      0 < (balance answers loss word).remaining :=
  ⟨fun positive word listed eligible => positive.trans_le (choice.least word listed eligible),
    fun every => every choice.word choice.registered choice.eligible⟩

theorem positive_minimum_names_the_exact_original_shortfall
    (positive : 0 < choice.minimum) :
    (loss.key.1, loss.key.2.2, choice.minimum) = residual answers loss choice.word ∧
      0 < choice.minimum ∧ choice.minimum ≤ loss.quantity ∧
      ∃ row, choice.state.read row = .inr (loss, balance answers loss choice.word) :=
  ⟨rfl, positive, the_original_loss_bounds_every_later_balance answers loss choice.word,
    reached_reads_exact_origin answers loss choice.word⟩

end MenuChoice

#print axioms choose
#print axioms retain_wins_when_no_eligible_offer_improves
#print axioms MenuChoice.minimum_zero_iff_eligible_word_clears
#print axioms MenuChoice.positive_minimum_names_the_exact_original_shortfall

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Occurrence
