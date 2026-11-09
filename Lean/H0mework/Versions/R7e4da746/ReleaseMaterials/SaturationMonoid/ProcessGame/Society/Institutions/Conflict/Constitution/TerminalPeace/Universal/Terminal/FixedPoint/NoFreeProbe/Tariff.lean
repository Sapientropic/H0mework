import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Cost

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Source

variable {Party Good Port Technology Instrument : Type}

/-- The source sets the filing debit and the assessment and opportunity
debits of each proposed instruction. The submission supplies only the word. -/
structure Tariff (Party Good Port Technology Instrument : Type) [DecidableEq Good] where
  port : Port
  filing : Bundle Good
  review : Request Party Good Port Technology Instrument → Bundle Good
  opportunity : Request Party Good Port Technology Instrument → Bundle Good
  filingNonnegative : NonnegativeBundle Good filing
  reviewNonnegative : ∀ request, NonnegativeBundle Good (review request)
  opportunityNonnegative : ∀ request, NonnegativeBundle Good (opportunity request)
  filingPositive : ∃ good, 0 < amount Good filing good

namespace Tariff

variable [DecidableEq Good]
  (tariff : Tariff Party Good Port Technology Instrument)

local notation "Word" => RawEvent Party Good Port Technology Instrument

def parts (word : Word) : ChargeParts Good :=
  ⟨tariff.filing, word.flatMap tariff.review, word.flatMap tariff.opportunity⟩

omit [DecidableEq Good] in
private theorem nonnegative_flatMap {α : Type} (inputs : List α) (quote : α → Bundle Good)
    (nonnegative : ∀ input, NonnegativeBundle Good (quote input)) :
    NonnegativeBundle Good (inputs.flatMap quote) := by
  intro lot listed
  obtain ⟨input, _, paid⟩ := List.mem_flatMap.mp listed
  exact nonnegative input lot paid

theorem parts_nonnegative (word : Word) :
    NonnegativeBundle Good (tariff.parts word).bundle := by
  intro lot listed
  simp only [parts, ChargeParts.bundle, List.mem_append] at listed
  rcases listed with (filing | review) | opportunity
  · exact tariff.filingNonnegative lot filing
  · exact nonnegative_flatMap word tariff.review tariff.reviewNonnegative lot review
  · exact nonnegative_flatMap word tariff.opportunity tariff.opportunityNonnegative lot opportunity

theorem amount_nonnegative (word : Word) (good : Good) :
    0 ≤ amount Good (tariff.parts word).bundle good :=
  Program.amount_nonnegative _ (tariff.parts_nonnegative word) good

theorem filing_le_full (word : Word) (good : Good) :
    amount Good tariff.filing good ≤ amount Good (tariff.parts word).bundle good := by
  rw [ChargeParts.amount_bundle]
  exact (le_add_of_nonneg_right
    (Program.amount_nonnegative _ (nonnegative_flatMap word tariff.review tariff.reviewNonnegative) good)).trans
    (le_add_of_nonneg_right
      (Program.amount_nonnegative _ (nonnegative_flatMap word tariff.opportunity tariff.opportunityNonnegative) good))

theorem positive (word : Word) : ∃ good, 0 < amount Good (tariff.parts word).bundle good := by
  obtain ⟨good, positive⟩ := tariff.filingPositive
  exact ⟨good, positive.trans_le (tariff.filing_le_full word good)⟩

private theorem amount_append (left right : Bundle Good) (good : Good) :
    amount Good (left ++ right) good = amount Good left good + amount Good right good := by
  simp [amount, List.sum_append]

theorem append_amount (first second : Word) (good : Good) :
    amount Good (tariff.parts first).bundle good + amount Good (tariff.parts second).bundle good =
      amount Good (tariff.parts (first ++ second)).bundle good + amount Good tariff.filing good := by
  simp only [ChargeParts.amount_bundle, parts, List.flatMap_append, amount_append]
  ring

/-- Each fragment retains its own filing debit. Assessment and opportunity
debits are charged once per instruction in the concatenated proposal. -/
theorem split_amount (pieces : List Word) (good : Good) :
    (pieces.map (fun word => amount Good (tariff.parts word).bundle good)).sum +
        amount Good tariff.filing good =
      amount Good (tariff.parts pieces.flatten).bundle good +
        (pieces.length : ℚ) * amount Good tariff.filing good := by
  induction pieces with
  | nil => simp [parts, ChargeParts.bundle, amount]
  | cons first later ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.length_cons, Nat.cast_succ]
    rw [add_assoc, ih, ← add_assoc, tariff.append_amount]
    ring

theorem split_cannot_discount (pieces : List Word) (nonempty : pieces ≠ []) (good : Good) :
    amount Good (tariff.parts pieces.flatten).bundle good ≤
      (pieces.map (fun word => amount Good (tariff.parts word).bundle good)).sum := by
  have filing := Program.amount_nonnegative _ tariff.filingNonnegative good
  have count : (1 : ℚ) ≤ (pieces.length : ℚ) := by
    exact_mod_cast List.length_pos_of_ne_nil nonempty
  have charged := mul_le_mul_of_nonneg_right count filing
  rw [one_mul] at charged
  linarith only [tariff.split_amount pieces good, charged]

theorem split_strictly_increases_some_amount (pieces : List Word) (several : 1 < pieces.length) :
    ∃ good, amount Good (tariff.parts pieces.flatten).bundle good <
      (pieces.map (fun word => amount Good (tariff.parts word).bundle good)).sum := by
  obtain ⟨good, positive⟩ := tariff.filingPositive
  refine ⟨good, ?_⟩
  have count : (1 : ℚ) < (pieces.length : ℚ) := by exact_mod_cast several
  have extra := mul_lt_mul_of_pos_right count positive
  rw [one_mul] at extra
  linarith only [tariff.split_amount pieces good, extra]

end Tariff

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe
