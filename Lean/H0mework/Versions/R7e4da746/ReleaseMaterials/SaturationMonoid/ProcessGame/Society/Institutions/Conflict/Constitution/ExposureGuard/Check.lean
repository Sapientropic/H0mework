import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Footprint

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument
local notation "Q" => Question Party Good Instrument

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (roster : List Party) (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

abbrev originalItems := Boundary.Actual.items (endAt seed past) input

def Authorized : Prop :=
  ∀ (position : Fin (originalItems (seed := seed) past input).length) (question : Q),
    question ∈ questions (endAt seed past) (originalItems (seed := seed) past input)[position] →
    question.1 ∈ roster → answers past input position question.1 = true

structure Denial where
  position : Fin (originalItems (seed := seed) past input).length
  question : Q
  original : question ∈ questions (endAt seed past) (originalItems (seed := seed) past input)[position]
  bearer : question.1 ∈ roster
  refused : answers past input position question.1 = false

theorem Denial.refutes (denied : Denial roster answers past input) :
    ¬ Authorized roster answers past input := by
  intro accepted
  have agrees := accepted denied.position denied.question denied.original denied.bearer
  rw [denied.refused] at agrees
  cases agrees

private def addressed : List (Fin (originalItems (seed := seed) past input).length × Q) :=
  (List.finRange (originalItems (seed := seed) past input).length).flatMap fun position =>
    (questions (endAt seed past) (originalItems (seed := seed) past input)[position]).map (fun question => (position, question))

/-- Read the complete original inventory, including instructions selected
by the native runtime rather than directly proposed by the caller. -/
def inspect : Denial roster answers past input ⊕ PLift (Authorized roster answers past input) :=
  match Capitalism.Universal.Abolition.Material.inspectList
    (fun entry : Fin (originalItems (seed := seed) past input).length × Q =>
      entry.2.1 ∈ roster → answers past input entry.1 entry.2.1 = true) (addressed past input) with
  | .clear checked => .inr ⟨fun position question listed member =>
      checked (position, question)
        (List.mem_flatMap.mpr ⟨position, List.mem_finRange _, List.mem_map_of_mem listed⟩) member⟩
  | .failure entry listed failed => .inl (by
      have asked : entry.2 ∈ questions (endAt seed past) (originalItems (seed := seed) past input)[entry.1] := by
        obtain ⟨position, _, present⟩ := List.mem_flatMap.mp listed
        obtain ⟨question, asked, rfl⟩ := List.mem_map.mp present
        exact asked
      have bearer : entry.2.1 ∈ roster := Classical.byContradiction fun absent => failed (fun member => (absent member).elim)
      exact ⟨entry.1, entry.2, asked, bearer,
        Bool.eq_false_of_not_eq_true (fun yes => failed (fun _ => yes))⟩)

variable (person : Party) (member : person ∈ roster)
  (position : Fin (originalItems (seed := seed) past input).length)

include member

theorem a_withholding_bearer_cannot_be_entered_as_signer
    (accepted : Authorized roster (withhold answers person) past input) :
    (originalItems (seed := seed) past input)[position].request.signer ≠ person := by
  intro forged
  have signed : (originalItems (seed := seed) past input)[position].request.signer ∈ roster := by
    rw [forged]
    exact member
  have answer := accepted position _ (signer_is_asked _ _)
    signed
  change withhold answers person past input position (originalItems (seed := seed) past input)[position].request.signer = true at answer
  rw [forged, withholding_uses_the_original_personal_lane] at answer
  cases answer

theorem a_withholding_bearer_cannot_fund_any_actual_item
    (accepted : Authorized roster (withhold answers person) past input) (good : Good) :
    let item := (originalItems (seed := seed) past input)[position]
    flowAt ((physical (endAt seed past)).actualDebit item.before item.request) person good ≤ 0 := by
  by_contra excess
  have answer := accepted position _
    (a_positive_actual_debit_asks_its_actual_bearer _ _ person good (lt_of_not_ge excess)) member
  change withhold answers person past input position person = true at answer
  rw [withholding_uses_the_original_personal_lane] at answer
  cases answer

theorem a_withholding_bearer_cannot_be_charged_by_any_actual_item
    (accepted : Authorized roster (withhold answers person) past input) (good : Good) :
    netDebit (endAt seed past) (originalItems (seed := seed) past input)[position] person good ≤ 0 :=
  nonpositive_actual_debit_is_nonpositive_net_debit _ _ _ _
    (a_withholding_bearer_cannot_fund_any_actual_item roster answers past input person member position accepted good)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
