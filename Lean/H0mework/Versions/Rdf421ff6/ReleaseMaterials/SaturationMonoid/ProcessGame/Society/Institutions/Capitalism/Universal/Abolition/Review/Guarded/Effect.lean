import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Completion

/-! The review result determines the source operation. A selected period
executes once; a typed obstruction retains the paid-review current and its
old debts. The root must use this operation as its native write. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : Root.ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin : RawCurrent Party Good Technology Instrument}
  {request : Request Party Good Port Technology Instrument} {fee : FeeScope request}
  {members : List Party} {start : RawCurrent Party Good Technology Instrument}
  {candidates : List (RawEvent Party Good Port Technology Instrument)}

namespace CompletedAt

variable (answer : CompletedAt input origin request fee members start candidates)

def selectedWord : Option (RawEvent Party Good Port Technology Instrument) :=
  match answer with
  | .selected (word := word) _ _ _ _ => some word
  | .exhausted .. | .blocked .. => none

def effect : RawCurrent Party Good Technology Instrument :=
  match answer with
  | .selected (word := word) _ payment _ _ => input.law.next payment.microNext word
  | .exhausted (current := state) _ => state
  | .blocked (current := state) _ _ _ => state

theorem selected_effect_is_the_actual_period
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : answer.selectedWord = some word) :
    answer.effect = input.law.next answer.current word ∧
      Checks input origin answer.current members word := by
  cases answer with
  | selected prior payment checked generated =>
      simp only [selectedWord, Option.some.injEq] at selected
      subst word
      exact ⟨rfl, checked⟩
  | exhausted prior => cases selected
  | blocked prior obstruction generated => cases selected

theorem rejected_effect_retains_review_current
    (rejected : answer.selectedWord = none) : answer.effect = answer.current := by
  cases answer with
  | selected prior payment checked generated => cases rejected
  | exhausted prior => rfl
  | blocked prior obstruction generated => rfl

theorem effect_preserves_original_claims : answer.effect.claims = start.claims := by
  cases answer with
  | selected prior payment checked generated =>
      exact (checked.1.next_claims input.law payment.microNext _).trans
        (payment.micro_claims_unchanged fee |>.trans (prior.payments.original_claims_unchanged fee))
  | exhausted prior => exact prior.payments.original_claims_unchanged fee
  | blocked prior obstruction generated => exact prior.payments.original_claims_unchanged fee

theorem selected_effect_pays_original_needs
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : answer.selectedWord = some word) :
    Material.OriginalNeedFloor input origin answer.current members word ∧
      Exit.Necessity.AllNeedsPaid input.law answer.current members word ∧
      Material.NoFreshControl input answer.current word := by
  have checked := (answer.selected_effect_is_the_actual_period word selected).2
  exact ⟨checked.2.1, checked.2.2.2.1, checked.2.2.2.2.1⟩

theorem selected_effect_advances_one_period
    (word : RawEvent Party Good Port Technology Instrument)
    (selected : answer.selectedWord = some word) :
    answer.effect.clock = start.clock + max 0 (input.law.duration answer.current) ∧
      answer.effect.round = start.round + 1 := by
  rw [(answer.selected_effect_is_the_actual_period word selected).1]
  change answer.current.clock + _ = _ ∧ answer.current.round + 1 = _
  rw [answer.preserves_period.1, answer.preserves_period.2]
  exact ⟨rfl, rfl⟩

#print axioms effect_preserves_original_claims
#print axioms selected_effect_pays_original_needs
#print axioms selected_effect_advances_one_period

end CompletedAt

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded
