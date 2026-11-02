import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered
open Source.Program

def NonCode : InputAt → Prop
  | .code _ => False
  | _ => True

private theorem completed_attempt_advances_only_the_original_code_position
    (past : List InputAt) (raw : InputAt) (notCode : NonCode raw) :
    codeProgress (past ++ [raw]) = (codeProgress past).map (fun progress => (progress.1, progress.2 + 1)) := by
  cases raw <;> simp_all only [NonCode, codeProgress, List.reverse_append, List.reverse_singleton,
    List.singleton_append, codeProgressFromReverse]

theorem a_prefix_without_submitted_code_has_no_programme_position
    (past : List InputAt) (original : ∀ raw ∈ past, NonCode raw) : codeProgress past = none := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past raw inherited =>
      rw [completed_attempt_advances_only_the_original_code_position past raw
        (original raw (List.mem_append_right _ (List.mem_singleton_self _))),
        inherited (fun item member => original item (List.mem_append_left _ member))]
      rfl

theorem every_completed_noncode_attempt_spends_its_one_original_position
    (past : List InputAt) (word : RawEvent Party Good Bool Nat Unit) (attempts : List InputAt)
    (original : ∀ raw ∈ attempts, NonCode raw) :
    codeProgress (past ++ [.code ⟨word⟩] ++ attempts) = some (word,attempts.length) := by
  induction attempts using List.reverseRecOn with
  | nil => simp only [List.append_nil, codeProgress, List.reverse_append, List.reverse_singleton,
      List.singleton_append, codeProgressFromReverse, List.length_nil]
  | append_singleton attempts raw inherited =>
      have checked := original raw (List.mem_append_right _ (List.mem_singleton_self _))
      have prior := inherited (fun item member => original item (List.mem_append_left _ member))
      rw [← List.append_assoc, completed_attempt_advances_only_the_original_code_position _ _ checked, prior]
      simp only [Option.map_some, List.length_append, List.length_singleton]

theorem the_finite_submitted_programme_generates_its_exact_next_attempt
    (past : List InputAt) (word : RawEvent Party Good Bool Nat Unit) (attempts : List InputAt)
    (original : ∀ raw ∈ attempts, NonCode raw) :
    afterPreparation (past ++ [.code ⟨word⟩] ++ attempts) =
      ((executionInputs word)[attempts.length]?).getD (.execute Control.Scenario.commonWork) := by
  unfold afterPreparation afterPreparationWith
  rw [every_completed_noncode_attempt_spends_its_one_original_position past word attempts original]

theorem no_prior_risk_liability_is_reissued_after_its_four_actual_attempts
    (past : List InputAt) (signal : Fin quotedMechanism.code.signals)
    (priced : signal = 0 ∨ signal = 1) (attempts : List InputAt)
    (original : ∀ raw ∈ attempts, NonCode raw) (finished : 4 ≤ attempts.length) :
    afterPreparation (past ++ [.code ⟨programme signal⟩] ++ attempts) = .execute Control.Scenario.commonWork := by
  rw [the_finite_submitted_programme_generates_its_exact_next_attempt past _ attempts original]
  have capacity : (executionInputs (programme signal)).length = 4 := by
    rcases priced with rfl | rfl
    · rw [native_risk_begins_before_the_guarded_work_and_primitive_payments.2]
      rfl
    · rw [native_risk_begins_before_the_guarded_work_and_primitive_payments.1]
      rfl
  rw [List.getElem?_eq_none_iff.mpr (show (executionInputs (programme signal)).length ≤ attempts.length by omega)]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
