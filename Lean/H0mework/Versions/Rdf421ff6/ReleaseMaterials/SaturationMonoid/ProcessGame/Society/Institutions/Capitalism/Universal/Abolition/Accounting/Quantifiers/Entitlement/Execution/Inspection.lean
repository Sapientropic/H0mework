import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution.Plan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)

private theorem final_index_independent (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) (left right : Nat) :
    (law.execute before left word).final = (law.execute before right word).final := by
  induction word generalizing before left right with
  | nil => rfl
  | cons request rest inherited => exact inherited (law.step before request) (left + 1) (right + 1)

theorem a_truncated_source_keeps_its_original_first_failure
    (before : RawCurrent Party Good Technology Instrument) (word : RawEvent Party Good Port Technology Instrument)
    (incomplete : payable law before word ≠ word) :
    ∃ request rest, word = payable law before word ++ request :: rest ∧
      ¬ law.Valid (law.execute before 0 (payable law before word)).final request := by
  induction word generalizing before with
  | nil => exact (incomplete rfl).elim
  | cons request rest inherited =>
      by_cases accepted : law.Valid before request
      · have notRest : payable law (law.step before request) rest ≠ rest := by
          intro same
          exact incomplete (by rw [payable,if_pos accepted,same])
        obtain ⟨failed,suffix,original,denied⟩ := inherited (law.step before request) notRest
        refine ⟨failed,suffix,?_,?_⟩
        · simpa only [payable,if_pos accepted,List.cons_append] using congrArg (List.cons request) original
        · simpa only [payable,if_pos accepted,RawLaw.execute,
            final_index_independent law (law.step before request) _ 1 0] using denied
      · exact ⟨request,rest,by rw [payable,if_neg accepted]; rfl,by simpa only [payable,if_neg accepted,RawLaw.execute] using accepted⟩

inductive InspectionAt (before : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) : Type
  | complete (whole : payable law before word = word)
  | blocked (request : Request Party Good Port Technology Instrument)
      (rest : RawEvent Party Good Port Technology Instrument)
      (original : word = payable law before word ++ request :: rest)
      (denied : ¬ law.Valid (law.execute before 0 (payable law before word)).final request)

def inspectWord (before : RawCurrent Party Good Technology Instrument) :
    (word : RawEvent Party Good Port Technology Instrument) → InspectionAt law before word
  | [] => .complete rfl
  | request :: rest =>
      if accepted : law.Valid before request then
        match inspectWord (law.step before request) rest with
        | .complete whole => .complete (by rw [payable,if_pos accepted,whole])
        | .blocked failed suffix original denied =>
            .blocked failed suffix
              (by simpa only [payable,if_pos accepted,List.cons_append] using congrArg (List.cons request) original)
              (by simpa only [payable,if_pos accepted,RawLaw.execute,
                final_index_independent law (law.step before request) _ 1 0] using denied)
      else .blocked request rest (by rw [payable,if_neg accepted]; rfl)
        (by simpa only [payable,if_neg accepted,RawLaw.execute] using accepted)

noncomputable section

variable [DecidableEq Port]
  {window : Entitlement.Source.Window (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} (claim : Entitlement.Source.Claim window)

abbrev Inspection := InspectionAt (Execution.law (window := window)) (Execution.before (window := window)) (candidate claim)

def inspect : Inspection claim :=
  inspectWord (Execution.law (window := window)) (Execution.before (window := window)) (candidate claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Entitlement.Execution
