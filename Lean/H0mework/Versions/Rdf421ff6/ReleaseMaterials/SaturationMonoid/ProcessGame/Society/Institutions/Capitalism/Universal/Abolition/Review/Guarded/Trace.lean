import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded.Effect
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Trace.Fees

/-! A source occurrence sees paid fees, its selected period, and any actual
refused fee. Rejected candidate simulations supply no birth or debt origin.
The supplied run may be the tail after an already executed original fee. -/

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

def actualWord (paidCount : Nat) : RawEvent Party Good Port Technology Instrument :=
  List.replicate paidCount request ++ match answer with
    | .selected (word := word) .. => word
    | .exhausted .. => []
    | .blocked .. => [request]

def actualExecution {freshStart : RawCurrent Party Good Technology Instrument} {paidCount : Nat}
    (_run : PaidMicroRun input.law request freshStart answer.current paidCount) :=
  input.law.execute freshStart 0 (answer.actualWord paidCount)

theorem actual_requests_exact {freshStart : RawCurrent Party Good Technology Instrument} {paidCount : Nat}
    (run : PaidMicroRun input.law request freshStart answer.current paidCount) :
    (answer.actualExecution run).items.map ExecutionItem.request = answer.actualWord paidCount :=
  input.law.inventory_requests_exact freshStart 0 _

theorem actual_trace_has_exact_material_endpoint
    {freshStart : RawCurrent Party Good Technology Instrument} {paidCount : Nat}
    (run : PaidMicroRun input.law request freshStart answer.current paidCount) :
    (answer.actualExecution run).final.stock = answer.effect.stock ∧
      (answer.actualExecution run).final.claims = answer.effect.claims ∧
      (answer.actualExecution run).final.technology = answer.effect.technology := by
  cases answer with
  | selected prior payment checked generated =>
      simp only [actualExecution, actualWord, effect, input.law.execute_append]
      rw [run.execution_is_the_original_fee_word 0]
      simp only [current]
      rw [execution_final_independent_of_index input.law payment.microNext _ _ 0]
      exact ⟨rfl, rfl, rfl⟩
  | exhausted prior =>
      simp only [actualExecution, actualWord, effect, List.append_nil]
      rw [run.execution_is_the_original_fee_word 0]
      exact ⟨rfl, rfl, rfl⟩
  | blocked prior obstruction generated =>
      simp only [actualExecution, actualWord, effect, input.law.execute_append]
      rw [run.execution_is_the_original_fee_word 0]
      simp only [current, RawLaw.execute, obstruction.actual_source_preserves_current]
      simp

theorem actual_trace_does_not_invent_a_period
    {freshStart : RawCurrent Party Good Technology Instrument} {paidCount : Nat}
    (run : PaidMicroRun input.law request freshStart answer.current paidCount) :
    (answer.actualExecution run).final.clock = freshStart.clock ∧
      (answer.actualExecution run).final.round = freshStart.round :=
  execution_preserves_period input.law freshStart _ 0

/-- This trace cannot turn a simulated candidate into an actual request. -/
theorem actual_request_is_fee_or_selected (paidCount : Nat)
    (item : Request Party Good Port Technology Instrument)
    (present : item ∈ answer.actualWord paidCount) :
    item = request ∨ item ∈ answer.selectedWord.getD [] := by
  cases answer with
  | selected prior payment checked generated =>
      simp only [actualWord, List.mem_append, List.mem_replicate, selectedWord, Option.getD_some] at present ⊢
      rcases present with feeMember | selectedMember
      · exact Or.inl feeMember.2
      · exact Or.inr selectedMember
  | exhausted prior =>
      simp only [actualWord, List.append_nil, List.mem_replicate] at present
      exact Or.inl present.2
  | blocked prior obstruction generated =>
      simp only [actualWord, List.mem_append, List.mem_replicate, List.mem_singleton] at present
      rcases present with feeMember | refused
      · exact Or.inl feeMember.2
      · exact Or.inl refused

#print axioms actual_trace_has_exact_material_endpoint
#print axioms actual_request_is_fee_or_selected

end CompletedAt

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Review.Guarded
