import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)
  (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
  (members : List Party)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
def CompulsoryTake (operation : Operation Party Good Technology Instrument) : Prop :=
  match operation with
  | .transfer .. | .produce _ | .revise .. => True
  | _ => False

theorem paid_remains_paid_under_every_actual_word
    (paid : Responsibility.Family.State.isPaid claim state)
    (word : RawEvent Party Good Port Technology Instrument) :
    Responsibility.Family.State.isPaid claim (Responsibility.Family.State.advance claim state law word) := by
  intro key member
  exact le_antisymm (by simpa only [paid key member] using
    Responsibility.Family.State.actual_advance_never_refills_any_original_cell claim state law word key)
    ((Responsibility.Family.State.advance claim state law word).nonnegative key)

theorem a_paid_original_row_has_no_new_compulsory_permission
    (paid : Responsibility.Family.State.isPaid claim state)
    (front : RawEvent Party Good Port Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (take : CompulsoryTake request.operation) :
    ¬ amountAllowed claim state law members front request := by
  have unchanged := paid_remains_paid_under_every_actual_word claim state law paid front
  cases operation : request.operation <;> simp_all [CompulsoryTake,amountAllowed,beforeState]

theorem the_source_gate_denies_a_paid_rows_next_compulsory_request
    (paid : Responsibility.Family.State.isPaid claim state)
    (request : Request Party Good Port Technology Instrument) (take : CompulsoryTake request.operation) :
    ∃ issue, decideRequest claim state law members [] request = .denied issue := by
  cases generated : decideRequest claim state law members [] request with
  | denied issue => exact ⟨issue,rfl⟩
  | permitted declared standing material valid amount control =>
    exact (a_paid_original_row_has_no_new_compulsory_permission claim state law members paid [] request take amount).elim

theorem accepted_paid_prefix_has_no_new_compulsory_request
    (paid : Responsibility.Family.State.isPaid claim state)
    {word : RawEvent Party Good Port Technology Instrument}
    (accepted : AcceptedPrefix claim state law members word) :
    ∀ request ∈ word, ¬ CompulsoryTake request.operation := by
  induction accepted with
  | nil => simp
  | snoc front request earlier declared standing material valid amount control inherited =>
    intro next member compulsory
    rcases List.mem_append.mp member with old | last
    · exact inherited next old compulsory
    · have same : next = request := List.mem_singleton.mp last
      subst next
      exact a_paid_original_row_has_no_new_compulsory_permission claim state law members paid front request compulsory amount

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
def FinancialOperation (operation : Operation Party Good Technology Instrument) : Prop :=
  match operation with
  | .issue .. | .assign .. | .settle .. => True
  | _ => False

theorem accepted_prefix_has_no_financial_operation
    {word : RawEvent Party Good Port Technology Instrument}
    (accepted : AcceptedPrefix claim state law members word) :
    ∀ request ∈ word, ¬ FinancialOperation request.operation := by
  induction accepted with
  | nil => simp
  | snoc front request earlier declared standing material valid amount control inherited =>
    intro next member financial
    rcases List.mem_append.mp member with old | last
    · exact inherited next old financial
    · have same : next = request := List.mem_singleton.mp last
      subst next
      cases operation : request.operation <;> simp_all [FinancialOperation,Responsibility.Family.materialOperation]

private theorem empty_word_from_excluded_head
    (request : Request Party Good Port Technology Instrument) (tail : RawEvent Party Good Port Technology Instrument)
    (excluded : ∀ next ∈ (evaluate claim state law members (request :: tail)).executableWord,
      next ≠ request) : (evaluate claim state law members (request :: tail)).executableWord = [] := by
  let evaluation := evaluate claim state law members (request :: tail)
  cases actual : evaluation.executableWord with
  | nil => rfl
  | cons head rest =>
    have original := evaluation.original
    rw [actual] at original
    have same : request = head := (List.cons.inj original).1
    have inside : head ∈ evaluation.executableWord := by rw [actual]; exact List.mem_cons_self
    exact (excluded head inside same.symm).elim

private theorem empty_prefix_has_a_typed_stop
    (request : Request Party Good Port Technology Instrument) (tail : RawEvent Party Good Port Technology Instrument)
    (empty : (evaluate claim state law members (request :: tail)).executableWord = []) :
    (evaluate claim state law members (request :: tail)).stop.isSome = true := by
  let evaluation := evaluate claim state law members (request :: tail)
  cases stopped : evaluation.stop with
  | some issue => rfl
  | none =>
    have rest := evaluation.complete_when_noStop stopped
    have original := evaluation.original
    rw [empty,rest] at original
    simp only [List.nil_append] at original
    cases original

theorem paid_row_compulsory_head_is_rejected_before_execution
    (paid : Responsibility.Family.State.isPaid claim state)
    (request : Request Party Good Port Technology Instrument) (tail : RawEvent Party Good Port Technology Instrument)
    (compulsory : CompulsoryTake request.operation) :
    (evaluate claim state law members (request :: tail)).executableWord = [] ∧
      (evaluate claim state law members (request :: tail)).stop.isSome = true := by
  have empty := empty_word_from_excluded_head claim state law members request tail (by
    intro next member same
    subst next
    exact accepted_paid_prefix_has_no_new_compulsory_request claim state law members paid
      (evaluate claim state law members (request :: tail)).accepted request member compulsory)
  exact ⟨empty,empty_prefix_has_a_typed_stop claim state law members request tail empty⟩

theorem financial_head_is_rejected_before_execution
    (request : Request Party Good Port Technology Instrument) (tail : RawEvent Party Good Port Technology Instrument)
    (financial : FinancialOperation request.operation) :
    (evaluate claim state law members (request :: tail)).executableWord = [] ∧
      (evaluate claim state law members (request :: tail)).stop.isSome = true := by
  have empty := empty_word_from_excluded_head claim state law members request tail (by
    intro next member same
    subst next
    exact accepted_prefix_has_no_financial_operation claim state law members
      (evaluate claim state law members (request :: tail)).accepted request member financial)
  exact ⟨empty,empty_prefix_has_a_typed_stop claim state law members request tail empty⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy
