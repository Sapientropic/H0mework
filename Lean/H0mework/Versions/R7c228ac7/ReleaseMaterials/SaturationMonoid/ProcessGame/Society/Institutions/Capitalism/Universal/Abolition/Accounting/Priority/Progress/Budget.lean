import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Policy.Evaluation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Progress

open Source.Program Innovation

noncomputable section

private theorem filter_length_mono {α : Type} (items : List α) (smaller larger : α → Bool)
    (inherited : ∀ item ∈ items, smaller item = true → larger item = true) :
    (items.filter smaller).length ≤ (items.filter larger).length := by
  induction items with
  | nil => exact le_rfl
  | cons item rest ih =>
    have later := ih (fun next member => inherited next (List.mem_cons_of_mem item member))
    by_cases firstTrue : smaller item = true <;> by_cases secondTrue : larger item = true
    · simpa [List.filter,firstTrue,secondTrue] using Nat.succ_le_succ later
    · exact (secondTrue (inherited item List.mem_cons_self firstTrue)).elim
    · simpa [List.filter,firstTrue,secondTrue] using Nat.le_succ_of_le later
    · simpa [List.filter,firstTrue,secondTrue] using later

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : source.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim source past nature response)

def unpaidCells (state : Responsibility.Family.State claim) : List (Party × Good) :=
  (Responsibility.Family.positiveScope source past nature response).filter fun key => decide (0 < state.remaining key)

def budget (state : Responsibility.Family.State claim) : Nat := (unpaidCells claim state).length

theorem zero_budget_exactly_when_all_original_cells_are_paid (state : Responsibility.Family.State claim) :
    budget claim state = 0 ↔ Responsibility.Family.State.isPaid claim state := by
  constructor
  · intro zero key member
    have empty : unpaidCells claim state = [] := List.length_eq_zero_iff.mp zero
    have nonpositive : ¬ 0 < state.remaining key := by
      intro positive
      have inside : key ∈ unpaidCells claim state := List.mem_filter.mpr ⟨member,decide_eq_true positive⟩
      rw [empty] at inside
      exact List.not_mem_nil inside
    exact le_antisymm (le_of_not_gt nonpositive) (state.nonnegative key)
  · intro paid
    apply List.length_eq_zero_iff.mpr
    apply List.filter_eq_nil_iff.mpr
    intro key member
    simp [paid key member]

theorem every_actual_word_cannot_add_an_unpaid_original_cell
    (state : Responsibility.Family.State claim) (law : RawLaw Party Good Port Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    budget claim (Responsibility.Family.State.advance claim state law word) ≤ budget claim state := by
  apply filter_length_mono
  intro key _ positive
  apply decide_eq_true
  have observed := of_decide_eq_true positive
  exact lt_of_lt_of_le observed
    (Responsibility.Family.State.actual_advance_never_refills_any_original_cell claim state law word key)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Progress
