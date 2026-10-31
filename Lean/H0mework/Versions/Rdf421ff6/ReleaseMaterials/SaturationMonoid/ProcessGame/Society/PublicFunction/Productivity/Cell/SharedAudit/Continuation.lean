import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Effects

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit

open Institutions.Capitalism.Universal.Source.Program

def withLabor (current : Current) (amount : ℚ) : Current :=
  { current with stock := fun actor good => current.stock actor good +
      if actor = 0 ∧ good = .labor then amount else 0 }

theorem extra_labor_keeps_every_legal_request (current : Current) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (request : RequestAt) (valid : law.Valid current request) :
    law.Valid (withLabor current amount) request := by
  refine ⟨valid.1, valid.2.1, ?_, valid.2.2.2.1, valid.2.2.2.2.1, ?_⟩
  · cases request.operation <;> exact valid.2.2.1
  · intro entry inside
    have enough := valid.2.2.2.2.2 entry inside
    change flowAt (law.debit current request) entry.1.1 entry.1.2 ≤
      current.stock entry.1.1 entry.1.2 + (if entry.1.1 = 0 ∧ entry.1.2 = .labor then amount else 0)
    split_ifs <;> linarith

theorem paid_step_transports_the_same_extra_labor (current : Current) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (request : RequestAt) (valid : law.Valid current request) :
    law.step (withLabor current amount) request = withLabor (law.step current request) amount := by
  rw [RawLaw.step, if_pos (extra_labor_keeps_every_legal_request current amount nonnegative request valid)]
  rw [RawLaw.step, if_pos valid]
  apply RawCurrent.ext
  · funext actor good
    change current.stock actor good + _ - flowAt (law.debit current request) actor good +
      flowAt (law.credit current request) actor good =
        current.stock actor good - flowAt (law.debit current request) actor good +
          flowAt (law.credit current request) actor good + _
    ring
  · cases request.operation <;> rfl
  all_goals cases request.operation <;> rfl

/-- Every legal old continuation can be replayed. The full inventory and
claim carrier is transported, not only its service score. -/
theorem every_legal_word_keeps_the_same_extra_labor (current : Current) (amount : ℚ)
    (nonnegative : 0 ≤ amount) (word : List RequestAt) (index : Nat)
    (accepted : ∀ item ∈ (law.execute current index word).items, law.Valid item.before item.request) :
    (∀ item ∈ (law.execute (withLabor current amount) index word).items,
      law.Valid item.before item.request) ∧
      (law.execute (withLabor current amount) index word).final =
        withLabor (law.execute current index word).final amount := by
  induction word generalizing current index with
  | nil => exact ⟨by simp [RawLaw.execute], rfl⟩
  | cons request rest ih =>
    have first := accepted ⟨index, current, request⟩ List.mem_cons_self
    have tail := ih (law.step current request) (index + 1)
      (fun item inside => accepted item (List.mem_cons_of_mem _ inside))
    simp only [RawLaw.execute, paid_step_transports_the_same_extra_labor current amount nonnegative request first]
    exact ⟨fun item inside => by
      simp only [List.mem_cons] at inside
      rcases inside with rfl | later
      · exact extra_labor_keeps_every_legal_request current amount nonnegative request first
      · exact tail.1 item later, tail.2⟩

theorem actual_final_current_is_the_same_carrier_plus_one_labor :
    source.currentAt 11 = withLabor (Cell.source.currentAt 11) 1 := by
  apply RawCurrent.ext
  · funext actor good
    exact complete_inventory_difference actor good
  · exact same_all_financial_positions
  · exact same_technology_and_window.1
  · exact same_technology_and_window.2.1
  · exact same_technology_and_window.2.2

theorem actual_dividend_preserves_every_old_executable_continuation (word : List RequestAt)
    (accepted : ∀ item ∈ law.rawItems (Cell.source.currentAt 11) word, law.Valid item.before item.request) :
    (∀ item ∈ law.rawItems (source.currentAt 11) word, law.Valid item.before item.request) ∧
      (law.execute (source.currentAt 11) 0 word).final =
        withLabor (law.execute (Cell.source.currentAt 11) 0 word).final 1 := by
  rw [actual_final_current_is_the_same_carrier_plus_one_labor]
  exact every_legal_word_keeps_the_same_extra_labor _ 1 (by norm_num) word 0 accepted

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit
