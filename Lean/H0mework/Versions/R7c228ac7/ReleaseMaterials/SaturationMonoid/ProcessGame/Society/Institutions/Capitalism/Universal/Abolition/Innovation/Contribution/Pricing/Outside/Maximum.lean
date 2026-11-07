import Mathlib.Algebra.Order.Field.Rat

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside

variable {α : Type} (score : α → ℚ)

inductive Maximum (values : List α) : Type
  | empty (none : values = [])
  | attained (item : α) (original : item ∈ values)
      (dominates : ∀ other ∈ values, score other ≤ score item)

def maximum : (values : List α) → Maximum score values
  | [] => .empty rfl
  | head :: tail =>
      match maximum tail with
      | .empty empty => .attained head List.mem_cons_self (by
          intro other inside
          rcases List.mem_cons.mp inside with same | later
          · subst other; exact le_refl _
          · rw [empty] at later; exact (List.not_mem_nil later).elim)
      | .attained best original dominates =>
          if later : score head ≤ score best then
            .attained best (List.mem_cons_of_mem _ original) (by
              intro other inside
              rcases List.mem_cons.mp inside with same | rest
              · simpa only [same] using later
              · exact dominates other rest)
          else .attained head List.mem_cons_self (by
            intro other inside
            rcases List.mem_cons.mp inside with same | rest
            · subst other; exact le_refl _
            · exact (dominates other rest).trans (le_of_lt (lt_of_not_ge later)))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Outside
