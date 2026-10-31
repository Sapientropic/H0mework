set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material

universe u

/-- A finite scan returns the actual failing member, not an existential
chosen from a negated successful result. -/
inductive ListInspection {α : Type u} (predicate : α → Prop) (items : List α) : Type u
  | clear (checked : ∀ item ∈ items, predicate item)
  | failure (item : α) (original : item ∈ items) (failed : ¬ predicate item)

def inspectList {α : Type u} (predicate : α → Prop) [DecidablePred predicate] :
    (items : List α) → ListInspection predicate items
  | [] => .clear (by simp)
  | item :: tail =>
      if checked : predicate item then
        match inspectList predicate tail with
        | .clear rest => .clear (by
            intro value present
            rcases List.mem_cons.mp present with same | later
            · exact same ▸ checked
            · exact rest value later)
        | .failure value present failed => .failure value (List.mem_cons_of_mem _ present) failed
      else .failure item List.mem_cons_self checked

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material
