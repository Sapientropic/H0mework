import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Guarantee

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection

inductive FiniteResult {α : Type} (predicate : α → Prop) (items : List α) : Type
  | ready (all : ∀ item ∈ items, predicate item)
  | blocked (item : α) (original : item ∈ items) (failed : ¬ predicate item)

def inspectAll {α : Type} (predicate : α → Prop) [DecidablePred predicate] :
    (items : List α) → FiniteResult predicate items
  | [] => .ready (by simp)
  | item :: rest =>
    if accepted : predicate item then
      match inspectAll predicate rest with
      | .ready later => .ready (by
          intro next member
          rcases List.mem_cons.mp member with same | inside
          · exact same ▸ accepted
          · exact later next inside)
      | .blocked next original failed => .blocked next (List.mem_cons_of_mem _ original) failed
    else .blocked item List.mem_cons_self accepted

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Inspection
