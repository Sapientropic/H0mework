import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Step

set_option autoImplicit false
set_option Elab.async false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations

open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations

noncomputable section
universe u
variable {S : Type u} {V X : S → Type u} [∀ s, AddCommGroup (V s)]
variable {s : S} {environment : Env V X}
variable {op : V s →+ V s} {body : Expr V X s} {total input : V s}
variable {parent : Trace environment (.linear op body) (.const total)}
variable {child : Trace environment body (.const input)}

local notation "Word" => Formal ℤ V X s

/-- A paid linear context writes the child's syntax at the same integer relation coordinates. -/
def linearWord (op : V s →+ V s) : Word →ₗ[ℤ] Word :=
  Finsupp.lmapDomain ℤ ℤ (Expr.linear op)

/-- In a linear parent the original children occupy a prefix, followed by the parent's actual action. -/
theorem linear_words (actual : Trace.LinearInterleaving op parent child) :
    words parent = (words child).map (linearWord op) ++
      [Finsupp.single (.linear op (.const input)) 1 - Finsupp.single (.const total) 1] := by
  induction actual with
  | last value => rfl
  | @step first middle total input paid parent child rest previous =>
      change (Finsupp.single (.linear op first) 1 - Finsupp.single (.linear op middle) 1) ::
          words parent =
        (linearWord op (Finsupp.single first 1 - Finsupp.single middle 1)) ::
          ((words child).map (linearWord op) ++ [_])
      rw [previous, map_sub]
      simp only [linearWord, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem linear_count_le (actual : Trace.LinearInterleaving op parent child) :
    (words child).length ≤ (words parent).length := by
  rw [linear_words actual, List.length_append, List.length_map]
  exact Nat.le_add_right _ _

/-- Read a relation word at the same exact child address in the original parent. -/
theorem linear_word_at (actual : Trace.LinearInterleaving op parent child)
    (i : Fin (words child).length) :
    (words parent).get (Fin.castLE (linear_count_le actual) i) =
      linearWord op ((words child).get i) := by
  have mapped : i.val < ((words child).map (linearWord op)).length := by
    rw [List.length_map]
    exact i.isLt
  rw [List.get_eq_getElem, List.get_eq_getElem]
  change (words parent)[i.val]'(lt_of_lt_of_le i.isLt (linear_count_le actual)) = _
  simp only [linear_words actual, List.getElem_append_left mapped, List.getElem_map]

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationPaidRelations
