import H0mework.Realization.Operations.Tree.Fold.Source

/-! The original typed programme retains every source root and child.
This parser recovers the complete tree from that generated syntax; it
makes no authority claim about an arbitrary parsed expression. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Inverse
open SourceOperationEffects SourceOperationExecution
variable {Root Carrier : Type u}
def readOrigin : Expr (Value Root Carrier) (Var Root) .origin → Option Root
  | .var root => some root
  | _ => none
mutual
 def readTree : Expr (Value Root Carrier) (Var Root) .result → Option (RootedAccountedUnfolding Root)
  | .bilinear (s:=leftSort) (t:=rightSort) _ left right =>
      match leftSort, rightSort with
      | .origin, .children => do
          let origin ← readOrigin left
          let branches ← readChildren right
          pure (.occur origin branches)
      | _, _ => none
  | _ => none
 def readChildren : Expr (Value Root Carrier) (Var Root) .children → Option (AccountedBranches Root)
  | .const _ => some .nil
  | .bilinear (s:=leftSort) (t:=rightSort) _ left right =>
      match leftSort, rightSort with
      | .result, .children => do
          let head ← readTree left
          let tail ← readChildren right
          pure (.cons head tail)
      | _, _ => none
  | _ => none
end
variable (atOccurrence : Root → List Carrier → Carrier)
mutual
 theorem read_program (tree : RootedAccountedUnfolding Root) : readTree (program atOccurrence tree) = some tree := by
  cases tree with
  | occur origin branches =>
    simp only [program, readTree, readOrigin, read_children]
    rfl
 theorem read_children (branches : AccountedBranches Root) :
     readChildren (children atOccurrence branches) = some branches := by
  cases branches with
  | nil => simp only [children, readChildren]
  | cons head tail =>
    simp only [children, readChildren, read_program, read_children]
    rfl
end
theorem program_injective : Function.Injective (program atOccurrence) := by
  intro left right same
  have reflected := congrArg readTree same
  rw [read_program, read_program] at reflected
  exact Option.some.inj reflected

end SourceOperationNative.Tree.Fold.Inverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
