import H0mework.Realization.Operations.BinaryInputs
import H0mework.Realization.Operations.Execution.Run
import H0mework.Realization.Operations.Execution.Relations
import H0mework.Foundation.Source.AccountedUnfolding

/-! The source constructor is compiled at every node of the complete tree.
Children are assembled as actual ordered lists; no candidate, target or
commuting equation is an input. Primitive-internal costs stay external. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold
open SourceOperationEffects SourceOperationExecution
inductive Slot : Type u | origin | result | children deriving DecidableEq
abbrev Value (Root Carrier : Type u) : Slot.{u} → Type u
  | .origin => Root →₀ ℤ
  | .result => Carrier →₀ ℤ
  | .children => List Carrier →₀ ℤ
abbrev Var (Root : Type u) : Slot.{u} → Type u
  | .origin => Root
  | .result => PEmpty.{u+1}
  | .children => PEmpty.{u+1}
instance {Root Carrier : Type u} : (slot : Slot.{u}) → AddCommGroup (Value Root Carrier slot)
  | .origin => inferInstance
  | .result => inferInstance
  | .children => inferInstance
def environment {Root Carrier : Type u} : Env (Value Root Carrier) (Var Root)
  | .origin, root => Finsupp.single root 1
  | .result, name => PEmpty.elim name
  | .children, name => PEmpty.elim name
variable {Root Carrier : Type u}
variable (atOccurrence : Root → List Carrier → Carrier)
mutual
 def program : RootedAccountedUnfolding Root → Expr (Value Root Carrier) (Var Root) .result
  | .occur root branches => .bilinear (s:=.origin) (t:=.children)
      (SourceNativeBinary.lift atOccurrence) (.var root) (children branches)
 def children : AccountedBranches Root → Expr (Value Root Carrier) (Var Root) .children
  | .nil => .const (Finsupp.single [] 1)
  | .cons head tail => .bilinear (s:=.result) (t:=.children)
      (SourceNativeBinary.lift List.cons) (program head) (children tail)
end
mutual
 theorem program_value (tree : RootedAccountedUnfolding Root) :
     (program atOccurrence tree).eval environment = Finsupp.single (tree.fold atOccurrence) 1 := by
  cases tree with
  | occur root branches =>
    change SourceNativeBinary.lift atOccurrence (Finsupp.single root 1)
      ((children atOccurrence branches).eval environment) = _
    rw [children_value]
    exact SourceNativeBinary.lift_point atOccurrence root _
 theorem children_value (branches : AccountedBranches Root) :
     (children atOccurrence branches).eval environment =
       Finsupp.single (RootedAccountedUnfolding.foldBranches atOccurrence branches) 1 := by
  cases branches with
  | nil => rfl
  | cons head tail =>
    change SourceNativeBinary.lift List.cons ((program atOccurrence head).eval environment)
      ((children atOccurrence tail).eval environment) = _
    rw [program_value, children_value]
    exact SourceNativeBinary.lift_point List.cons _ _
end
mutual
 def budget : RootedAccountedUnfolding Root → Nat
  | .occur _ branches => 2 + childrenBudget branches
 def childrenBudget : AccountedBranches Root → Nat
  | .nil => 0
  | .cons head tail => budget head + childrenBudget tail + 1
end
mutual
 theorem program_budget (tree : RootedAccountedUnfolding Root) :
     remaining (program atOccurrence tree) = budget tree := by
  cases tree with
  | occur root branches =>
    change 1 + remaining (children atOccurrence branches) + 1 = 2 + childrenBudget branches
    rw [children_budget]
    omega
 theorem children_budget (branches : AccountedBranches Root) :
     remaining (children atOccurrence branches) = childrenBudget branches := by
  cases branches with
  | nil => rfl
  | cons head tail =>
    change remaining (program atOccurrence head) + remaining (children atOccurrence tail) + 1 = _
    rw [program_budget, children_budget]
    rfl
end
variable (tree : RootedAccountedUnfolding Root)
def sourceTrace := execution environment (program atOccurrence tree)
theorem trace_budget : (sourceTrace atOccurrence tree).length = budget tree :=
  (execution_length environment _).trans (program_budget _ _)

theorem source_boundary : SourceOperationScalarPresentation.relationMap (R := ℤ) environment
    (sourceTrace atOccurrence tree).relationWords =
      Finsupp.single (program atOccurrence tree) 1 -
        Finsupp.single (.const ((program atOccurrence tree).eval environment)) 1 :=
  (sourceTrace atOccurrence tree).relation_boundary

end SourceOperationNative.Tree.Fold
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
