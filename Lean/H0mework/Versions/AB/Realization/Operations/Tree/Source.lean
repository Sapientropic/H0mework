import H0mework.Versions.R2.Arithmetic.UnitArithmetic.Root
import H0mework.Realization.Operations.Execution.Run

/-! The full unit-history source tree generates constructor syntax. Each
child unit is visited; neither a target nor a fold equation enters the compiler. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree
open ArithmeticGeneration CanonicalUnitArithmeticRoot
open SourceOperationEffects SourceOperationExecution

abbrev Value := SourceNativeBinary.Value UnitHistory UnitHistory UnitHistory
abbrev Var := SourceNativeBinary.Var UnitHistory UnitHistory UnitHistory
abbrev Program := Expr Value Var .result
abbrev environment := SourceNativeBinary.environment (X := UnitHistory) (Y := UnitHistory) (Z := UnitHistory)
def appendConstructor : (UnitHistory →₀ ℤ) →+ (UnitHistory →₀ ℤ) :=
  (Finsupp.lmapDomain ℤ ℤ UnitHistory.next).toAddMonoidHom

def appendUnits (input : Program) : UnitHistory → Program
  | .empty => input
  | .next previous => .linear appendConstructor (appendUnits input previous)

private theorem parallel_assoc (left middle right : UnitHistory) :
    (left.parallel middle).parallel right = left.parallel (middle.parallel right) := by
  induction right with
  | empty => rfl
  | next right ih => exact congrArg UnitHistory.next ih

private theorem foldl_parallel (prior origin : UnitHistory) (values : List UnitHistory) :
    values.foldl UnitHistory.parallel (prior.parallel origin) =
      prior.parallel (values.foldl UnitHistory.parallel origin) := by
  induction values generalizing origin with
  | nil => rfl
  | cons head tail ih =>
    change tail.foldl UnitHistory.parallel ((prior.parallel origin).parallel head) =
      prior.parallel (tail.foldl UnitHistory.parallel (origin.parallel head))
    rw [parallel_assoc, ih]

private theorem append_units_eval (input : Program) (origin right : UnitHistory)
    (source_basis : input.eval environment = Finsupp.single origin 1) :
    (appendUnits input right).eval environment = Finsupp.single (origin.parallel right) 1 := by
  induction right with
  | empty => exact source_basis
  | next right ih =>
    change appendConstructor ((appendUnits input right).eval environment) =
      Finsupp.single (UnitHistory.next (origin.parallel right)) 1
    rw [ih]
    simp only [appendConstructor, LinearMap.toAddMonoidHom_coe, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

mutual
  def appendTree (input : Program) : RootedAccountedUnfolding UnitHistory → Program
    | .occur origin branches => appendBranches (appendUnits input origin) branches
  def appendBranches (input : Program) : AccountedBranches UnitHistory → Program
    | .nil => input
    | .cons head tail => appendBranches (appendTree input head) tail
end

mutual
  private theorem tree_eval (tree : RootedAccountedUnfolding UnitHistory)
      (input : Program) (origin : UnitHistory)
      (source_basis : input.eval environment = Finsupp.single origin 1) :
      (appendTree input tree).eval environment = Finsupp.single (origin.parallel (nativeActionTarget tree)) 1 := by
    cases tree with
    | occur root branches =>
      have generated := branches_eval branches (appendUnits input root) (origin.parallel root)
        (append_units_eval input origin root source_basis)
      exact generated.trans (congrArg (fun value => Finsupp.single value (1 : ℤ))
        (foldl_parallel origin root (RootedAccountedUnfolding.foldBranches nativeActionAlgebra branches)))
  private theorem branches_eval (branches : AccountedBranches UnitHistory)
      (input : Program) (origin : UnitHistory)
      (source_basis : input.eval environment = Finsupp.single origin 1) :
      (appendBranches input branches).eval environment =
        Finsupp.single ((RootedAccountedUnfolding.foldBranches nativeActionAlgebra branches).foldl
          UnitHistory.parallel origin) 1 := by
    cases branches with
    | nil => exact source_basis
    | cons head tail =>
      exact branches_eval tail (appendTree input head) (origin.parallel (nativeActionTarget head))
        (tree_eval head input origin source_basis)
end

def program : RootedAccountedUnfolding UnitHistory → Program
  | .occur origin branches => appendBranches (.var origin) branches

mutual
  def unitWork : RootedAccountedUnfolding UnitHistory → Nat
    | .occur origin branches => origin.cardinalShadow + branchWork branches
  def branchWork : AccountedBranches UnitHistory → Nat
    | .nil => 0
    | .cons head tail => unitWork head + branchWork tail
end

/-- The original root is bound once. Child histories contribute their actual
constructor work rather than one opaque binary/fold call. -/
def budget : RootedAccountedUnfolding UnitHistory → Nat
  | .occur _ branches => 1 + branchWork branches

private theorem append_units_work (input : Program) (history : UnitHistory) :
    remaining (appendUnits input history) = remaining input + history.cardinalShadow := by
  induction history with
  | empty => exact (Nat.add_zero _).symm
  | next history ih =>
    change remaining (appendUnits input history) + 1 = remaining input + (history.cardinalShadow + 1)
    rw [ih, Nat.add_assoc]

mutual
  private theorem tree_work (tree : RootedAccountedUnfolding UnitHistory) (input : Program) :
      remaining (appendTree input tree) = remaining input + unitWork tree := by
    cases tree with
    | occur origin branches =>
      change remaining (appendBranches (appendUnits input origin) branches) =
        remaining input + (origin.cardinalShadow + branchWork branches)
      rw [branches_work, append_units_work, Nat.add_assoc]
  private theorem branches_work (branches : AccountedBranches UnitHistory) (input : Program) :
      remaining (appendBranches input branches) = remaining input + branchWork branches := by
    cases branches with
    | nil => exact (Nat.add_zero _).symm
    | cons head tail =>
      change remaining (appendBranches (appendTree input head) tail) =
        remaining input + (unitWork head + branchWork tail)
      rw [branches_work, tree_work, Nat.add_assoc]
end

theorem program_budget (tree : RootedAccountedUnfolding UnitHistory) :
    remaining (program tree) = budget tree := by
  cases tree with
  | occur origin branches => exact branches_work branches (.var origin)

theorem program_source (tree : RootedAccountedUnfolding UnitHistory) :
    (program tree).eval environment = Finsupp.single (nativeActionTarget tree) 1 := by
  cases tree with
  | occur origin branches => exact branches_eval branches (.var origin) origin rfl

def sourceTrace (tree : RootedAccountedUnfolding UnitHistory) :
    Trace environment (program tree) (.const ((program tree).eval environment)) :=
  execution environment (program tree)

theorem trace_charged (tree : RootedAccountedUnfolding UnitHistory) :
    (sourceTrace tree).length = budget tree :=
  (sourceTrace tree).length_to_const.trans (program_budget tree)

end SourceOperationNative.Tree
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
