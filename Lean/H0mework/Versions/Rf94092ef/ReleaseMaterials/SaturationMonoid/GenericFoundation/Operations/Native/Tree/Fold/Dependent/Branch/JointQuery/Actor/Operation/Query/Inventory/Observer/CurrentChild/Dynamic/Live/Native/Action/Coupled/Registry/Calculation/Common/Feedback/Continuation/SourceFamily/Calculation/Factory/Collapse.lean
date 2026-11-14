import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.Factory.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory

open SourceOperationScalarInventoryLift
attribute [local instance] levelGroups

variable {Sorts : Type u} {W : Sorts → Type u} [∀ target, AddCommGroup (W target)]

private theorem collapse_value_zero (grade : Nat) (target : Sorts) :
    collapseValue (W := W) grade (0 : PairValue (L.Value W grade) target) = 0 := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change collapseValue (W := W) grade
      ((0 : PairValue (L.Value W grade) target)+(0 : PairValue (L.Value W grade) target)) = 0
    simpa only [zero_add] using previous

private theorem collapse_value_add (grade : Nat) {target : Sorts}
    (left right : PairValue (L.Value W grade) target) :
    collapseValue (W := W) grade (left+right) = collapseValue grade left+collapseValue grade right := by
  induction grade with
  | zero => rfl
  | succ grade previous =>
    change PairValue (L.Value W grade) target × PairValue (L.Value W grade) target at left right
    change collapseValue (W := W) grade ((left.1+right.1)+(left.2+right.2)) =
      collapseValue grade (left.1+left.2)+collapseValue grade (right.1+right.2)
    rw [add_add_add_comm,previous]

/-- The existing grade collapse preserves addition before any field is observed. -/
def collapseValueAddHom (grade : Nat) (target : Sorts) :
    PairValue (L.Value W grade) target →+ PairValue W target where
  toFun := collapseValue grade
  map_zero' := collapse_value_zero grade target
  map_add' := collapse_value_add grade

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
