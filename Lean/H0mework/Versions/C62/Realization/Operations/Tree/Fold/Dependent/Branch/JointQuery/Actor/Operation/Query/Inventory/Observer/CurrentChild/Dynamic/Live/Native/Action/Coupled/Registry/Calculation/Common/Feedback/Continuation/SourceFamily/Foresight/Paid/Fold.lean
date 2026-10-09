import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Paid.Word
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Paid.Ledger
section Fold
variable {A B : Type u}
def combine (first : RootedAccountedUnfolding B) (children : List (RootedAccountedUnfolding B)) :=
 children.foldl SourceHistoryCommon.seed first

theorem combine_first (first : RootedAccountedUnfolding B) (children : List (RootedAccountedUnfolding B))
 (event : B) (found : event ∈ first.trace) : event ∈ (combine first children).trace := by
 induction children generalizing first with
 | nil => exact found
 | cons head tail prior =>
  exact prior (SourceHistoryCommon.seed first head) ((SourceHistoryCommon.parallel_left _ _ _).1 event found)

theorem combine_child (first : RootedAccountedUnfolding B) (children : List (RootedAccountedUnfolding B))
 (child : RootedAccountedUnfolding B) (present : child ∈ children) (event : B) (found : event ∈ child.trace) :
 event ∈ (combine first children).trace := by
 induction children generalizing first with
 | nil => exact False.elim (List.not_mem_nil present)
 | cons head tail prior =>
  cases List.mem_cons.mp present with
  | inl same =>
   subst child
   exact combine_first (SourceHistoryCommon.seed first head) tail event
    ((SourceHistoryCommon.parallel_right _ _ _).1 event found)
  | inr later => exact prior (SourceHistoryCommon.seed first head) later

variable (write : A → RootedAccountedUnfolding B)
def atOccurrence (source : A) (children : List (RootedAccountedUnfolding B)) := combine (write source) children
def run (tree : RootedAccountedUnfolding A) := tree.fold (atOccurrence write)
mutual
theorem run_contains (tree : RootedAccountedUnfolding A) (source : A) (present : source ∈ tree.trace)
 (event : B) (written : event ∈ (write source).trace) : event ∈ (run write tree).trace := by
 cases tree with
 | occur root branches =>
  cases List.mem_cons.mp present with
  | inl same =>
   subst source
   exact combine_first (write root) (RootedAccountedUnfolding.foldBranches (atOccurrence write) branches) event written
  | inr later =>
   obtain ⟨child,childFound,eventFound⟩ := branches_contains branches source later event written
   exact combine_child (write root) (RootedAccountedUnfolding.foldBranches (atOccurrence write) branches) child childFound event eventFound

theorem branches_contains (branches : AccountedBranches A) (source : A)
 (present : source ∈ RootedAccountedUnfolding.traceBranches branches) (event : B) (written : event ∈ (write source).trace) :
 ∃ child, child ∈ RootedAccountedUnfolding.foldBranches (atOccurrence write) branches ∧ event ∈ child.trace := by
 cases branches with
 | nil => exact False.elim (List.not_mem_nil present)
 | cons head tail =>
  cases List.mem_append.mp present with
  | inl here => exact ⟨run write head, List.mem_cons_self, run_contains head source here event written⟩
  | inr later =>
   obtain ⟨child,childFound,eventFound⟩ := branches_contains tail source later event written
   exact ⟨child,List.mem_cons_of_mem _ childFound,eventFound⟩
end
end Fold

end Lower.SourceFamily.Foresight.Paid.Ledger
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
