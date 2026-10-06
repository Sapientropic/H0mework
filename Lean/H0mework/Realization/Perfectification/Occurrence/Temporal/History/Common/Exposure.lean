import H0mework.Realization.Perfectification.Occurrence.Temporal.History.Common.Source
set_option autoImplicit false
noncomputable section
universe u v w r
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryCommon
open CofinalHistorySettlement
variable {A : Type v} {B : Type w} {G : Type u} {Root : Type r}
variable {rootA : RootedAccountedUnfolding A} {rootB : RootedAccountedUnfolding B}
variable {seedA seedB : RootedAccountedUnfolding (PresentedRelationEventAt G)}
variable {nextA nextB : RootedAccountedUnfolding (PresentedRelationEventAt G → RootedAccountedUnfolding (PresentedRelationEventAt G))}
variable (left : RootGeneratedCofinalHistoryAt rootA seedA nextA)
variable (right : RootGeneratedCofinalHistoryAt rootB seedB nextB)
def Exposure {X : Type u} (first second : RootedAccountedUnfolding X) : Prop :=
  (∀ event, event ∈ first.trace → event ∈ second.trace) ∧
  (∀ event, event ∈ first.frontier → event ∈ second.frontier)
mutual
 theorem trace_advance {X : Type u} (action : X → RootedAccountedUnfolding X)
     (tree : RootedAccountedUnfolding X) (event : X) :
     event ∈ (tree.advance action).trace ↔ event ∈ tree.trace ∨
       ∃ leaf, leaf ∈ tree.frontier ∧ event ∈ (action leaf).trace := by
   cases tree with
   | occur root branches =>
     cases branches with
     | nil => simp [RootedAccountedUnfolding.advance, RootedAccountedUnfolding.trace,
         RootedAccountedUnfolding.frontier, AccountedBranches.singleton]
     | cons head tail =>
       change event ∈ root :: RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.advanceBranches action (.cons head tail)) ↔ _
       rw [List.mem_cons, trace_branches_advance]
       have trace_eq : (RootedAccountedUnfolding.occur root (.cons head tail)).trace =
           root :: RootedAccountedUnfolding.traceBranches (.cons head tail) := rfl
       have frontier_eq : (RootedAccountedUnfolding.occur root (.cons head tail)).frontier =
           RootedAccountedUnfolding.frontierBranches (.cons head tail) := rfl
       rw [trace_eq, frontier_eq, List.mem_cons]
       tauto
 theorem trace_branches_advance {X : Type u} (action : X → RootedAccountedUnfolding X)
     (branches : AccountedBranches X) (event : X) :
     event ∈ RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.advanceBranches action branches) ↔
       event ∈ RootedAccountedUnfolding.traceBranches branches ∨
       ∃ leaf, leaf ∈ RootedAccountedUnfolding.frontierBranches branches ∧ event ∈ (action leaf).trace := by
   cases branches with
   | nil => simp [RootedAccountedUnfolding.advanceBranches, RootedAccountedUnfolding.traceBranches, RootedAccountedUnfolding.frontierBranches]
   | cons head tail =>
     change event ∈ (head.advance action).trace ++ RootedAccountedUnfolding.traceBranches (RootedAccountedUnfolding.advanceBranches action tail) ↔ _
     simp only [List.mem_append, trace_advance, trace_branches_advance]
     change _ ↔ (event ∈ head.trace ++ RootedAccountedUnfolding.traceBranches tail) ∨
       ∃ leaf, (leaf ∈ head.frontier ++ RootedAccountedUnfolding.frontierBranches tail) ∧ event ∈ (action leaf).trace
     simp only [List.mem_append]
     aesop
end
theorem exposure_advance {X : Type u}
    {first second : RootedAccountedUnfolding X} {firstAction secondAction : X → RootedAccountedUnfolding X}
    (prior : Exposure first second) (actions : ∀ event, Exposure (firstAction event) (secondAction event)) :
    Exposure (first.advance firstAction) (second.advance secondAction) := by
  constructor
  · intro event present
    rcases (trace_advance _ _ _).mp present with old | ⟨leaf, leaf_mem, new_mem⟩
    · exact (trace_advance _ _ _).mpr (.inl (prior.1 event old))
    · exact (trace_advance _ _ _).mpr (.inr ⟨leaf, prior.2 leaf leaf_mem, (actions leaf).1 event new_mem⟩)
  · intro event present
    rw [RootedAccountedUnfolding.frontier_advance] at present ⊢
    rcases List.mem_flatMap.mp present with ⟨leaf, leaf_mem, new_mem⟩
    exact List.mem_flatMap.mpr ⟨leaf, prior.2 leaf leaf_mem, (actions leaf).2 event new_mem⟩

theorem parallel_left {X : Type u} (anchor : X) (first second : RootedAccountedUnfolding X) :
    Exposure first (RootedAccountedUnfolding.parallelAt anchor first second) := by
  constructor
  · intro event present
    have expanded : (RootedAccountedUnfolding.parallelAt anchor first second).trace =
        anchor :: (first.trace ++ (second.trace ++ [])) := rfl
    rw [expanded]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ present)
  · intro event present
    rw [RootedAccountedUnfolding.frontier_parallelAt]
    exact List.mem_append_left _ present

theorem parallel_right {X : Type u} (anchor : X) (first second : RootedAccountedUnfolding X) :
    Exposure second (RootedAccountedUnfolding.parallelAt anchor first second) := by
  constructor
  · intro event present
    have expanded : (RootedAccountedUnfolding.parallelAt anchor first second).trace =
        anchor :: (first.trace ++ (second.trace ++ [])) := rfl
    rw [expanded]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ present))
  · intro event present
    rw [RootedAccountedUnfolding.frontier_parallelAt]
    exact List.mem_append_right _ present

theorem observations_left (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    Exposure (left.observation stage) ((history left right actual).observation stage) := by
  induction stage with
  | zero => exact parallel_left _ _ _
  | succ stage prior =>
    exact exposure_advance prior (fun event => parallel_left event _ _)

theorem observations_right (actual : RootedAccountedUnfolding Root) (stage : Nat) :
    Exposure (right.observation stage) ((history left right actual).observation stage) := by
  induction stage with
  | zero => exact parallel_right _ _ _
  | succ stage prior =>
    exact exposure_advance prior (fun event => parallel_right event _ _)
end SourceHistoryCommon
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
