import H0mework.Foundation.Source.AccountedUnfolding

/-!
# Exact provenance of one finite advance

`RootedAccountedUnfolding.advance` is the sole way to expose another finite
patch.  This file records its trace law once, generically: every event after
an advance was already present, or belongs to the patch generated at an
actual old frontier leaf.  Conversely both kinds of events remain visible.

No domain payload, completed value, observer, or choice enters this law.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootedAccountedUnfolding

universe u

theorem frontier_mem_trace {Root : Type u}
    (occurrence : RootedAccountedUnfolding Root) :
    ∀ event, event ∈ occurrence.frontier → event ∈ occurrence.trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ event, event ∈ current.frontier → event ∈ current.trace)
    (motive_2 := fun branches =>
      ∀ event, event ∈ frontierBranches branches →
        event ∈ traceBranches branches)
    (fun root branches branchResult event event_mem => by
      cases branches with
      | nil => exact event_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root (branchResult event event_mem))
    (fun event event_mem => by
      change event ∈ ([] : List Root) at event_mem
      exact False.elim (List.not_mem_nil event_mem))
    (fun head tail headResult tailResult event event_mem => by
      change event ∈ head.frontier ++ frontierBranches tail at event_mem
      change event ∈ head.trace ++ traceBranches tail
      rw [List.mem_append] at event_mem ⊢
      cases event_mem with
      | inl inHead => exact Or.inl (headResult event inHead)
      | inr inTail => exact Or.inr (tailResult event inTail))
    occurrence

theorem trace_mem_trace_advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    ∀ event, event ∈ occurrence.trace →
      event ∈ (occurrence.advance next).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ event, event ∈ current.trace →
        event ∈ (current.advance next).trace)
    (motive_2 := fun branches =>
      ∀ event, event ∈ traceBranches branches →
        event ∈ traceBranches (advanceBranches next branches))
    (fun root branches branchResult event event_mem => by
      cases branches with
      | nil =>
          change event ∈ [root] at event_mem
          have event_eq : event = root := by simpa using event_mem
          subst event
          exact root_mem_trace _
      | cons head tail =>
          change event ∈ root :: traceBranches (.cons head tail) at event_mem
          change event ∈ root ::
            traceBranches (advanceBranches next (.cons head tail))
          rw [List.mem_cons] at event_mem ⊢
          cases event_mem with
          | inl event_eq => exact Or.inl event_eq
          | inr branch_mem =>
              exact Or.inr (branchResult event branch_mem))
    (fun event event_mem => by
      change event ∈ ([] : List Root) at event_mem
      exact False.elim (List.not_mem_nil event_mem))
    (fun head tail headResult tailResult event event_mem => by
      change event ∈ head.trace ++ traceBranches tail at event_mem
      change event ∈ (head.advance next).trace ++
        traceBranches (advanceBranches next tail)
      rw [List.mem_append] at event_mem ⊢
      cases event_mem with
      | inl inHead => exact Or.inl (headResult event inHead)
      | inr inTail => exact Or.inr (tailResult event inTail))
    occurrence

theorem generated_trace_mem_trace_advance {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    ∀ leaf, leaf ∈ occurrence.frontier →
      ∀ event, event ∈ (next leaf).trace →
        event ∈ (occurrence.advance next).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ leaf, leaf ∈ current.frontier →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ (current.advance next).trace)
    (motive_2 := fun branches =>
      ∀ leaf, leaf ∈ frontierBranches branches →
        ∀ event, event ∈ (next leaf).trace →
          event ∈ traceBranches (advanceBranches next branches))
    (fun root branches branchResult leaf leaf_mem event event_mem => by
      cases branches with
      | nil =>
          change leaf ∈ [root] at leaf_mem
          have leaf_eq : leaf = root := by simpa using leaf_mem
          subst leaf
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.nil : AccountedBranches Root)).advance next =
                RootedAccountedUnfolding.occur root
                  (AccountedBranches.singleton (next root)) from rfl]
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.singleton (next root))).trace =
                root :: (next root).trace by
            simp [trace, AccountedBranches.singleton]]
          exact List.mem_cons_of_mem root event_mem
      | cons head tail =>
          exact List.mem_cons_of_mem root
            (branchResult leaf leaf_mem event event_mem))
    (fun leaf leaf_mem event event_mem => by
      change leaf ∈ ([] : List Root) at leaf_mem
      exact False.elim (List.not_mem_nil leaf_mem))
    (fun head tail headResult tailResult leaf leaf_mem event event_mem => by
      change leaf ∈ head.frontier ++ frontierBranches tail at leaf_mem
      change event ∈ (head.advance next).trace ++
        traceBranches (advanceBranches next tail)
      rw [List.mem_append] at leaf_mem ⊢
      cases leaf_mem with
      | inl inHead => exact Or.inl (headResult leaf inHead event event_mem)
      | inr inTail => exact Or.inr (tailResult leaf inTail event event_mem))
    occurrence

theorem trace_advance_cases {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root) :
    ∀ event, event ∈ (occurrence.advance next).trace →
      event ∈ occurrence.trace ∨
        ∃ leaf, leaf ∈ occurrence.frontier ∧
          event ∈ (next leaf).trace :=
  RootedAccountedUnfolding.rec
    (motive_1 := fun current =>
      ∀ event, event ∈ (current.advance next).trace →
        event ∈ current.trace ∨
          ∃ leaf, leaf ∈ current.frontier ∧
            event ∈ (next leaf).trace)
    (motive_2 := fun branches =>
      ∀ event, event ∈ traceBranches (advanceBranches next branches) →
        event ∈ traceBranches branches ∨
          ∃ leaf, leaf ∈ frontierBranches branches ∧
            event ∈ (next leaf).trace)
    (fun root branches branchResult event event_mem => by
      cases branches with
      | nil =>
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.nil : AccountedBranches Root)).advance next =
                RootedAccountedUnfolding.occur root
                  (AccountedBranches.singleton (next root)) from rfl] at event_mem
          rw [show (RootedAccountedUnfolding.occur root
              (AccountedBranches.singleton (next root))).trace =
                root :: (next root).trace by
            simp [trace, AccountedBranches.singleton]] at event_mem
          rw [List.mem_cons] at event_mem
          cases event_mem with
          | inl event_eq =>
              subst event
              exact Or.inl (root_mem_trace _)
          | inr next_mem =>
              exact Or.inr ⟨root, by
                change root ∈ [root]
                simp, next_mem⟩
      | cons head tail =>
          change event ∈ root ::
            traceBranches (advanceBranches next (.cons head tail)) at event_mem
          rw [List.mem_cons] at event_mem
          cases event_mem with
          | inl event_eq =>
              subst event
              exact Or.inl (root_mem_trace _)
          | inr branch_mem =>
              cases branchResult event branch_mem with
              | inl old_mem =>
                  exact Or.inl (List.mem_cons_of_mem root old_mem)
              | inr generated => exact Or.inr generated)
    (fun event event_mem => by
      change event ∈ ([] : List Root) at event_mem
      exact False.elim (List.not_mem_nil event_mem))
    (fun head tail headResult tailResult event event_mem => by
      change event ∈ (head.advance next).trace ++
        traceBranches (advanceBranches next tail) at event_mem
      rw [List.mem_append] at event_mem
      cases event_mem with
      | inl inHead =>
          cases headResult event inHead with
          | inl oldHead =>
              exact Or.inl (by
                change event ∈ head.trace ++ traceBranches tail
                rw [List.mem_append]
                exact Or.inl oldHead)
          | inr generated =>
              obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
              exact Or.inr ⟨leaf, by
                change leaf ∈ head.frontier ++ frontierBranches tail
                rw [List.mem_append]
                exact Or.inl leaf_mem,
                generated_mem⟩
      | inr inTail =>
          cases tailResult event inTail with
          | inl oldTail =>
              exact Or.inl (by
                change event ∈ head.trace ++ traceBranches tail
                rw [List.mem_append]
                exact Or.inr oldTail)
          | inr generated =>
              obtain ⟨leaf, leaf_mem, generated_mem⟩ := generated
              exact Or.inr ⟨leaf, by
                change leaf ∈ head.frontier ++ frontierBranches tail
                rw [List.mem_append]
                exact Or.inr leaf_mem,
                generated_mem⟩)
    occurrence

/-- Exact finite no-island law for one source advance. -/
theorem mem_trace_advance_iff {Root : Type u}
    (next : Root → RootedAccountedUnfolding Root)
    (occurrence : RootedAccountedUnfolding Root)
    (event : Root) :
    event ∈ (occurrence.advance next).trace ↔
      event ∈ occurrence.trace ∨
        ∃ leaf, leaf ∈ occurrence.frontier ∧
          event ∈ (next leaf).trace := by
  constructor
  · exact trace_advance_cases next occurrence event
  · intro source
    cases source with
    | inl old => exact trace_mem_trace_advance next occurrence event old
    | inr generated =>
        obtain ⟨leaf, leaf_mem, event_mem⟩ := generated
        exact generated_trace_mem_trace_advance next occurrence leaf leaf_mem
          event event_mem

end RootedAccountedUnfolding
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
