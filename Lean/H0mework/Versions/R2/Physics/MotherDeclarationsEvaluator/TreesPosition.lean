import H0mework.Versions.R2.Physics.MotherDeclarationsEvaluator.TreesShape

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTrees

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RootedAccountedUnfolding

universe u

mutual

/-- Addresses depend only on constructor position, never on payload equality. -/
def positions {E : Type u} : RootedAccountedUnfolding E → RootedAccountedUnfolding ℕ
  | .occur _ branches => .occur 0 (mapBranches Nat.succ (branchPositions branches))

def branchPositions {E : Type u} : AccountedBranches E → AccountedBranches ℕ
  | .nil => .nil
  | .cons head tail => .cons ((positions head).map (fun n => 2 * n))
      (mapBranches (fun n => 2 * n + 1) (branchPositions tail))

end

mutual

theorem positions_recover {E : Type u} (tree : RootedAccountedUnfolding E) :
    ∃ values : ℕ → E, (positions tree).map values = tree := by
  cases tree with
  | occur origin branches =>
    obtain ⟨values, recovered⟩ := branchPositions_recover origin branches
    refine ⟨(fun | 0 => origin | n + 1 => values n), ?_⟩
    change RootedAccountedUnfolding.occur origin
      (mapBranches _ (mapBranches Nat.succ (branchPositions branches))) = _
    rw [mapBranches_map_map]
    change RootedAccountedUnfolding.occur origin
      (mapBranches values (branchPositions branches)) = _
    rw [recovered]

theorem branchPositions_recover {E : Type u} (fallback : E) (branches : AccountedBranches E) :
    ∃ values : ℕ → E, mapBranches values (branchPositions branches) = branches := by
  cases branches with
  | nil => exact ⟨fun _ => fallback, rfl⟩
  | cons head tail =>
    obtain ⟨headValues, headRecovered⟩ := positions_recover head
    obtain ⟨tailValues, tailRecovered⟩ := branchPositions_recover fallback tail
    let values : ℕ → E := fun n =>
      if n % 2 = 0 then headValues (n / 2) else tailValues (n / 2)
    have even : values ∘ (fun n => 2 * n) = headValues := by
      funext n
      simp [values]
    have odd : values ∘ (fun n => 2 * n + 1) = tailValues := by
      funext n
      simp [values, Nat.add_div]
    refine ⟨values, ?_⟩
    change AccountedBranches.cons (((positions head).map (fun n => 2 * n)).map values)
      (mapBranches values (mapBranches (fun n => 2 * n + 1) (branchPositions tail))) = _
    rw [map_map, mapBranches_map_map, even, odd, headRecovered, tailRecovered]

end

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherEvaluatorTrees
