import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionCapture
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorLiberty

/-!
An actual sparse exterior removes the apparent boundary-capture alternatives.
The guard compares source occupancy with source-generated exterior components;
no boundary group is assumed alive.  Interior native captures then commute
with the same board restriction.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionSparse

open RegionProjection RegionAction RegionCapture

def Capacity {n : Nat} (region : Finset (Point n)) (board : Board n) (colour : Polarity) : Prop :=
  ∀ point, point ∉ region →
    (stones board colour.other).card < (ExteriorLiberty.component region point).card

theorem capacity_set {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (empty : board played = none)
    (capacity : Capacity region board colour) :
    Capacity region (Board.set board played (some colour)) colour := by
  intro point outside
  rw [ExteriorLiberty.opposing_stones_set empty]
  exact capacity point outside

/-- Both capture programs consume the same original white components.  A
component reaching the exterior has a generated actual liberty on both faces. -/
theorem own_capture_exact {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (playedInterior : adjacentPoints played ⊆ region)
    (confined : Confined region board colour) (empty : board played = none)
    (capacity : Capacity region board colour) :
    capturedStonesAfterPlay board colour played =
      capturedStonesAfterPlay (restrict region board) colour played := by
  have confinedPlaced := ExteriorLiberty.confined_set region confined inside
  have capacityPlaced := capacity_set region board colour played empty capacity
  unfold capturedStonesAfterPlay
  rw [← restrict_set region board colour played inside]
  apply Finset.biUnion_congr rfl
  intro neighbour adjacent
  have neighbourInside := playedInterior adjacent
  simp only [restrict_at _ _ neighbourInside]
  by_cases occupied : Board.set board played (some colour) neighbour = some colour.other
  · by_cases interior : Interior region (groupAt (restrict region
        (Board.set board played (some colour))) neighbour)
    · have groupEq := interior_group region (Board.set board played (some colour))
        colour.other neighbour neighbourInside occupied interior
      have libertyEq := liberties_of_interior_group region (Board.set board played (some colour))
        neighbour groupEq (groupEq ▸ interior)
      have sameLiberty : stoneHasLiberty (restrict region (Board.set board played (some colour))) neighbour ↔
          stoneHasLiberty (Board.set board played (some colour)) neighbour := by
        rw [← liberties_nonempty_iff, ← liberties_nonempty_iff, libertyEq]
      simp only [occupied, true_and, sameLiberty, groupEq]
    · have boundary : ∃ stone ∈ groupAt (restrict region (Board.set board played (some colour))) neighbour,
          ∃ exterior ∈ adjacentPoints stone, exterior ∉ region := by
        by_contra absent
        apply interior
        intro stone member exterior adjacent
        by_contra outside
        exact absent ⟨stone, member, exterior, adjacent, outside⟩
      obtain ⟨stone, member, exterior, exteriorAdjacent, outside⟩ := boundary
      have originalMember := local_group_subset region (Board.set board played (some colour))
        colour.other neighbour neighbourInside occupied member
      have originalLiberty := ExteriorLiberty.liberty_of_capacity region confinedPlaced occupied
        originalMember exteriorAdjacent outside (capacityPlaced exterior outside)
      have localLiberty : stoneHasLiberty
          (restrict region (Board.set board played (some colour))) neighbour :=
        ⟨stone, member, exterior, exteriorAdjacent, by simp only [restrict, if_neg outside]⟩
      simp [originalLiberty, localLiberty]
  · simp only [occupied, false_and, ↓reduceIte]

theorem own_board_exact {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (playedInterior : adjacentPoints played ⊆ region)
    (confined : Confined region board colour) (empty : board played = none)
    (capacity : Capacity region board colour) :
    restrict region (boardAfterPlay board colour played) =
      boardAfterPlay (restrict region board) colour played := by
  have captureEq := own_capture_exact region board colour played inside playedInterior confined empty capacity
  have setEq := restrict_set region board colour played inside
  funext point
  by_cases captured : point ∈ capturedStonesAfterPlay (restrict region board) colour played
  · by_cases member : point ∈ region
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captureEq, captured]
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captured]
  · by_cases member : point ∈ region
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captureEq, captured]
      simpa only [restrict_at _ _ member] using congrFun setEq point
    · have different : point ≠ played := by intro same; exact member (same.symm ▸ inside)
      simp only [restrict, member, ↓reduceIte, boardAfterPlay, captured,
        Board.set_other _ _ different]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionSparse
