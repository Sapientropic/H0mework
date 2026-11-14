import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionProjection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionCapture

open RegionProjection

theorem restrict_set {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region) :
    restrict region (Board.set board played (some colour)) =
      Board.set (restrict region board) played (some colour) := by
  funext point
  by_cases same : point = played
  · subst point
    rw [restrict_at _ _ inside, Board.set_self, Board.set_self]
  · by_cases member : point ∈ region
    · rw [restrict_at _ _ member, Board.set_other _ _ same,
        Board.set_other _ _ same, restrict_at _ _ member]
    · simp only [restrict, if_neg member, Board.set_other _ _ same]

theorem placed_opponent_colour {n : Nat} {board : Board n} {colour : Polarity}
    {played point : Point n}
    (occupied : Board.set board played (some colour.other) point = some colour) :
    board point = some colour := by
  by_cases same : point = played
  · subst point
    rw [Board.set_self] at occupied
    exact False.elim (Polarity.other_ne colour (Option.some.inj occupied))
  · rw [Board.set_other _ _ same] at occupied
    exact occupied

theorem confined_opponent_set {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (confined : Confined region board colour) :
    Confined region (Board.set board played (some colour.other)) colour := by
  intro point occupied
  exact confined point (placed_opponent_colour occupied)

theorem interior_opponent_set {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (interior : SupportInterior region board colour) :
    SupportInterior region (Board.set board played (some colour.other)) colour := by
  intro point occupied
  exact interior point (placed_opponent_colour occupied)

theorem liberties_nonempty_iff {n : Nat} (board : Board n) (seed : Point n) :
    (LibertyReserve.liberties board seed).Nonempty ↔ stoneHasLiberty board seed := by
  constructor
  · rintro ⟨liberty, member⟩
    obtain ⟨⟨stone, groupMember, adjacent⟩, empty⟩ := LibertyReserve.mem_liberties.mp member
    exact ⟨stone, groupMember, liberty, adjacent, empty⟩
  · rintro ⟨stone, groupMember, liberty, adjacent, empty⟩
    exact ⟨liberty, LibertyReserve.mem_liberties.mpr ⟨⟨stone, groupMember, adjacent⟩, empty⟩⟩

/-- Interior own components have the same capture condition in the original
board and its region restriction, including groups that currently have one liberty. -/
theorem opponent_capture_exact {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (confined : Confined region board colour) (interior : SupportInterior region board colour) :
    capturedStonesAfterPlay board colour.other played =
      capturedStonesAfterPlay (restrict region board) colour.other played := by
  have confinedPlaced := confined_opponent_set region board colour played confined
  have interiorPlaced := interior_opponent_set region board colour played interior
  unfold capturedStonesAfterPlay
  apply congrArg (fun groups => (adjacentPoints played).biUnion groups)
  funext neighbour
  simp only [Polarity.other_other]
  by_cases occupied : Board.set board played (some colour.other) neighbour = some colour
  · have localOccupied : Board.set (restrict region board) played (some colour.other) neighbour =
        some colour := by
      rw [← restrict_set region board colour.other played inside]
      exact (confined_colour region _ colour confinedPlaced neighbour).mpr occupied
    have groupEq := confined_group region (Board.set board played (some colour.other))
      colour neighbour occupied confinedPlaced
    have libertyEq := confined_liberties region (Board.set board played (some colour.other))
      colour neighbour occupied confinedPlaced (fun stone member =>
        interiorPlaced stone (groupAt_member_colour occupied member))
    rw [restrict_set region board colour.other played inside] at groupEq libertyEq
    have sameLiberty : stoneHasLiberty (Board.set (restrict region board) played (some colour.other)) neighbour ↔
        stoneHasLiberty (Board.set board played (some colour.other)) neighbour := by
      rw [← liberties_nonempty_iff, ← liberties_nonempty_iff, libertyEq]
    simp only [occupied, localOccupied, true_and, sameLiberty, groupEq]
  · have localAbsent : Board.set (restrict region board) played (some colour.other) neighbour ≠
        some colour := by
      intro localOccupied
      rw [← restrict_set region board colour.other played inside] at localOccupied
      exact occupied ((confined_colour region _ colour confinedPlaced neighbour).mp localOccupied)
    simp only [occupied, localAbsent, false_and, ↓reduceIte]

theorem opponent_board_exact {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (confined : Confined region board colour) (interior : SupportInterior region board colour) :
    restrict region (boardAfterPlay board colour.other played) =
      boardAfterPlay (restrict region board) colour.other played := by
  have captureEq := opponent_capture_exact region board colour played inside confined interior
  have setEq := restrict_set region board colour.other played inside
  funext point
  by_cases captured : point ∈ capturedStonesAfterPlay (restrict region board) colour.other played
  · by_cases member : point ∈ region
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captureEq, captured]
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captured]
  · by_cases member : point ∈ region
    · simp only [restrict, member, ↓reduceIte, boardAfterPlay, captureEq, captured]
      simpa only [restrict_at _ _ member] using congrFun setEq point
    · have different : point ≠ played := by intro same; exact member (same.symm ▸ inside)
      simp only [restrict, member, ↓reduceIte, boardAfterPlay, captured,
        Board.set_other _ _ different]

/-- Removing the exterior cannot make a legal interior stone lack all
liberties: either its group stays interior, or the cut exposes an empty neighbour. -/
theorem liberty_projects {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (inside : seed ∈ region)
    (occupied : board seed = some colour) (liberty : stoneHasLiberty board seed) :
    stoneHasLiberty (restrict region board) seed := by
  by_cases interior : Interior region (groupAt (restrict region board) seed)
  · have groupEq := interior_group region board colour seed inside occupied interior
    have wholeInterior : Interior region (groupAt board seed) := groupEq ▸ interior
    have libertyEq := liberties_of_interior_group region board seed groupEq wholeInterior
    rw [← liberties_nonempty_iff, libertyEq]
    exact (liberties_nonempty_iff board seed).mpr liberty
  · have boundary : ∃ stone ∈ groupAt (restrict region board) seed,
        ∃ candidate ∈ adjacentPoints stone, candidate ∉ region := by
      by_contra absent
      apply interior
      intro stone member candidate adjacent
      by_contra outside
      exact absent ⟨stone, member, candidate, adjacent, outside⟩
    obtain ⟨stone, member, candidate, adjacent, outside⟩ := boundary
    exact ⟨stone, member, candidate, adjacent, by simp only [restrict, if_neg outside]⟩

/-- Every original legal opponent placement passes the region's no-suicide
guard.  PSK history remains a separate source responsibility. -/
theorem opponent_noSuicide {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (confined : Confined region board colour) (interior : SupportInterior region board colour)
    (legal : stoneHasLiberty (boardAfterPlay board colour.other played) played) :
    stoneHasLiberty (boardAfterPlay (restrict region board) colour.other played) played := by
  rw [← opponent_board_exact region board colour played inside confined interior]
  exact liberty_projects region (boardAfterPlay board colour.other played) colour.other played
    inside (TwoEye.Growth.placed_survives board colour.other played) legal

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionCapture
