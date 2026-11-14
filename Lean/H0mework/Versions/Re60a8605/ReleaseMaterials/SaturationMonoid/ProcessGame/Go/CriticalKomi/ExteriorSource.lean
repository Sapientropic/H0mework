import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionSparse

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorSource

open RegionProjection RegionAction

/-- A finite geometric check of the exterior; it contains no game outcome. -/
structure Connected {n : Nat} (region : Finset (Point n)) where
  seed : Point n
  outside : seed ∉ region
  component_eq : ExteriorLiberty.component region seed = Finset.univ \ region

def recognize? {n : Nat} (region : Finset (Point n)) : Option (Connected region) :=
  match found : (allPoints n).find? (fun point => decide (point ∉ region)) with
  | none => none
  | some seed =>
      have tested := List.find?_some found
      have outside : seed ∉ region := of_decide_eq_true tested
      if whole : ExteriorLiberty.component region seed = Finset.univ \ region then
        some ⟨seed, outside, whole⟩
      else none

theorem Connected.component_at {n : Nat} {region : Finset (Point n)}
    (connected : Connected region) (point : Point n) (outside : point ∉ region) :
    ExteriorLiberty.component region point = Finset.univ \ region := by
  have member : point ∈ ExteriorLiberty.component region connected.seed := by
    rw [connected.component_eq]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, outside⟩
  have seedValue := (ExteriorLiberty.mask_outside region connected.seed).mpr connected.outside
  exact (groupAt_eq_of_mem seedValue member).trans connected.component_eq

theorem Connected.capacity {n : Nat} {region : Finset (Point n)}
    (connected : Connected region) (board : Board n) (colour : Polarity)
    (room : (stones board colour.other).card < (Finset.univ \ region).card) :
    RegionSparse.Capacity region board colour := by
  intro point outside
  rw [connected.component_at point outside]
  exact room

theorem Connected.replay_capacity {n : Nat} {region : Finset (Point n)}
    (connected : Connected region) {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) (colour : Polarity)
    (room : ExteriorLiberty.placementCount moves < (Finset.univ \ region).card) :
    RegionSparse.Capacity region replay.final.visible.board colour :=
  connected.capacity replay.final.visible.board colour
    (lt_of_le_of_lt (ExteriorLiberty.initial_stones_le_placements replay colour.other) room)

/-- An actual original prefix, its finite footprint and its event count
generate the exact region capture/update equation. -/
theorem Connected.replay_board_exact {n : Nat} {region : Finset (Point n)}
    (connected : Connected region) {law : Law} {moves : List (Move n)}
    (replay : GeneratedReplay law (Frame.initial n) moves) (colour : Polarity)
    (played : Point n) (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region replay.final.visible.board colour)
    (empty : replay.final.visible.board played = none)
    (room : ExteriorLiberty.placementCount moves < (Finset.univ \ region).card) :
    restrict region (boardAfterPlay replay.final.visible.board colour played) =
      boardAfterPlay (restrict region replay.final.visible.board) colour played :=
  RegionSparse.own_board_exact region replay.final.visible.board colour played inside neighbours
    confined empty (connected.replay_capacity replay colour room)

def corner19 : Finset (Point 19) :=
  Finset.univ.filter (fun point => point.1.val < 6 ∧ point.2.val < 6)

def south19 : Finset (Point 19) := insert ((6 : Fin 19), (0 : Fin 19)) corner19

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorSource
