import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionAction

/-!
The regional board is a restriction of the original board.  A confined colour
has exactly the same generated groups; an interior group has exactly the same
liberties.  Opponent components meeting the exterior retain a separate boundary
responsibility rather than being declared captured or alive.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionProjection

def restrict {n : Nat} (region : Finset (Point n)) (board : Board n) : Board n :=
  fun point => if point ∈ region then board point else none

theorem restrict_at {n : Nat} (region : Finset (Point n)) (board : Board n)
    {point : Point n} (inside : point ∈ region) : restrict region board point = board point := by
  simp only [restrict, if_pos inside]

theorem restrict_colour {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (point : Point n) :
    restrict region board point = some colour ↔ point ∈ region ∧ board point = some colour := by
  by_cases inside : point ∈ region <;> simp only [restrict, inside, ↓reduceIte]
  · simp
  · simp

def Confined {n : Nat} (region : Finset (Point n)) (board : Board n) (colour : Polarity) : Prop :=
  ∀ point, board point = some colour → point ∈ region

theorem confined_colour {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (confined : Confined region board colour) (point : Point n) :
    restrict region board point = some colour ↔ board point = some colour := by
  rw [restrict_colour]
  exact ⟨And.right, fun occupied => ⟨confined point occupied, occupied⟩⟩

theorem confined_group {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (occupied : board seed = some colour)
    (confined : Confined region board colour) :
    groupAt (restrict region board) seed = groupAt board seed := by
  have localSeed := (confined_colour region board colour confined seed).mpr occupied
  simp only [groupAt, occupied, localSeed]
  apply componentAt_eq_of_same_value_fiber
  intro point
  rw [localSeed, occupied]
  exact confined_colour region board colour confined point

theorem local_group_inside {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (inside : seed ∈ region)
    (occupied : board seed = some colour) : groupAt (restrict region board) seed ⊆ region := by
  have localSeed : restrict region board seed = some colour := by rw [restrict_at _ _ inside, occupied]
  intro point member
  have same := groupAt_member_colour localSeed member
  exact ((restrict_colour region board colour point).mp same).1

theorem local_group_subset {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (inside : seed ∈ region)
    (occupied : board seed = some colour) :
    groupAt (restrict region board) seed ⊆ groupAt board seed := by
  have localSeed : restrict region board seed = some colour := by rw [restrict_at _ _ inside, occupied]
  simp only [groupAt, localSeed, occupied]
  apply componentAt_subset_of_component_values_preserved
  intro point member
  have localValue := (componentAt_member_value member).trans localSeed
  exact ((restrict_colour region board colour point).mp localValue).2.trans occupied.symm

def Interior {n : Nat} (region group : Finset (Point n)) : Prop :=
  ∀ stone ∈ group, adjacentPoints stone ⊆ region

/-- A group whose complete boundary lies inside the observed region has no
unseen same-colour connection to the exterior. -/
theorem interior_group {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (inside : seed ∈ region)
    (occupied : board seed = some colour)
    (interior : Interior region (groupAt (restrict region board) seed)) :
    groupAt (restrict region board) seed = groupAt board seed := by
  have localSeed : restrict region board seed = some colour := by rw [restrict_at _ _ inside, occupied]
  apply Finset.Subset.antisymm (local_group_subset region board colour seed inside occupied)
  simp only [groupAt, localSeed, occupied] at interior ⊢
  apply componentAt_minimal (predicate := fun point => point ∈ componentAt (restrict region board) seed)
    (point_mem_componentAt _ _)
  intro current _ currentMember candidate adjacent value
  have localAdjacent : candidate ∈ adjacentPoints current := by
    simpa only [adjacentPoints, List.mem_toFinset] using adjacent
  have candidateInside := interior current currentMember localAdjacent
  apply componentAt_closed currentMember adjacent
  rw [restrict_at _ _ candidateInside, localSeed]
  exact value.trans occupied

theorem liberties_of_interior_group {n : Nat} (region : Finset (Point n)) (board : Board n)
    (seed : Point n)
    (groupEq : groupAt (restrict region board) seed = groupAt board seed)
    (interior : Interior region (groupAt board seed)) :
    LibertyReserve.liberties (restrict region board) seed = LibertyReserve.liberties board seed := by
  ext liberty
  simp only [LibertyReserve.mem_liberties, groupEq]
  constructor
  · rintro ⟨⟨stone, member, adjacent⟩, free⟩
    have inside := interior stone member adjacent
    exact ⟨⟨stone, member, adjacent⟩, (restrict_at _ _ inside).symm.trans free⟩
  · rintro ⟨⟨stone, member, adjacent⟩, free⟩
    have inside := interior stone member adjacent
    exact ⟨⟨stone, member, adjacent⟩, (restrict_at _ _ inside).trans free⟩

theorem confined_liberties {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (seed : Point n) (occupied : board seed = some colour)
    (confined : Confined region board colour) (interior : Interior region (groupAt board seed)) :
    LibertyReserve.liberties (restrict region board) seed = LibertyReserve.liberties board seed :=
  liberties_of_interior_group region board seed
    (confined_group region board colour seed occupied confined) interior

def SupportInterior {n : Nat} (region : Finset (Point n)) (board : Board n) (colour : Polarity) : Prop :=
  ∀ stone, board stone = some colour → adjacentPoints stone ⊆ region

/-- An outside opponent placement cannot meet an interior own stone, so its
capture set is empty even when the interior contains several vulnerable groups. -/
theorem outside_capture_empty {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n)
    (interior : SupportInterior region board colour) (outside : played ∉ region) :
    capturedStonesAfterPlay board colour.other played = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro point captured
  unfold capturedStonesAfterPlay at captured
  obtain ⟨neighbour, adjacent, member⟩ := Finset.mem_biUnion.mp captured
  split at member
  · rename_i taken
    have old := taken.1
    rw [Polarity.other_other] at old
    have different : neighbour ≠ played := by
      intro same
      subst neighbour
      rw [Board.set_self] at old
      exact Polarity.other_ne colour (Option.some.inj old)
    rw [Board.set_other _ _ different] at old
    apply outside
    apply interior neighbour old
    exact mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
      (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))
  · simp at member

theorem outside_restrict {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n)
    (interior : SupportInterior region board colour) (outside : played ∉ region) :
    restrict region (boardAfterPlay board colour.other played) = restrict region board := by
  funext point
  by_cases inside : point ∈ region
  · rw [restrict_at _ _ inside, restrict_at _ _ inside]
    have different : point ≠ played := by
      intro same
      exact outside (same ▸ inside)
    simp only [boardAfterPlay, outside_capture_empty region board colour played interior outside]
    simp only [Finset.notMem_empty, ↓reduceIte, Board.set_other _ _ different]
  · simp only [restrict, if_neg inside]

/-- The environment event retains the original play phase and complete history
append while exposing an unchanged regional board. -/
theorem outside_nativeStep {n : Nat} (region : Finset (Point n))
    {frame target : Frame n} {colour : Polarity} {played : Point n}
    (interior : SupportInterior region frame.visible.board colour)
    (opponent : frame.visible.toMove = colour.other) (outside : played ∉ region)
    (step : LegalStep (Law.positionalSuperko 0) frame (.play played) target) :
    restrict region target.visible.board = restrict region frame.visible.board ∧
      target.visible.status = .playing ∧ target.visible.consecutivePasses = 0 ∧
      target.visible.toMove = colour ∧
      target.positionHistory = frame.positionHistory ++ [target.visible.situation] := by
  have facts := play_step_facts step
  have boardTurn : target.visible.board =
      boardAfterPlay frame.visible.board frame.visible.toMove played ∧
      target.visible.toMove = frame.visible.toMove.other := by
    have visible := nativeStep_visible_eq step
    simp only [stepVisible?, playVisible?, facts.1] at visible
    split at visible
    · split at visible
      · split at visible
        · simp at visible
        · rw [← Option.some.inj visible]
          exact ⟨rfl, rfl⟩
      · simp at visible
    · simp at visible
  refine ⟨?_, facts.2.1, facts.2.2.1, ?_, nativeStep_positionHistory_eq step⟩
  · rw [boardTurn.1, opponent]
    exact outside_restrict region frame.visible.board colour played interior outside
  · rw [boardTurn.2, opponent, Polarity.other_other]

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionProjection
