import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ExteriorSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.TwoEyeRecognize

/-!
The same regional geometry and action lift to the original frame. Source
support pays eye containment and liberty equality; source exterior capacity
pays capture equality; the original history bound pays the original PSK move.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionLift

open RegionProjection RegionAction

private theorem eye_inside {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {g : TwoEye.Geometry n} {eye : Point n}
    (interior : SupportInterior region board colour)
    (holds : TwoEye.Holds g colour (restrict region board))
    (boundary : adjacentPoints eye ⊆ g.core) (neighbour : (adjacentPoints eye).Nonempty) :
    eye ∈ region := by
  obtain ⟨stone, adjacent⟩ := neighbour
  have localColour := TwoEye.core_colour holds (boundary adjacent)
  have originalColour := ((restrict_colour region board colour stone).mp localColour).2
  apply interior stone originalColour
  exact mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
    (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent))

/-- An apparent eye cannot be an erased exterior point: its nonempty core
boundary and the actual support force that same eye into the region. -/
theorem holds_lift {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {g : TwoEye.Geometry n}
    (interior : SupportInterior region board colour)
    (holds : TwoEye.Holds g colour (restrict region board)) :
    TwoEye.Holds g colour board := by
  have seed := (restrict_colour region board colour g.seed).mp holds.1
  have first := eye_inside region interior holds g.boundary₁ g.neighbour₁
  have second := eye_inside region interior holds g.boundary₂ g.neighbour₂
  refine ⟨seed.2, ?_, ?_, ?_⟩
  · exact holds.2.1.trans (local_group_subset region board colour g.seed seed.1 seed.2)
  · exact (restrict_at region board first).symm.trans holds.2.2.1
  · exact (restrict_at region board second).symm.trans holds.2.2.2

def detected_lift {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity}
    (interior : SupportInterior region board colour)
    (detected : TwoEye.Detected (restrict region board) colour) : TwoEye.Detected board colour :=
  ⟨detected.geometry, holds_lift region interior detected.holds⟩

theorem own_confined {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (confined : Confined region board colour) :
    Confined region (boardAfterPlay board colour played) colour := by
  intro point occupied
  have member : point ∈ stones (boardAfterPlay board colour played) colour :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ point, occupied⟩
  rw [own_stones] at member
  rcases Finset.mem_insert.mp member with same | old
  · exact same ▸ inside
  · exact confined point (Finset.mem_filter.mp old).2

theorem own_supportInterior {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (neighbours : adjacentPoints played ⊆ region)
    (interior : SupportInterior region board colour) :
    SupportInterior region (boardAfterPlay board colour played) colour := by
  intro point occupied
  have member : point ∈ stones (boardAfterPlay board colour played) colour :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ point, occupied⟩
  rw [own_stones] at member
  rcases Finset.mem_insert.mp member with same | old
  · exact same ▸ neighbours
  · exact interior point (Finset.mem_filter.mp old).2

/-- The local post-move reserve is the actual post-move reserve. -/
theorem own_liberties_exact {n : Nat} (region : Finset (Point n)) (board : Board n)
    (colour : Polarity) (played : Point n) (inside : played ∈ region)
    (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region board colour) (interior : SupportInterior region board colour)
    (empty : board played = none) (capacity : RegionSparse.Capacity region board colour) :
    LibertyReserve.liberties (boardAfterPlay (restrict region board) colour played) played =
      LibertyReserve.liberties (boardAfterPlay board colour played) played := by
  rw [← RegionSparse.own_board_exact region board colour played inside neighbours confined empty capacity]
  have occupied := TwoEye.Growth.placed_survives board colour played
  apply confined_liberties region (boardAfterPlay board colour played) colour played occupied
    (own_confined region board colour played inside confined)
  intro stone member
  exact own_supportInterior region board colour played neighbours interior stone
    (groupAt_member_colour occupied member)

/-- This is the original native reply, using the reserve generated on its
regional restriction and the original frame's retained history. -/
def playReply {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (played : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (history : HistoryBound frame colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay (restrict region frame.visible.board) colour played) played).card) :
    ScoringReply frame :=
  let originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  RegionAction.playReply frame colour played playing owned originalEmpty history (by
    rw [← own_liberties_exact region frame.visible.board colour played inside neighbours
      confined interior originalEmpty capacity]
    exact reserve)

theorem playReply_exact {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (played : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (history : HistoryBound frame colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay (restrict region frame.visible.board) colour played) played).card) :
    let reply := playReply region frame colour played playing owned inside neighbours
      confined interior empty history capacity reserve
    restrict region reply.target.visible.board =
        boardAfterPlay (restrict region frame.visible.board) colour played ∧
      reply.target.positionHistory = frame.positionHistory ++ [reply.target.visible.situation] ∧
      HistoryBound reply.target colour ∧
      Confined region reply.target.visible.board colour ∧
      SupportInterior region reply.target.visible.board colour := by
  let reply := playReply region frame colour played playing owned inside neighbours
    confined interior empty history capacity reserve
  have originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  refine ⟨RegionSparse.own_board_exact region frame.visible.board colour played inside neighbours
    confined originalEmpty capacity, nativeStep_positionHistory_eq reply.step, ?_,
    own_confined region frame.visible.board colour played inside confined,
    own_supportInterior region frame.visible.board colour played neighbours interior⟩
  apply historyBound_step history reply.step
  change (stones frame.visible.board colour).card ≤
    (stones (boardAfterPlay frame.visible.board colour played) colour).card
  rw [own_stones_card originalEmpty]
  omega

/-- The source single group remains the same tracked group after a local
attached action; membership is lifted before calling the paid native producer. -/
theorem playReply_oneGroup {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (played seed : Point n)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (history : HistoryBound frame colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (reserve : 2 ≤ (LibertyReserve.liberties
      (boardAfterPlay (restrict region frame.visible.board) colour played) played).card)
    (occupied : frame.visible.board seed = some colour)
    (single : OneGroup frame.visible.board colour seed)
    (attached : ∃ stone ∈ groupAt (restrict region frame.visible.board) seed,
      played ∈ adjacentPoints stone) :
    OneGroup (playReply region frame colour played playing owned inside neighbours
      confined interior empty history capacity reserve).target.visible.board colour seed := by
  have originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  apply own_oneGroup occupied single originalEmpty
  obtain ⟨stone, member, adjacent⟩ := attached
  rw [confined_group region frame.visible.board colour seed occupied confined] at member
  exact ⟨stone, member, adjacent⟩

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionLift
