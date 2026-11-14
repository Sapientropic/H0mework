import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginHistory
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RegionLift
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginRegionAction

open RegionProjection

/-- A regional move needs its actual no-suicide condition, not a promise that
every own group will survive the opponent.  Retained past points pay PSK. -/
def reply {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (played : Point n) (virgin : played ∉ seen)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (legal : stoneHasLiberty (boardAfterPlay (restrict region frame.visible.board) colour played) played) :
    ScoringReply frame :=
  let originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  VirginHistory.reply frame colour seen tracked played virgin playing owned originalEmpty (by
    rw [← RegionCapture.liberties_nonempty_iff] at legal ⊢
    rw [RegionLift.own_liberties_exact region frame.visible.board colour played inside neighbours
      confined interior originalEmpty capacity] at legal
    exact legal)

theorem reply_exact {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (seen : Finset (Point n)) (tracked : VirginHistory.Tracked frame colour seen)
    (played : Point n) (virgin : played ∉ seen)
    (playing : frame.visible.status = .playing) (owned : frame.visible.toMove = colour)
    (inside : played ∈ region) (neighbours : adjacentPoints played ⊆ region)
    (confined : Confined region frame.visible.board colour)
    (interior : SupportInterior region frame.visible.board colour)
    (capacity : RegionSparse.Capacity region frame.visible.board colour)
    (empty : restrict region frame.visible.board played = none)
    (legal : stoneHasLiberty (boardAfterPlay (restrict region frame.visible.board) colour played) played) :
    let response := reply region frame colour seen tracked played virgin playing owned inside neighbours
      confined interior capacity empty legal
    restrict region response.target.visible.board =
        boardAfterPlay (restrict region frame.visible.board) colour played ∧
      VirginHistory.Tracked response.target colour (insert played seen) ∧
      Confined region response.target.visible.board colour ∧
      SupportInterior region response.target.visible.board colour := by
  let originalEmpty := (restrict_at region frame.visible.board inside).symm.trans empty
  refine ⟨RegionSparse.own_board_exact region frame.visible.board colour played inside neighbours
    confined originalEmpty capacity, ?_,
    RegionLift.own_confined region frame.visible.board colour played inside confined,
    RegionLift.own_supportInterior region frame.visible.board colour played neighbours interior⟩
  have nativeLegal : stoneHasLiberty (boardAfterPlay frame.visible.board colour played) played := by
    rw [← RegionCapture.liberties_nonempty_iff] at legal ⊢
    rw [RegionLift.own_liberties_exact region frame.visible.board colour played inside neighbours
      confined interior originalEmpty capacity] at legal
    exact legal
  exact VirginHistory.reply_tracked frame colour seen tracked played virgin playing owned originalEmpty nativeLegal

/-- The shared-eye geometry is unchanged.  Its actual core neighbours force
each retained eye into the region, so no erased exterior cell becomes an eye. -/
theorem coalition_holds {n : Nat} (region : Finset (Point n))
    {board : Board n} {colour : Polarity} {g : EyeCoalition.Geometry n}
    (interior : SupportInterior region board colour)
    (holds : EyeCoalition.Holds g colour (restrict region board)) :
    EyeCoalition.Holds g colour board := by
  have core : ∀ point ∈ g.core, board point = some colour := by
    intro point member
    exact ((restrict_colour region board colour point).mp (holds.1 point member)).2
  refine ⟨core, ?_⟩
  intro eye member
  obtain ⟨stone, adjacent⟩ := g.neighbours eye member
  have inside : eye ∈ region := interior stone (core stone (g.boundary eye member adjacent))
    (mem_adjacentPoints_iff_orthogonallyAdjacent.mpr
      (orthogonallyAdjacent_symm (mem_adjacentPoints_iff_orthogonallyAdjacent.mp adjacent)))
  exact (restrict_at region board inside).symm.trans (holds.2 eye member)

def coalitionCertificate {n : Nat} (region : Finset (Point n)) (frame : Frame n)
    (colour : Polarity) (threshold : Int) (interior : SupportInterior region frame.visible.board colour)
    (detected : EyeCoalition.Detected (restrict region frame.visible.board) colour)
    (scoring : ScoringStatus frame)
    (relaxed : acceptsMargin colour threshold (EyeCoalition.bound detected.geometry colour) = true) :
    Certificate colour threshold frame :=
  .eyeCoalition ⟨detected.geometry, coalition_holds region interior detected.holds⟩ scoring relaxed

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VirginRegionAction
