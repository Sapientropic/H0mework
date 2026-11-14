import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.MaterializedStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.CarriedProgram

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

/-- One actual component pays the repeated old-core liberty obligations. -/
structure Reserve (board : Board 19) where
  component : Finset (Point 19)
  generated : component = groupAt board (1,1)
  occupied : board (1,1) = some .positive
  two : 2 ≤ ((component.biUnion adjacentPoints).filter (fun point => board point = none)).card

def reserve? (board : Board 19) : Option (Reserve board) :=
  if occupied : board (1,1) = some .positive then
    let component := groupAt board (1,1)
    if two : 2 ≤ ((component.biUnion adjacentPoints).filter (fun point => board point = none)).card then
      some ⟨component, rfl, occupied, two⟩
    else none
  else none

theorem Reserve.saved {board : Board 19} (reserve : Reserve board)
    {stones : Finset (Point 19)} {completion : Point 19}
    (included : ∀ stone ∈ stones, stone ≠ completion → stone ∈ reserve.component) :
    ∀ stone ∈ stones, stone ≠ completion → 2 ≤ (LibertyReserve.liberties board stone).card := by
  intro stone member different
  have inside : stone ∈ groupAt board (1,1) := by
    rw [← reserve.generated]
    exact included stone member different
  unfold LibertyReserve.liberties
  rw [groupAt_eq_of_mem reserve.occupied inside, ← reserve.generated]
  exact reserve.two

theorem tracked_after_other {frame target : Frame 19} {seen : Finset (Point 19)}
    (tracked : VirginHistory.Tracked frame .positive seen)
    (opponent : frame.visible.toMove = Polarity.positive.other)
    {move : Move 19} (scoring : move ≠ .resign)
    (step : LegalStep (Law.positionalSuperko 0) frame move target) :
    VirginHistory.Tracked target .positive seen := by
  have next := VirginHistory.step tracked scoring step
  cases move <;> simpa only [VirginHistory.nextSeen, opponent, Polarity.other_ne, ↓reduceIte] using next

/-- The same original action transports the already retained history carrier. -/
def chooseTracked? (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) (point : Point 19)
    (read : (target : Frame 19) → VirginHistory.Tracked target .positive (insert point seen) →
      Option (Certificate .positive (-345) target)) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  have trackedMaterial : VirginHistory.Tracked material .positive seen := by rw [same]; exact tracked
  if owned : material.visible.toMove = .positive then
    match generated : MaterializedStep.step? (Law.positionalSuperko 0) material (.play point) with
    | none => none
    | some raw =>
        let target := BufferedReplay.restore (BufferedReplay.capture raw)
        have targetSame : target = raw := BufferedReplay.restore_capture raw
        let reply : ScoringReply material :=
          ⟨.play point, target, by simp, by
            rw [targetSame]
            exact (MaterializedStep.step_eq (Law.positionalSuperko 0) material (.play point)).symm.trans generated⟩
        have next : VirginHistory.Tracked target .positive (insert point seen) := by
          have carried := VirginHistory.step trackedMaterial reply.notResign reply.step
          simpa only [VirginHistory.nextSeen, if_pos owned] using carried
        (read target next).map (fun child => same ▸ .choose owned reply child)
  else none

def allTracked? (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen)
    (read : (observed : Move 19) → (target : Frame 19) → VirginHistory.Tracked target .positive seen →
      Option (Certificate .positive (-345) target)) : Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove = Polarity.positive.other then
      let expansion := MaterializedStep.scoring frame
      have exactExpansion : expansion = scoringExpansion frame := MaterializedStep.scoring_eq frame
      (Corridor.collect? expansion.length (fun port => Certificate .positive (-345) (expansion.get port).2)
        (fun port =>
          have member : expansion.get port ∈ scoringExpansion frame :=
            exactExpansion ▸ List.get_mem expansion port
          have native := mem_scoringExpansion_iff.mp member
          read (expansion.get port).1 (expansion.get port).2
            (tracked_after_other tracked opponent native.2 native.1))).map
        (fun children => .all playing (by rw [opponent]; exact Polarity.other_ne _) (by
          rw [← exactExpansion]
          exact children))
    else none
  else none

def sealAgainstOthers? (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen)
    (point : Point 19) (geometry : VitalChambers.Geometry 19)
    (exception : (target : Frame 19) → VirginHistory.Tracked target .positive seen →
      Option (Certificate .positive (-345) target)) : Option (Certificate .positive (-345) frame) :=
  if opponent : frame.visible.toMove = Polarity.positive.other then
    if passes : frame.visible.consecutivePasses = 0 then
      (reserve? frame.visible.board).bind (fun reserve =>
        (VitalBirthCapturing.candidate? frame .positive (-345) seen point geometry).bind (fun candidate =>
          if same : candidate.plan.point = point then
            if included : ∀ stone ∈ candidate.plan.geometry.core,
                stone ≠ candidate.plan.point → stone ∈ reserve.component then
              ExceptionalAll.certificateWithStep? frame (.play point)
                (fun _move _target scoring step avoided =>
                  VitalBirthCapturing.afterOpponent seen tracked candidate.plan
                    (reserve.saved included) candidate.virgin opponent passes scoring step
                    (by simpa only [same] using avoided) (-345) candidate.accepted)
                (fun target step => exception target (tracked_after_other tracked opponent (by simp) step))
            else none
          else none))
    else none
  else none


end SaturationMonoid.ProcessGame.Go.CriticalKomi.CarriedProgram
