import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StrategyCertificate
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthCapturing
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ExceptionalAll

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.RoomSplit

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def bottom : Finset (Point 19) := {(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5)}
def core : Finset (Point 19) := insert (0, 5) bottom
def roomPoints : List (Point 19) := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4)]
def room : Finset (Point 19) := roomPoints.toFinset

def emptyPoints (board : Board 19) : List (Point 19) :=
  roomPoints.filter (fun point => board point == none)

def Layout (board : Board 19) : Prop :=
  (∀ point ∈ core, board point = some .positive) ∧
  (∀ point ∈ room, board point ≠ some .positive) ∧
  board (0, 4) = some .negative

instance (board : Board 19) : Decidable (Layout board) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The White source reads only the current sealed room, its floor and the
original timing. Native replies below continue to read the complete history. -/
def Source (frame : Frame 19) : Prop :=
  frame.visible.status = .playing ∧ frame.visible.toMove = .negative ∧
  frame.visible.consecutivePasses = 0 ∧ Layout frame.visible.board ∧
  3 ≤ (emptyPoints frame.visible.board).length

instance (frame : Frame 19) : Decidable (Source frame) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

def separator? (board : Board 19) : Option (Point 19) :=
  match emptyPoints board with
  | first :: second :: remaining =>
      if remaining.isEmpty then some (if first == (0, 0) then second else first)
      else some second
  | _ => none

def splitGeometry? (column : Fin 19) : Option (VitalChambers.Geometry 19) :=
  VitalChambers.geometry? (insert (0, column) core)
    {room.filter (fun point => point.2 < column), room.filter (fun point => column < point.2)}

/-- The three source geometries are shared by all original opponent ports. -/
def geometries : List (Fin 19 × VitalChambers.Geometry 19) :=
  ([1, 2, 3] : List (Fin 19)).filterMap (fun column =>
    (splitGeometry? column).map (fun geometry => (column, geometry)))

private def reply? (frame : Frame 19) (point : Point 19) : Option (ScoringReply frame) :=
  match generated : nativeStep? (Law.positionalSuperko 0) frame (.play point) with
  | none => none
  | some raw =>
      let target := BufferedReplay.restore (BufferedReplay.capture raw)
      have same : target = raw := BufferedReplay.restore_capture raw
      some ⟨.play point, target, by simp, by rw [same]; exact generated⟩

/-- Choose the separator from the already observed empty points. Every capture
and the full PSK guard belong to this original Black reply. -/
@[noinline] def response? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if owned : material.visible.toMove = .positive then
    if Layout material.visible.board then
      (separator? material.visible.board).bind (fun point =>
        (geometries.find? (fun entry => entry.1 == point.2)).bind (fun entry =>
          (reply? material point).bind (fun reply =>
            if holds : VitalChambers.Holds entry.2 .positive reply.target.visible.board then
              if accepted : acceptsMargin .positive (-345) (VitalChambers.bound entry.2 .positive) = true then
                some (same ▸ .choose owned reply (.vitalChambers ⟨entry.2, holds⟩
                  (nonresigning_step_scoringStatus reply.notResign reply.step) accepted))
              else none
            else none)))
    else none
  else none

structure Prepared (frame : Frame 19) where
  source : Source frame
  seen : Finset (Point 19)
  tracked : VirginHistory.Tracked frame .positive seen
  candidate : VitalBirth.Candidate frame .positive (-345) seen
  saved : VitalBirth.SavedCore candidate.plan

/-- The current second empty point divides the room into two presently
nonempty rooms. SavedCore and VirginHistory are checked at this source. -/
@[noinline] def prepare? (frame : Frame 19) : Option (Prepared frame) :=
  if source : Source frame then
    let seen := CoalitionBirth.retained frame .positive
    (separator? frame.visible.board).bind (fun point =>
      if virgin : point ∉ seen then
        if empty : frame.visible.board point = none then
          (geometries.find? (fun entry => entry.1 == point.2)).bind (fun entry =>
            if holds : VitalChambers.Holds entry.2 .positive
                (Board.set frame.visible.board point (some .positive)) then
              if participates : point ∈ entry.2.core then
                let plan : VitalBirth.Plan frame.visible.board .positive :=
                  ⟨point, empty, ⟨entry.2, holds⟩, participates⟩
                if saved : VitalBirth.SavedCore plan then
                  if accepted : acceptsMargin .positive (-345)
                      (VitalChambers.bound entry.2 .positive) = true then
                    some ⟨source, seen, CoalitionBirth.retained_tracked frame .positive,
                      ⟨plan, virgin, accepted⟩, saved⟩
                  else none
                else none
              else none
            else none)
        else none
      else none)
  else none

namespace Capturing

structure SavedCandidate (frame : Frame 19) (seen : Finset (Point 19)) extends
    VitalBirthCapturing.Candidate frame .positive (-345) seen where
  saved : VitalBirthCapturing.SavedCore plan

def candidate? (frame : Frame 19) (seen : Finset (Point 19)) (point : Point 19) :
    Option (SavedCandidate frame seen) :=
  (geometries.find? (fun entry => entry.1 == point.2)).bind (fun entry =>
    (VitalBirthCapturing.candidate? frame .positive (-345) seen point entry.2).bind (fun candidate =>
      if saved : VitalBirthCapturing.SavedCore candidate.plan then
        some ⟨candidate, saved⟩
      else none))

def miai {frame : Frame 19} (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen)
    (left right : SavedCandidate frame seen) (distinct : left.plan.point ≠ right.plan.point)
    (playing : frame.visible.status = .playing)
    (opponent : frame.visible.toMove = Polarity.positive.other)
    (passes : frame.visible.consecutivePasses = 0) : Certificate .positive (-345) frame :=
  let delayed : Thunk (List (Move 19 × Frame 19)) := ⟨fun _ => scoringExpansion frame⟩
  .all playing (by rw [opponent]; decide) (fun port =>
    let expansion := delayed.get
    let facts := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
    if hitsLeft : (expansion.get port).1 = .play left.plan.point then
      VitalBirthCapturing.afterOpponent seen tracked right.plan right.saved right.virgin
        opponent passes facts.2 facts.1
        (fun hitsRight => distinct (Move.play.inj (hitsLeft.symm.trans hitsRight)))
        (-345) right.accepted
    else
      VitalBirthCapturing.afterOpponent seen tracked left.plan left.saved left.virgin
        opponent passes facts.2 facts.1 hitsLeft (-345) left.accepted)

/-- Two current interior vacancies yield two independently checked capturing
plans. If only one interior vacancy remains, this source reader retains none. -/
@[noinline] def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if playing : material.visible.status = .playing then
    if opponent : material.visible.toMove = Polarity.positive.other then
      if passes : material.visible.consecutivePasses = 0 then
        if Layout material.visible.board ∧ 2 ≤ (emptyPoints material.visible.board).length then
          let seen := CoalitionBirth.retained material .positive
          let candidates := ([(0, 1), (0, 2), (0, 3)] : List (Point 19)).filterMap
            (candidate? material seen)
          match candidates with
          | left :: right :: _ =>
              if distinct : left.plan.point ≠ right.plan.point then
                some (same ▸ miai seen (CoalitionBirth.retained_tracked material .positive)
                  left right distinct playing opponent passes)
              else none
          | _ => none
        else none
      else none
    else none
  else none


end Capturing

/-- The source plan responds uniformly to every original White event except
occupation of its separator. That actual exception is compiled once. -/
@[noinline] def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  (prepare? material).bind (fun prepared =>
    (ExceptionalAll.certificate? material (.play prepared.candidate.plan.point)
      (fun _move _target scoring step avoided =>
        VitalBirth.afterOpponent prepared.seen prepared.tracked prepared.candidate.plan
          prepared.saved prepared.candidate.virgin prepared.source.2.1 prepared.source.2.2.1
          scoring step avoided (-345) prepared.candidate.accepted)
      response?).map (fun certificate => same ▸ certificate)) <|> Capturing.certificate? frame

/-- The preceding Black turn seals at the actual (0,5), then consumes the
five-point-room source and its complete original opponent layer. -/
@[noinline] def seal? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let material := BufferedReplay.restore (BufferedReplay.capture frame)
  have same : material = frame := BufferedReplay.restore_capture frame
  if owned : material.visible.toMove = .positive then
    (reply? material (0, 5)).bind (fun reply =>
      (certificate? reply.target).map (fun child => same ▸ .choose owned reply child))
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.RoomSplit
