import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor

/-!
The current left room and two alternative lower bridges generate an original
Black strategy. Actual interference with a bridge enters the existing corridor;
all other original White actions retain the source-generated bridge miai.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridge

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def core : Finset (Point 19) := {(1,0), (1,1), (1,2), (1,3), (2,1), (2,3), (0,2), (3,2)}

def geometry? (bridge : Point 19) : Option (VitalChambers.Geometry 19) :=
  VitalChambers.geometry? (insert bridge core) {{(0,0), (0,1)}, {(2,2)}}

def candidate? (frame : Frame 19) (seen : Finset (Point 19)) (point : Point 19)
    (geometry : VitalChambers.Geometry 19) :
    Option (VitalBirthRecognize.SavedCandidate frame .positive (-345) seen) :=
  if virgin : point ∉ seen then
    if empty : frame.visible.board point = none then
      if holds : VitalChambers.Holds geometry .positive (Board.set frame.visible.board point (some .positive)) then
        if participates : point ∈ geometry.core then
          let plan : VitalBirth.Plan frame.visible.board .positive :=
            ⟨point, empty, ⟨geometry, holds⟩, participates⟩
          if saved : VitalBirth.SavedCore plan then
            if accepted : acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true then
              some ⟨⟨plan, virgin, accepted⟩, saved⟩
            else none
          else none
        else none
      else none
    else none
  else none

def miai? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  (geometry? (3,1)).bind (fun leftGeometry =>
    (geometry? (3,3)).bind (fun rightGeometry =>
      -- An already completed bridge needs no new empty or virgin point.
      Corridor.leaf? leftGeometry frame <|> Corridor.leaf? rightGeometry frame <|>
        if playing : frame.visible.status = .playing then
          if opponent : frame.visible.toMove = Polarity.positive.other then
            if passes : frame.visible.consecutivePasses = 0 then
              let seen := CoalitionBirth.retained frame .positive
              (candidate? frame seen (3,1) leftGeometry).bind (fun left =>
                (candidate? frame seen (3,3) rightGeometry).bind (fun right =>
                  if distinct : left.plan.point ≠ right.plan.point then
                    some (VitalBirth.miaiCertificate seen (CoalitionBirth.retained_tracked frame .positive)
                      left.plan right.plan distinct left.saved right.saved left.virgin right.virgin
                      playing opponent passes (-345) left.accepted right.accepted)
                  else none))
            else none
          else none
        else none))

/-- Only the observed interference with the lower placement or its two bridges
uses the already generated top corridor. Both readers inspect the actual target. -/
def respond? (observed : Move 19) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if observed ∈ ([.play (3,1), .play (3,2), .play (3,3)] : List (Move 19)) then
    Corridor.choose? frame (1,4) (Corridor.certificate? 4 2)
  else Corridor.choose? frame (3,2) miai?

def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  Corridor.choose? frame (0,2) (fun target => Corridor.all? target respond?)

def base : Finset (Point 19) := {(1,0), (1,1), (1,2), (1,3), (2,1), (2,3)}

/-- Inspect the six current Black stones before constructing any opponent ports.
This recognition gate does not constrain the remaining board or retained history. -/
def recognize? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if frame.visible.status = .playing ∧ frame.visible.toMove = .positive ∧
      ∀ point ∈ base, frame.visible.board point = some .positive then
    certificate? frame
  else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenLeftBridge
