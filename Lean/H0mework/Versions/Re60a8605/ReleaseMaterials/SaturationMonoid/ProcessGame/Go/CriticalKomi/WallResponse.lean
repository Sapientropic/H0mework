import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourVital
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RoomSplit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.WallResponse

def leftGeometry? : Option (VitalChambers.Geometry 19) :=
  VitalChambers.geometry? (insert (0, 1) (insert (0, 3) (Corridor.floor 5))) {{(0, 0)}, {(0, 2)}}

def leftThreat? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  leftGeometry?.bind (fun geometry =>
    Corridor.sealAgainstOthers? frame (0, 1) geometry
      (fun target => Corridor.choose? target (1, 6) (Corridor.certificate? 6 3)))

/-- The second White event determines whether to seal the five-point room or
create the left three-point threat. Future floor occupancy is never guessed. -/
def earlySeal? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  Corridor.choose? frame (1, 5) (fun next =>
    Corridor.all? next (fun observed target =>
      if observed = .play (0, 5) then Corridor.choose? target (0, 3) leftThreat?
      else RoomSplit.seal? target))

def future : Finset (Point 19) := Corridor.rowRange 0 0 19 ∪ Corridor.rowRange 1 4 19

def Source (frame : Frame 19) : Prop :=
  frame.visible.status = .playing ∧ frame.visible.toMove = .positive ∧
  (∀ point ∈ Corridor.floor 3, frame.visible.board point = some .positive) ∧
  (∀ point ∈ future, point ≠ (0, 0) → frame.visible.board point = none) ∧
  (frame.visible.board (0, 0) = none ∨ frame.visible.board (0, 0) = some .negative) ∧
  Disjoint future (CoalitionBirth.retained frame .positive)

instance (frame : Frame 19) : Decidable (Source frame) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- All three new White interventions and every old straight-four port belong
to the same original Black wall-extension event. -/
def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if Source frame then
    Corridor.choose? frame (1, 4) (fun next =>
      Corridor.all? next (fun observed target =>
        if observed = .play (0, 1) then Corridor.enter? target 4 2
        else if observed = .play (0, 2) then Corridor.enter? target 4 1
        else if observed = .play (0, 4) then earlySeal? target
        else StraightFourVital.seal? target))
  else none

def recognize? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  certificate? frame <|>
    if frame.visible.toMove = .positive ∧
        (∀ point ∈ Corridor.floor 4, frame.visible.board point = some .positive) then
      if frame.visible.board (0, 1) = some .negative then Corridor.enter? frame 4 2
      else if frame.visible.board (0, 2) = some .negative then Corridor.enter? frame 4 1
      else none
    else none

end SaturationMonoid.ProcessGame.Go.CriticalKomi.WallResponse
