import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.RoomSplit
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CarriedProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW02

open CarriedProgram

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def geometry? (column : Nat) (foot : HookSource.Foot) : Option (VitalChambers.Geometry 19) :=
  let wall := foot.core ∪ Corridor.floor column
  if column = 18 then
    VitalChambers.geometry? wall {Corridor.rowRange 0 0 19, {foot.eye}}
  else
    VitalChambers.geometry? (insert (Corridor.point 0 column) wall)
      {Corridor.rowRange 0 0 column, {foot.eye}}

/-- The two fixed lower completions share compiled geometry across actual ports. -/
structure Geometries where
  columns : List (Option (VitalChambers.Geometry 19) × Option (VitalChambers.Geometry 19))

def compileGeometries (count : Nat) : Geometries :=
  ⟨(List.range count).map (fun column => (geometry? column .left, geometry? column .right))⟩

def Geometries.get? (book : Geometries) (column : Nat) (foot : HookSource.Foot) :
    Option (VitalChambers.Geometry 19) :=
  let pair := book.columns.getD column (none, none)
  match foot with
  | .left => pair.1
  | .right => pair.2

def candidate? (frame : Frame 19) (seen : Finset (Point 19))
    (reserve : Reserve frame.visible.board) (foot : HookSource.Foot) (geometry : VitalChambers.Geometry 19) :
    Option (RoomSplit.Capturing.SavedCandidate frame seen) :=
  (VitalBirthCapturing.candidate? frame .positive (-345) seen foot.point geometry).bind (fun candidate =>
    if included : ∀ stone ∈ candidate.plan.geometry.core,
        stone ≠ candidate.plan.point → stone ∈ reserve.component then
      some ⟨candidate, reserve.saved included⟩
    else none)

/-- Each lower completion may capture its occupied singleton room. Both
plans are checked on the same current frame before the next opponent event. -/
def miaiWith? (book : Geometries) (column : Nat) (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) : Option (Certificate .positive (-345) frame) :=
  if playing : frame.visible.status = .playing then
    if opponent : frame.visible.toMove = Polarity.positive.other then
      if passes : frame.visible.consecutivePasses = 0 then
        (book.get? column .left).bind (fun leftGeometry =>
          (book.get? column .right).bind (fun rightGeometry =>
            (reserve? frame.visible.board).bind (fun reserve =>
              (candidate? frame seen reserve .left leftGeometry).bind (fun left =>
                (candidate? frame seen reserve .right rightGeometry).bind (fun right =>
            if distinct : left.plan.point ≠ right.plan.point then
              some (RoomSplit.Capturing.miai seen tracked
                left right distinct playing opponent passes)
            else none)))))
      else none
    else none
  else none

/-- One actual lower eye supports the top room while only current-seal
occupation advances the floor. The physical right edge closes column 18. -/
def oneEyeWith? (book : Geometries) (column : Nat) (foot : HookSource.Foot) (frame : Frame 19)
    (seen : Finset (Point 19)) (tracked : VirginHistory.Tracked frame .positive seen) :
    Option (Certificate .positive (-345) frame) :=
  (book.get? column foot).bind (fun geometry =>
    if _edge : column = 18 then Corridor.leaf? geometry frame
    else if _before : column < 18 then
      Corridor.leaf? geometry frame <|>
        CarriedProgram.sealAgainstOthers? frame seen tracked (Corridor.point 0 column) geometry
          (fun target next =>
            let point := Corridor.point 1 (column + 1)
            chooseTracked? target seen next point (fun final carried =>
              oneEyeWith? book (column + 1) foot final (insert point seen) carried))
    else none)
termination_by 18 - column
decreasing_by omega

/-- A source-fixed fork: a seal invasion extends; a lower-point invasion
gives the other actual eye; every other event seals and leaves both captures. -/
def forkWith? (book : Geometries) (column : Nat) (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) : Option (Certificate .positive (-345) frame) :=
  if _edge : column = 18 then miaiWith? book column frame seen tracked
  else if _before : column < 18 then
    allTracked? frame seen tracked (fun observed target next =>
      if observed = .play (Corridor.point 0 column) then
        let point := Corridor.point 1 (column + 1)
        chooseTracked? target seen next point (fun final carried =>
          forkWith? book (column + 1) final (insert point seen) carried)
      else if observed = .play (3,0) then
        chooseTracked? target seen next (3,2) (fun final carried =>
          oneEyeWith? book column .right final (insert (3,2) seen) carried)
      else if observed = .play (3,2) then
        chooseTracked? target seen next (3,0) (fun final carried =>
          oneEyeWith? book column .left final (insert (3,0) seen) carried)
      else
        let point := Corridor.point 0 column
        chooseTracked? target seen next point (fun final carried =>
          miaiWith? book column final (insert point seen) carried))
  else none
termination_by 18 - column
decreasing_by omega

def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let book := compileGeometries 19
  let seen := CoalitionBirth.retained frame .positive
  chooseTracked? frame seen (CoalitionBirth.retained_tracked frame .positive) (3,1)
    (fun target tracked => forkWith? book 3 target (insert (3,1) seen) tracked)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW02
