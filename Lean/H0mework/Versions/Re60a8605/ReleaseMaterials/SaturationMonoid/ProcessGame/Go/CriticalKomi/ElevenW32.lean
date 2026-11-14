import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.HookSourceGeometry
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirthRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.CarriedProgram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW32

open CarriedProgram

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset

def columnRange (column first past : Nat) : Finset (Point 19) :=
  Finset.univ.filter (fun point => point.2.val = column ∧ first ≤ point.1.val ∧ point.1.val < past)

def wall (row : Nat) : Finset (Point 19) :=
  HookSource.core ∪ columnRange 1 1 (row + 1)

/-- The bottom edge is used only at actual row 18. The top room and the
left-column room have disjoint boundaries on the original board. -/
def geometry? (row divider : Nat) : Option (VitalChambers.Geometry 19) :=
  let stones := insert (Corridor.point 0 divider) (wall row)
  if row = 18 then
    VitalChambers.geometry? stones {Corridor.rowRange 0 0 divider, columnRange 0 2 19}
  else
    VitalChambers.geometry? (insert (Corridor.point row 0) stones)
      {Corridor.rowRange 0 0 divider, columnRange 0 2 row}

/-- Geometry compilation has no source board, strategy, or future coverage.
The resulting book is reused by every actual port of one source program. -/
structure Geometries where
  rows : List (Option (VitalChambers.Geometry 19) × Option (VitalChambers.Geometry 19))

def compileGeometries (count : Nat) : Geometries :=
  ⟨(List.range count).map (fun row => (geometry? row 2, geometry? row 3))⟩

def Geometries.get? (book : Geometries) (row divider : Nat) : Option (VitalChambers.Geometry 19) :=
  let pair := book.rows.getD row (none, none)
  if divider = 2 then pair.1 else if divider = 3 then pair.2 else none

def candidate? (frame : Frame 19) (seen : Finset (Point 19)) (reserve : Reserve frame.visible.board)
    (point : Point 19) (geometry : VitalChambers.Geometry 19) :
    Option (VitalBirthRecognize.SavedCandidate frame .positive (-345) seen) :=
  if virgin : point ∉ seen then
    if empty : frame.visible.board point = none then
      if holds : VitalChambers.Holds geometry .positive (Board.set frame.visible.board point (some .positive)) then
        if participates : point ∈ geometry.core then
          let plan : VitalBirth.Plan frame.visible.board .positive := ⟨point, empty, ⟨geometry, holds⟩, participates⟩
          if included : ∀ stone ∈ geometry.core, stone ≠ point → stone ∈ reserve.component then
            if accepted : acceptsMargin .positive (-345) (VitalChambers.bound geometry .positive) = true then
              some ⟨⟨plan, virgin, accepted⟩, reserve.saved included⟩
            else none
          else none
        else none
      else none
    else none
  else none

/-- Both top plans consume the same current component and retained history. -/
def miaiWith? (book : Geometries) (row : Nat) (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) : Option (Certificate .positive (-345) frame) :=
  (book.get? row 2).bind (fun leftGeometry =>
    (book.get? row 3).bind (fun rightGeometry =>
      Corridor.leaf? leftGeometry frame <|> Corridor.leaf? rightGeometry frame <|>
        if playing : frame.visible.status = .playing then
          if opponent : frame.visible.toMove = Polarity.positive.other then
            if passes : frame.visible.consecutivePasses = 0 then
              (reserve? frame.visible.board).bind (fun reserve =>
                (candidate? frame seen reserve (0,2) leftGeometry).bind (fun left =>
                  (candidate? frame seen reserve (0,3) rightGeometry).bind (fun right =>
                    if distinct : left.plan.point ≠ right.plan.point then
                      some (VitalBirth.miaiCertificate seen tracked left.plan right.plan distinct
                        left.saved right.saved left.virgin right.virgin playing opponent passes
                        (-345) left.accepted right.accepted)
                    else none)))
            else none
          else none
        else none))

/-- Only the actually occupied current seal extends the floor. -/
def oneRoomWith? (book : Geometries) (row divider : Nat) (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) : Option (Certificate .positive (-345) frame) :=
  (book.get? row divider).bind (fun geometry =>
    if _edge : row = 18 then Corridor.leaf? geometry frame
    else if _before : row < 18 then
      Corridor.leaf? geometry frame <|>
        sealAgainstOthers? frame seen tracked (Corridor.point row 0) geometry
          (fun target next =>
            let point := Corridor.point (row + 1) 1
            chooseTracked? target seen next point (fun final carried =>
              oneRoomWith? book (row + 1) divider final (insert point seen) carried))
    else none)
termination_by 18 - row
decreasing_by omega

/-- Preblocked future cells are actual events whose branch seals immediately;
only current-seal occupation extends the same source program. -/
def growthWith? (book : Geometries) (row : Nat) (frame : Frame 19) (seen : Finset (Point 19))
    (tracked : VirginHistory.Tracked frame .positive seen) : Option (Certificate .positive (-345) frame) :=
  if _edge : row = 18 then miaiWith? book row frame seen tracked
  else if _before : row < 18 then
    allTracked? frame seen tracked (fun observed target next =>
      if observed = .play (Corridor.point row 0) then
        let point := Corridor.point (row + 1) 1
        chooseTracked? target seen next point (fun final carried =>
          growthWith? book (row + 1) final (insert point seen) carried)
      else if observed ∈ ([.play (0,0), .play (0,2), .play (0,3)] : List (Move 19)) then
        let divider := if observed = .play (0,2) then 3 else 2
        let point := Corridor.point 0 divider
        chooseTracked? target seen next point (fun final carried =>
          oneRoomWith? book row divider final (insert point seen) carried)
      else
        let point := Corridor.point row 0
        chooseTracked? target seen next point (fun final carried =>
          miaiWith? book row final (insert point seen) carried))
  else none
termination_by 18 - row
decreasing_by omega

def miai? (row : Nat) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  miaiWith? (compileGeometries 19) row frame (CoalitionBirth.retained frame .positive)
    (CoalitionBirth.retained_tracked frame .positive)

def oneRoom? (row divider : Nat) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  oneRoomWith? (compileGeometries 19) row divider frame (CoalitionBirth.retained frame .positive)
    (CoalitionBirth.retained_tracked frame .positive)

def growth? (row : Nat) (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  growthWith? (compileGeometries 19) row frame (CoalitionBirth.retained frame .positive)
    (CoalitionBirth.retained_tracked frame .positive)

def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  let book := compileGeometries 19
  let seen := CoalitionBirth.retained frame .positive
  chooseTracked? frame seen (CoalitionBirth.retained_tracked frame .positive) (3,1)
    (fun target tracked => growthWith? book 3 target (insert (3,1) seen) tracked)

end SaturationMonoid.ProcessGame.Go.CriticalKomi.ElevenW32
