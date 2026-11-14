import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalBirth
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.Corridor
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ChamberRecognize

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourVital

def geometry? (divider : Nat) : Option (VitalChambers.Geometry 19) :=
  VitalChambers.geometry? (insert (Corridor.point 0 divider) StraightFourBirth.core)
    {Corridor.rowRange 0 0 divider, Corridor.rowRange 0 (divider + 1) 4}

structure SavedCandidate (frame : Frame 19) (seen : Finset (Point 19)) extends
    VitalBirth.Candidate frame .positive (-345) seen where
  saved : VitalBirth.SavedCore plan

def candidate? (frame : Frame 19) (seen : Finset (Point 19)) (divider : Nat) :
    Option (SavedCandidate frame seen) := do
  let geometry ← geometry? divider
  let point := Corridor.point 0 divider
  if virgin : point ∉ seen then
    if empty : frame.visible.board point = none then
      if holds : VitalChambers.Holds geometry .positive
          (Board.set frame.visible.board point (some .positive)) then
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

/-- Two source-born room completions share one original opponent program. -/
def pureMiai? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if source : StraightFourBirth.Source frame then
    let seen := CoalitionBirth.retained frame .positive
    (candidate? frame seen 1).bind (fun left =>
      (candidate? frame seen 2).bind (fun right =>
        if distinct : left.plan.point ≠ right.plan.point then
          some (VitalBirth.miaiCertificate seen (CoalitionBirth.retained_tracked frame .positive)
            left.plan right.plan distinct left.saved right.saved left.virgin right.virgin
            source.1 (by simpa only [Polarity.other] using source.2.1) source.2.2.1
            (-345) left.accepted right.accepted)
        else none))
  else none

/-- Occupied endpoint rooms are captured by the source plan. The single
exception uses the other actual completion and retains its native target. -/
def capturingMiai? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  if StraightFourBirth.Source frame then
    (geometry? 1).bind (fun left =>
      (geometry? 2).bind (fun right =>
        Corridor.sealAgainstOthers? frame (0, 1) left
          (fun target => Corridor.choose? target (0, 2) (Corridor.leaf? right))))
  else none

def certificate? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  pureMiai? frame <|> capturingMiai? frame <|> (StraightFourBirth.certificate? frame).map
    (fun certificate => certificate.weaken (-345) (by decide))

def seal? (frame : Frame 19) : Option (Certificate .positive (-345) frame) :=
  Corridor.choose? frame (0, 4) certificate?

end SaturationMonoid.ProcessGame.Go.CriticalKomi.StraightFourVital
