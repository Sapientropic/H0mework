import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.ChamberStrategy

/-!
Adjacent source cells around an already detected living group generate a sealed
two-point chamber.  Its board, turn, pass and history tests select a native seal
or the complete opponent-response certificate.  Threshold weakening preserves
the original finite strategy nodes.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi

namespace Certificate

def weaken {n : Nat} {side : Polarity} {threshold : Int} {frame : Frame n}
    (certificate : Certificate side threshold frame) (target : Int)
    (relaxed : acceptsMargin side target threshold = true) : Certificate side target frame :=
  match certificate with
  | .terminal finished accepted =>
      .terminal finished (acceptsMargin_trans side target threshold _ relaxed accepted)
  | .twoEye detected scoring accepted =>
      .twoEye detected scoring (acceptsMargin_trans side target threshold _ relaxed accepted)
  | .twoEyeFamily detected scoring accepted =>
      .twoEyeFamily detected scoring (acceptsMargin_trans side target threshold _ relaxed accepted)
  | .eyeCoalition detected scoring accepted =>
      .eyeCoalition detected scoring (acceptsMargin_trans side target threshold _ relaxed accepted)
  | .vitalChambers detected scoring accepted =>
      .vitalChambers detected scoring (acceptsMargin_trans side target threshold _ relaxed accepted)
  | .choose owned reply child => .choose owned reply (child.weaken target relaxed)
  | .all playing opponent children =>
      -- The recursive call needs the original child Frame at runtime. Share
      -- that enumeration across ports, including when the threshold is unchanged.
      let delayed : Thunk (List (Move n × Frame n)) := ⟨fun _ => scoringExpansion frame⟩
      .all playing opponent (fun port =>
        let expansion := delayed.get
        @weaken n side threshold (expansion.get port).2 (children port) target relaxed)

end Certificate

namespace ChamberRecognize

/-- The second point comes from the first point's original adjacency list. -/
def geometry? {n : Nat} (g : TwoEye.Geometry n) (first : Point n)
    (second : {point : Point n // point ∈ adjacentPointList first}) :
    Option (TwoPointChamber.Geometry g) :=
  if shape : first ≠ second.1 ∧
      adjacentPoints first ⊆ insert second.1 g.core ∧
      adjacentPoints second.1 ⊆ insert first g.core ∧
      TwoEye.Growth.Attached g first ∧ TwoEye.Growth.Attached g second.1 ∧
      first ≠ g.eye₁ ∧ first ≠ g.eye₂ ∧ second.1 ≠ g.eye₁ ∧ second.1 ≠ g.eye₂ then by
    rcases shape with ⟨distinct, boundaryFirst, boundarySecond, attachedFirst, attachedSecond,
      firstEye₁, firstEye₂, secondEye₁, secondEye₂⟩
    exact some {
      first := first
      second := second.1
      distinct := distinct
      adjacent := by simpa only [adjacentPoints, List.mem_toFinset] using second.2
      boundaryFirst := boundaryFirst
      boundarySecond := boundarySecond
      attachedFirst := attachedFirst
      attachedSecond := attachedSecond
      firstEye₁ := firstEye₁
      firstEye₂ := firstEye₂
      secondEye₁ := secondEye₁
      secondEye₂ := secondEye₂
    }
  else none

def fromChamber? {n : Nat} {g : TwoEye.Geometry n} (chamber : TwoPointChamber.Geometry g)
    (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing) (inside : TwoEye.Holds g colour frame.visible.board)
    (relaxed : acceptsMargin colour threshold (TwoPointChamber.bound g colour) = true) :
    Option (Certificate colour threshold frame) :=
  if secondEmpty : frame.visible.board chamber.second = none then
    if owned : frame.visible.toMove = colour then
      if first : frame.visible.board chamber.first = none ∨
          frame.visible.board chamber.first = some colour.other then
        if secondVirgin : TwoEye.Growth.Virgin g colour chamber.second frame.positionHistory then
          some ((TwoPointChamber.sealCertificate chamber frame playing owned inside first
            secondEmpty secondVirgin).weaken threshold relaxed)
        else none
      else none
    else
      if passes : frame.visible.consecutivePasses = 0 then
        if firstEmpty : frame.visible.board chamber.first = none then
          if firstVirgin : TwoEye.Growth.Virgin g colour chamber.first frame.positionHistory then
            if secondVirgin : TwoEye.Growth.Virgin g colour chamber.second frame.positionHistory then
              have opponent : frame.visible.toMove = colour.other := by
                cases colour <;> cases toMove : frame.visible.toMove <;> simp_all
              some ((TwoPointChamber.opponentCertificate chamber frame playing inside opponent
                passes firstEmpty secondEmpty firstVirgin secondVirgin).weaken threshold relaxed)
            else none
          else none
        else none
      else none
  else none

/-- Reject an insufficient area bound before scanning any candidate pair. -/
def fromGroup? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing) (g : TwoEye.Geometry n)
    (inside : TwoEye.Holds g colour frame.visible.board) :
    Option (Certificate colour threshold frame) :=
  if relaxed : acceptsMargin colour threshold (TwoPointChamber.bound g colour) = true then
    (allPoints n).findSome? (fun first =>
      (adjacentPointList first).attach.findSome? (fun second =>
        match geometry? g first second with
        | none => none
        | some chamber => fromChamber? chamber frame colour threshold playing inside relaxed))
  else none

def fromFamily? {n : Nat} (frame : Frame n) (colour : Polarity) (threshold : Int)
    (playing : frame.visible.status = .playing)
    (detected : TwoEyeFamily.Detected frame.visible.board colour) :
    Option (Certificate colour threshold frame) :=
  detected.family.attach.findSome? (fun geometry =>
    fromGroup? frame colour threshold playing geometry.1 (detected.holds geometry.1 geometry.2))

end ChamberRecognize

end SaturationMonoid.ProcessGame.Go.CriticalKomi
