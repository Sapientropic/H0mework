import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalitionRecognize
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.BufferedReplay

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalitionControl

/-- Actual source path to the first unresolved reserved-group frontier.
The shared pair of eyes joins two protected components without merging them. -/
def moves19 : List (Move 19) := [
  .play (1, 1), .play (0, 1), .play (2, 3), .play (1, 0),
  .play (1, 2), .play (1, 3), .play (0, 2), .play (2, 2),
  .play (2, 0), .play (2, 1), .play (0, 0), .play (0, 3),
  .play (3, 1), .play (3, 0), .play (3, 2), .play (4, 2),
  .play (4, 0), .play (2, 5), .play (2, 1), .play (5, 2),
  .play (0, 4), .play (4, 1), .play (3, 0), .play (3, 3)
]

def check : IO Unit := do
  let started ← IO.monoMsNow
  match BufferedReplay.generate? (Law.positionalSuperko 0) 19 moves19 with
  | none => throw (IO.userError "coalition frontier did not replay under original rules")
  | some replay =>
      let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
      unless (RegionAction.stones frame.visible.board .positive).card == 12 &&
          (groupAt frame.visible.board (0, 0)).card == 1 &&
          (groupAt frame.visible.board (1, 1)).card == 9 do
        throw (IO.userError "original group partition differs from the source frontier")
      match EyeCoalition.recognize? frame.visible.board .positive with
      | none => throw (IO.userError "source coalition was not recognized")
      | some detected =>
          let g := detected.geometry
          unless g.core.card == 10 && g.eyes == {(0, 1), (1, 0)} &&
              (EyeCoalition.points g).card == 12 do
            throw (IO.userError "the same shared-eye coalition has different source geometry")
          if playing : frame.visible.status = .playing then
            have _guarantee := EyeCoalition.against_every_policy g .positive frame detected.holds
              (.inl playing)
            IO.println "24 original placements: protected core=10 in two distinct groups; shared eyes={(0,1),(1,0)}; area=12"
            IO.println s!"original all-opponent closure margin={EyeCoalition.bound g .positive}"
            unless (SourceLeaf.twoEyeAnswer? frame (-338) (.inl playing)).isNone do
              throw (IO.userError "old individual-eye leaf unexpectedly closed this source")
            match settle? frame (-338) (.inl playing) with
            | some (.black (.eyeCoalition found _ _)) =>
                unless (EyeCoalition.points found.geometry).card == 12 do
                  throw (IO.userError "original leaf consumed a different coalition")
                IO.println "original settle? emits the shared-eye Certificate directly"
            | _ => throw (IO.userError "shared-eye closure is not connected to the original leaf")
            let response := passReply frame playing
            let next := BufferedReplay.restore (BufferedReplay.capture response.target)
            unless (scoringExpansion next).all (fun child => decide (EyeCoalition.Holds g .positive child.2.visible.board)) do
              throw (IO.userError "an actual opponent reply violated the shared-eye closure")
            IO.println s!"after original Black pass: all {(scoringExpansion next).length} native White replies preserve the same coalition"
          else throw (IO.userError "expected playing source")
          let broken : Board 19 := Board.set frame.visible.board (0, 0) none
          match EyeCoalition.recognize? broken .positive with
          | none => pure ()
          | some bad =>
              unless (EyeCoalition.points bad.geometry).card < 12 do
                throw (IO.userError "missing shared protector was ignored")
      IO.println s!"original shared-eye controls: {(← IO.monoMsNow)-started} ms"

end SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalitionControl

def main : IO Unit := SaturationMonoid.ProcessGame.Go.CriticalKomi.EyeCoalitionControl.check
