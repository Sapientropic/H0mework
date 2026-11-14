import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChambers
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.CriticalKomi.SourceLeaf

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChamberControl

def core : List (Point 19) := [(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (0, 2), (0, 5)]

def moves (colour : Polarity) : List (Move 19) :=
  match colour with
  | .positive => (core.flatMap (fun point => [.play point, .pass])).dropLast
  | .negative => core.flatMap (fun point => [.pass, .play point])

def run (colour : Polarity) : IO Unit := do
  let started ← IO.monoMsNow
  let some replay := BufferedReplay.generate? (Law.positionalSuperko 0) 19 (moves colour)
    | throw (IO.userError "original two-domino source replay failed")
  let frame := BufferedReplay.restore (BufferedReplay.capture replay.final)
  if playing : frame.visible.status = .playing then
    let threshold := if colour = .positive then (-346 : Int) else 345
    unless (SourceLeaf.twoEyeAnswer? frame threshold (.inl playing)).isNone &&
        (SourceLeaf.coalitionAnswer? frame threshold (.inl playing)).isNone do
      throw (IO.userError "two-domino source already has the old singleton-eye closure")
    let detected : VitalChambers.Detected frame.visible.board colour ←
      match side : colour, settle? frame threshold (.inl playing) with
      | .positive, some (.black (.vitalChambers detected _ _)) => pure (side.symm ▸ detected)
      | .negative, some (.white (.vitalChambers detected _ _)) => pure (side.symm ▸ detected)
      | _, _ => throw (IO.userError "production source did not emit the new vital-chamber certificate")
    let g := detected.geometry
    unless g.core.card == 8 && g.rooms.card == 2 && (VitalChambers.points g).card == 8 do
      throw (IO.userError "unexpected current core/region/area reader")
    IO.println s!"recognized {repr colour}: eight core stones and two disjoint two-cell vital chambers"
    (← IO.getStdout).flush
    if opponent : frame.visible.toMove = colour.other then
      let expansion := scoringExpansion frame
      for port in List.finRange expansion.length do
        let facts := mem_scoringExpansion_iff.mp (List.get_mem expansion port)
        have _preserved := VitalChambers.opponent_legalStep_preserves detected.holds opponent facts.2 facts.1
        unless decide (VitalChambers.Holds g colour (expansion.get port).2.visible.board) do
          throw (IO.userError "original opponent step destroyed the generated chamber invariant")
      let damaged := Board.set frame.visible.board (1, 0) none
      unless !(decide (VitalChambers.Holds g colour damaged)) do
        throw (IO.userError "missing core negative control was accepted")
      let some invadedRaw := nativeStep? (Law.positionalSuperko 0) frame (.play (0, 0))
        | throw (IO.userError "first chamber invasion should be an actual legal move")
      let invaded := BufferedReplay.restore (BufferedReplay.capture invadedRaw)
      let some invadedSource := VitalChambers.recognize? invaded.visible.board colour
        | throw (IO.userError "the source reader discarded a partly invaded chamber")
      unless invadedSource.geometry.rooms.card == 2 do
        throw (IO.userError "the invasion was confused with an empty-component split")
      if inside : VitalChambers.invariant g colour invaded = true then
        if owned : invaded.visible.toMove = colour then
          if active : invaded.visible.status = .playing then
            let reply := (VitalChambers.closure g colour).ownReply invaded inside owned active
            unless nativeStep? (Law.positionalSuperko 0) invaded reply.move == some reply.target &&
                VitalChambers.invariant g colour reply.target do
              throw (IO.userError "the original survival compiler did not generate a legal preserving reply")
          else throw (IO.userError "one invasion prematurely terminated the source")
        else throw (IO.userError "the observed invasion did not yield the actual beneficiary turn")
      else throw (IO.userError "the original invasion left the generated invariant")
      let some passed := nativeStep? (Law.positionalSuperko 0) invaded .pass
        | throw (IO.userError "the source-preserving original pass was rejected")
      unless (nativeStep? (Law.positionalSuperko 0) passed (.play (0, 1))).isNone do
        throw (IO.userError "the opponent illegally filled the last chamber liberty")
      IO.println s!"all {expansion.length} original opponent ports preserve the source; bound={VitalChambers.bound g colour}; {(← IO.monoMsNow)-started} ms"
    else throw (IO.userError "wrong original opponent turn")
  else throw (IO.userError "two-domino source is not playing")

end SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChamberControl

def main (args : List String) : IO Unit :=
  SaturationMonoid.ProcessGame.Go.CriticalKomi.VitalChamberControl.run
    (if args == ["white"] then .negative else .positive)
