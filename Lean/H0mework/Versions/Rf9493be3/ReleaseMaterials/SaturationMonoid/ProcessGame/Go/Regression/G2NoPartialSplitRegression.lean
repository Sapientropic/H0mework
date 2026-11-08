import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.GeneratedGroupLineage

/-!
# G2 universal no-partial-split regression

The public theorem consumes only an exact reachable `ActualPly`.  Concrete
placement, pass, resignation and whole-capture plies exercise every compiler
move shape without supplying a coherence certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go
namespace G2NoPartialSplitRegression

def law : Law := Law.positionalSuperko 0

def p00 : Point 2 := (0, 0)
def p01 : Point 2 := (0, 1)
def p10 : Point 2 := (1, 0)
def p11 : Point 2 := (1, 1)

def emptyReplay : GeneratedReplay law (Frame.initial 2) [] :=
  .nil (Frame.initial 2)

theorem playTarget_isSome :
    (nativeStep? law emptyReplay.final (.play p00)).isSome = true := by
  decide

def playTarget : Frame 2 :=
  (nativeStep? law emptyReplay.final (.play p00)).get playTarget_isSome

def playPly : GeneratedReplay.ActualPly emptyReplay where
  target := playTarget
  emitted := .play p00
  step := by
    unfold LegalStep playTarget
    exact (Option.some_get playTarget_isSome).symm

theorem play_has_no_partial_group_split :
    IsEmpty (ActualSplitDisposition playPly) :=
  actualPly_noPartialChainSplit playPly

theorem passTarget_isSome :
    (nativeStep? law emptyReplay.final (.pass : Move 2)).isSome = true := by
  decide

def passTarget : Frame 2 :=
  (nativeStep? law emptyReplay.final (.pass : Move 2)).get passTarget_isSome

def passPly : GeneratedReplay.ActualPly emptyReplay where
  target := passTarget
  emitted := .pass
  step := by
    unfold LegalStep passTarget
    exact (Option.some_get passTarget_isSome).symm

theorem pass_has_no_partial_group_split :
    IsEmpty (ActualSplitDisposition passPly) :=
  actualPly_noPartialChainSplit passPly

theorem resignTarget_isSome :
    (nativeStep? law emptyReplay.final (.resign : Move 2)).isSome = true := by
  decide

def resignTarget : Frame 2 :=
  (nativeStep? law emptyReplay.final (.resign : Move 2)).get
    resignTarget_isSome

def resignPly : GeneratedReplay.ActualPly emptyReplay where
  target := resignTarget
  emitted := .resign
  step := by
    unfold LegalStep resignTarget
    exact (Option.some_get resignTarget_isSome).symm

theorem resign_has_no_partial_group_split :
    IsEmpty (ActualSplitDisposition resignPly) :=
  actualPly_noPartialChainSplit resignPly

def capturePrefixMoves : List (Move 2) :=
  [.play p00, .play p01, .play p10]

theorem capturePrefix_isSome :
    (generate? law 2 capturePrefixMoves).isSome = true := by
  decide

def capturePrefix :
    GeneratedReplay law (Frame.initial 2) capturePrefixMoves :=
  (generate? law 2 capturePrefixMoves).get capturePrefix_isSome

theorem captureTarget_isSome :
    (nativeStep? law capturePrefix.final (.play p11)).isSome = true := by
  decide

def captureTarget : Frame 2 :=
  (nativeStep? law capturePrefix.final (.play p11)).get
    captureTarget_isSome

def capturePly : GeneratedReplay.ActualPly capturePrefix where
  target := captureTarget
  emitted := .play p11
  step := by
    unfold LegalStep captureTarget
    exact (Option.some_get captureTarget_isSome).symm

/-- The whole-capture event is covered by the same universal theorem; no
capture set, target board or source-coherence witness enters this mouth. -/
theorem capture_has_no_partial_group_split :
    IsEmpty (ActualSplitDisposition capturePly) :=
  actualPly_noPartialChainSplit capturePly

/-- Public exact-scope consumer: every reachable actual ply uses the same
no-partial-split theorem, independently of the concrete regression scripts. -/
theorem every_actual_ply_has_no_partial_group_split
    {n : Nat} {fixedLaw : Law} {moves : List (Move n)}
    {replay : GeneratedReplay fixedLaw (Frame.initial n) moves}
    (ply : GeneratedReplay.ActualPly replay) :
    IsEmpty (ActualSplitDisposition ply) :=
  actualPly_noPartialChainSplit ply

end G2NoPartialSplitRegression
end Go
end ProcessGame
end SaturationMonoid
