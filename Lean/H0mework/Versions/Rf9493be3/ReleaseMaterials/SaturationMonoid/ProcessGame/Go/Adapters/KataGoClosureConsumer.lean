import H0mework.Versions.Rf9493be3.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.Strategy.ClosureGain

/-!
# One-way KataGo observation of generated closure gain

KataGo metadata and scores are external observations attached to an already
compiler-generated obligation update.  `closureReadout` is definitionally the
update's `closureGain`; engine score, win rate, visits and ranking never enter
its formation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

open Obligation

universe u

structure KataGoFixtureMetadata where
  engineVersion : String
  backend : String
  model : String
  queryId : String
  boardSize : Nat
  setupMoves : List String
  rules : String
  komiScaled : Int
  maxVisits : Nat
  rootHash : String
  deriving DecidableEq, Repr

/-- Checked local fixture metadata supplied by the G6 external-engine run. -/
def checkedKoFixtureMetadata : KataGoFixtureMetadata where
  engineVersion := "1.17.2"
  backend := "Metal"
  model := "kata1-b18c384nbt-s9996604416-d4316597426.bin.gz"
  queryId := "g6-ko-setup"
  boardSize := 3
  setupMoves := ["B pass", "W A3", "B A2", "W C3", "B pass", "W B2"]
  rules := "tromp-taylor"
  komiScaled := 0
  maxVisits := 64
  rootHash := "EF1A26A2D96E0694E67438CF80CDD0CA"

structure KataGoCandidateDatum where
  moveLabel : String
  order : Nat
  visits : Nat
  scoreLeadScaled100000000 : Int
  winrateScaled1000000000 : Nat
  deriving DecidableEq, Repr

def checkedC2Datum : KataGoCandidateDatum where
  moveLabel := "C2"
  order := 0
  visits := 33
  scoreLeadScaled100000000 := 533215295
  winrateScaled1000000000 := 893929366

def checkedB3Datum : KataGoCandidateDatum where
  moveLabel := "B3"
  order := 1
  visits := 24
  scoreLeadScaled100000000 := -648616104
  winrateScaled1000000000 := 156402686

/-- One external datum attached to one exact generated update. -/
structure KataGoClosureObservation
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    (update : GeneratedObligationUpdate face ply) where
  fixture : KataGoFixtureMetadata
  external : KataGoCandidateDatum

namespace KataGoClosureObservation

/-- The one-way closure readout ignores every external-engine field. -/
def closureReadout
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    {update : GeneratedObligationUpdate face ply}
    (_observation : KataGoClosureObservation update) : Int :=
  closureGain update

@[simp] theorem closureReadout_eq_generatedClosure
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    {update : GeneratedObligationUpdate face ply}
    (observation : KataGoClosureObservation update) :
    observation.closureReadout = closureGain update :=
  rfl

/-- Changing external data on the same generated update cannot change `C`. -/
theorem externalData_cannot_redefine_closure
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {ply : GeneratedReplay.ActualPly replay}
    {update : GeneratedObligationUpdate face ply}
    (first last : KataGoClosureObservation update) :
    first.closureReadout = last.closureReadout :=
  rfl

end KataGoClosureObservation

/-- One-way agreement: the external engine ranks `strong` above `candidate`,
and independently generated closure gain has the same strict ordering. -/
def ExternalScoreAndClosurePrefer
    {n : Nat} {law : Law} {moves : List (Move n)}
    {replay : GeneratedReplay law (Frame.initial n) moves}
    {Incidence : Type u} [DecidableEq Incidence]
    {face : OpenRelationObligationFace replay Incidence}
    {leftPly rightPly : GeneratedReplay.ActualPly replay}
    {leftUpdate : GeneratedObligationUpdate face leftPly}
    {rightUpdate : GeneratedObligationUpdate face rightPly}
    (strong : KataGoClosureObservation leftUpdate)
    (candidate : KataGoClosureObservation rightUpdate) : Prop :=
  strong.fixture = candidate.fixture ∧
    candidate.external.scoreLeadScaled100000000 <
        strong.external.scoreLeadScaled100000000 ∧
      candidate.closureReadout < strong.closureReadout

end Go
end ProcessGame
end SaturationMonoid
