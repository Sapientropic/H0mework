import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Go.RulesKernel

/-!
# Go area-score readout

Chinese-style area score is a dependent readout of a generated board.  Komi
enters only here; it never affects move generation, history or root authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-- Colours occurring on the boundary of a generated empty region. -/
def borderingColours {n : Nat} (board : Board n)
    (region : Finset (Point n)) : Finset Polarity :=
  Finset.univ.filter (fun colour =>
    ∃ emptyPoint ∈ region, ∃ stone,
      OrthogonallyAdjacent emptyPoint stone ∧ board stone = some colour)

/-- Territory owner of an empty point, when its whole generated region meets
exactly one colour. -/
def territoryOwner? {n : Nat} (board : Board n) (point : Point n) :
    Option Polarity :=
  if board point = none then
    let colours := borderingColours board (emptyRegionAt board point)
    if colours = {Polarity.positive} then
      some .positive
    else if colours = {Polarity.negative} then
      some .negative
    else
      none
  else
    none

/-- Chinese-style area: stones plus empty points in singly-coloured regions. -/
def areaScore {n : Nat} (board : Board n) (colour : Polarity) : Nat :=
  (Finset.univ.filter (fun point =>
    board point = some colour ∨ territoryOwner? board point = some colour)).card

/-- Positive-minus-negative area margin, with komi paid to the negative
polarity. -/
def scoreMargin {n : Nat} (law : Law) (board : Board n) : ℚ :=
  (areaScore board .positive : ℚ) - (areaScore board .negative : ℚ) - law.komi

/-- Terminal score winner; `none` denotes a draw. -/
def scoreWinner? {n : Nat} (law : Law) (board : Board n) : Option Polarity :=
  if 0 < scoreMargin law board then
    some .positive
  else if scoreMargin law board < 0 then
    some .negative
  else
    none

end Go
end ProcessGame
end SaturationMonoid
