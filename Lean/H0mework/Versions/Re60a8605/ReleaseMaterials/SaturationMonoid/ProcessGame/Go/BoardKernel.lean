import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Dist

/-!
# Generated finite Go board

This module contains only the finite board, orthogonal adjacency, executable
component exposure, liberties and capture.  A component is generated from the
board by bounded flood fill; no primitive group identity is installed.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Go

/-- The two unnamed control polarities.  Black/White are presentation gauges,
not primitive players. -/
inductive Polarity where
  | positive
  | negative
  deriving DecidableEq, Repr

instance : Fintype Polarity where
  elems := {.positive, .negative}
  complete := by
    intro polarity
    cases polarity <;> simp

namespace Polarity

/-- Alternation of the two control polarities. -/
def other : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

@[simp] theorem other_positive : other .positive = .negative := rfl

@[simp] theorem other_negative : other .negative = .positive := rfl

@[simp] theorem other_other (polarity : Polarity) : polarity.other.other = polarity := by
  cases polarity <;> rfl

theorem other_ne (polarity : Polarity) : polarity.other ≠ polarity := by
  cases polarity <;> decide

end Polarity

/-- A point of the finite `n × n` board. -/
abbrev Point (n : Nat) := Fin n × Fin n

/-- A board is the finite position field itself. -/
abbrev Board (n : Nat) := Point n → Option Polarity

namespace Board

/-- The empty board. -/
def empty {n : Nat} : Board n := fun _ => none

/-- Functional placement/removal at one point. -/
def set {n : Nat} (board : Board n) (point : Point n)
    (value : Option Polarity) : Board n :=
  Function.update board point value

@[simp] theorem set_self {n : Nat} (board : Board n) (point : Point n)
    (value : Option Polarity) :
    set board point value point = value := by
  simp [set]

@[simp] theorem set_other {n : Nat} (board : Board n) {point other : Point n}
    (value : Option Polarity) (hne : other ≠ point) :
    set board point value other = board other := by
  simp [set, hne]

end Board

/-- Executable faithful row-major board presentation used by repetition
history. -/
abbrev BoardSignature (_n : Nat) := List (List (Option Polarity))

/-- Row-major finite presentation of a board. -/
def boardSignature {n : Nat} (board : Board n) : BoardSignature n :=
  List.ofFn (fun row : Fin n =>
    List.ofFn (fun column : Fin n => board (row, column)))

/-- The executable signature loses no board information. -/
theorem boardSignature_injective {n : Nat} :
    Function.Injective (boardSignature : Board n → BoardSignature n) := by
  intro left right equalSignatures
  apply funext
  intro point
  have rowFunctions :
      (fun row : Fin n => List.ofFn (fun column : Fin n => left (row, column))) =
        (fun row : Fin n => List.ofFn (fun column : Fin n => right (row, column))) :=
    List.ofFn_injective equalSignatures
  have columnLists := congrFun rowFunctions point.1
  have columnFunctions :
      (fun column : Fin n => left (point.1, column)) =
        (fun column : Fin n => right (point.1, column)) :=
    List.ofFn_injective columnLists
  exact congrFun columnFunctions point.2

theorem boardSignature_eq_iff {n : Nat} {left right : Board n} :
    boardSignature left = boardSignature right ↔ left = right :=
  boardSignature_injective.eq_iff

/-- Orthogonal grid adjacency. -/
def OrthogonallyAdjacent {n : Nat} (left right : Point n) : Prop :=
  (left.1 = right.1 ∧ Nat.dist left.2.val right.2.val = 1) ∨
  (left.2 = right.2 ∧ Nat.dist left.1.val right.1.val = 1)

instance {n : Nat} (left right : Point n) :
    Decidable (OrthogonallyAdjacent left right) := by
  unfold OrthogonallyAdjacent
  infer_instance

theorem orthogonallyAdjacent_symm {n : Nat} {left right : Point n}
    (adjacent : OrthogonallyAdjacent left right) :
    OrthogonallyAdjacent right left := by
  rcases adjacent with adjacent | adjacent
  · exact Or.inl ⟨adjacent.1.symm, by simpa [Nat.dist_comm] using adjacent.2⟩
  · exact Or.inr ⟨adjacent.1.symm, by simpa [Nat.dist_comm] using adjacent.2⟩

theorem not_orthogonallyAdjacent_self {n : Nat} (point : Point n) :
    ¬ OrthogonallyAdjacent point point := by
  simp [OrthogonallyAdjacent]

/-- Previous coordinate on one finite axis, when it exists. -/
def axisPrevious? {n : Nat} (coordinate : Fin n) : Option (Fin n) :=
  if 0 < coordinate.val then
    some ⟨coordinate.val - 1,
      Nat.lt_of_le_of_lt (Nat.sub_le coordinate.val 1) coordinate.isLt⟩
  else
    none

/-- Next coordinate on one finite axis, when it exists. -/
def axisNext? {n : Nat} (coordinate : Fin n) : Option (Fin n) :=
  if next_lt : coordinate.val + 1 < n then
    some ⟨coordinate.val + 1, next_lt⟩
  else
    none

/-- The at-most-four grid neighbours, without scanning the full board. -/
def adjacentPointList {n : Nat} (point : Point n) : List (Point n) :=
  ((axisPrevious? point.1).toList.map (fun row => (row, point.2)) ++
    (axisNext? point.1).toList.map (fun row => (row, point.2)) ++
    (axisPrevious? point.2).toList.map (fun column => (point.1, column)) ++
    (axisNext? point.2).toList.map (fun column => (point.1, column)))

/-- Finite-set neighbour readout. -/
def adjacentPoints {n : Nat} (point : Point n) : Finset (Point n) :=
  (adjacentPointList point).toFinset

/-- Linear executable worklist.  Every pending point is inserted into `seen`
when enqueued, so the board cardinality is a sufficient fuel bound. -/
def componentWorklist {n : Nat} (board : Board n) (value : Option Polarity) :
    Nat → List (Point n) → List (Point n) → List (Point n)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, current :: pending, seen =>
      let fresh := (adjacentPointList current).filter
        (fun point => board point = value ∧ point ∉ seen)
      componentWorklist board value fuel (pending ++ fresh) (seen ++ fresh)

/-- The bounded finite component generated by a point.  There are only
`Fintype.card (Point n)` vertices, so this is the full flood exposure while
remaining executable and storing no independent component identifier. -/
def componentAt {n : Nat} (board : Board n) (point : Point n) :
    Finset (Point n) :=
  (componentWorklist board (board point) (Fintype.card (Point n))
    [point] [point]).toFinset

/-- Snapshot stone group generated from same-colour connectivity. -/
def groupAt {n : Nat} (board : Board n) (point : Point n) :
    Finset (Point n) :=
  match board point with
  | none => ∅
  | some _ => componentAt board point

/-- Empty region generated from the same finite component exposure. -/
def emptyRegionAt {n : Nat} (board : Board n) (point : Point n) :
    Finset (Point n) :=
  match board point with
  | none => componentAt board point
  | some _ => ∅

/-- A generated finite group has a liberty when one of its stones meets an
empty orthogonal neighbour. -/
def GroupHasLiberty {n : Nat} (board : Board n)
    (group : Finset (Point n)) : Prop :=
  ∃ stone ∈ group, ∃ liberty ∈ adjacentPoints stone,
    board liberty = none

instance {n : Nat} (board : Board n) (group : Finset (Point n)) :
    Decidable (GroupHasLiberty board group) := by
  unfold GroupHasLiberty
  infer_instance

/-- Liberty readout for the generated component at `point`. -/
def stoneHasLiberty {n : Nat} (board : Board n) (point : Point n) : Prop :=
  GroupHasLiberty board (groupAt board point)

instance {n : Nat} (board : Board n) (point : Point n) :
    Decidable (stoneHasLiberty board point) := by
  unfold stoneHasLiberty
  infer_instance

/-- The exact finite capture set generated by one placement. -/
def capturedStonesAfterPlay {n : Nat} (board : Board n) (colour : Polarity)
    (point : Point n) : Finset (Point n) :=
  let placed := Board.set board point (some colour)
  (adjacentPoints point).biUnion (fun neighbour =>
    if placed neighbour = some colour.other ∧
        ¬ stoneHasLiberty placed neighbour then
      groupAt placed neighbour
    else
      ∅)

/-- Place one stone and remove exactly the adjacent opponent groups that the
placement leaves without liberties. -/
def boardAfterPlay {n : Nat} (board : Board n) (colour : Polarity)
    (point : Point n) : Board n :=
  let placed := Board.set board point (some colour)
  let captured := capturedStonesAfterPlay board colour point
  fun candidate => if candidate ∈ captured then none else placed candidate

end Go
end ProcessGame
end SaturationMonoid
