import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Portfolio.Allocation.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Changes

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

local notation "Row" => Occurrence seed community × Balance

def append : {front tail : List Row} → Changes front → Changes tail → Changes (front ++ tail)
  | _, _, .nil, second => second
  | _, _, .cons first remaining, second => .cons first (append remaining second)

def split (front tail : List Row) (moves : Changes (front ++ tail)) : Changes front × Changes tail :=
  match front with
  | [] => ⟨.nil, moves⟩
  | _ :: remainingRows =>
    match moves with
    | .cons first remaining =>
      let parts := split remainingRows tail remaining
      ⟨.cons first parts.1, parts.2⟩

theorem append_split (front tail : List Row) (moves : Changes (front ++ tail)) :
    append (split front tail moves).1 (split front tail moves).2 = moves := by
  induction front with
  | nil => rfl
  | cons _ remainingRows prior =>
    cases moves with
    | cons first remaining =>
      exact congrArg (Changes.cons first) (prior remaining)

theorem result_append {front tail : List Row} (first : Changes front) (second : Changes tail) :
    (first.append second).result = first.result ++ second.result := by
  induction first with
  | nil => rfl
  | cons _ _ prior => simp only [append, result, List.cons_append, prior]

theorem assigned_append (select : Occurrence seed community → Prop) [DecidablePred select]
    {front tail : List Row} (first : Changes front) (second : Changes tail) :
    (first.append second).assignedWhere select = first.assignedWhere select + second.assignedWhere select := by
  induction first with
  | nil => simp [append, assignedWhere]
  | cons _ _ prior => simp only [append, assignedWhere, prior, add_assoc]

def single {row : Row} (move : Change row.1 row.2) : Changes [row] := .cons move .nil

private def singleHead {row : Row} : Changes [row] → Change row.1 row.2
  | .cons move .nil => move

private theorem singleHead_exact {row : Row} (moves : Changes [row]) :
    single (singleHead moves) = moves := by
  cases moves with
  | cons move tail => cases tail; rfl

def unsnoc (front : List Row) (row : Row) (moves : Changes (front ++ [row])) :
    Changes front × Change row.1 row.2 :=
  let parts := split front [row] moves
  ⟨parts.1, singleHead parts.2⟩

theorem append_unsnoc (front : List Row) (row : Row) (moves : Changes (front ++ [row])) :
    (unsnoc front row moves).1.append (single (unsnoc front row moves).2) = moves :=
  (congrArg (append (split front [row] moves).1) (singleHead_exact (split front [row] moves).2)).trans
    (append_split front [row] moves)

theorem result_unsnoc (front : List Row) (row : Row) (moves : Changes (front ++ [row])) :
    moves.result = (unsnoc front row moves).1.result ++ [(row.1, (unsnoc front row moves).2.after)] :=
  (congrArg result (append_unsnoc front row moves).symm).trans (result_append _ _)

theorem assigned_unsnoc (select : Occurrence seed community → Prop) [DecidablePred select]
    (front : List Row) (row : Row) (moves : Changes (front ++ [row])) :
    moves.assignedWhere select = (unsnoc front row moves).1.assignedWhere select +
      (if select row.1 then (unsnoc front row moves).2.amount else 0) := by
  calc
    moves.assignedWhere select =
        ((unsnoc front row moves).1.append (single (unsnoc front row moves).2)).assignedWhere select :=
      congrArg (assignedWhere select) (append_unsnoc front row moves).symm
    _ = _ := by simp only [assigned_append, single, assignedWhere, add_zero]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation.Changes
