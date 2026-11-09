import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

/-- One disposition of an existing original liability row. -/
inductive Change (origin : Occurrence seed community) (before : Balance)
  | keep
  | pay (share : Share origin) (within : share.amount ≤ before.remaining)

namespace Change

variable {origin : Occurrence seed community} {before : Balance}

def amount : Change origin before → ℚ
  | .keep => 0
  | .pay share _ => share.amount

def after : Change origin before → Balance
  | .keep => before
  | .pay share within => before.subtract share.amount within

def motion (move : Change origin before) :
    Transport.Motion (law origin) (.live before) (.live move.after) :=
  match move with
  | .keep => .inr (.wait (.live before))
  | .pay share within => credit origin before share within

theorem amount_nonnegative (move : Change origin before) : 0 ≤ move.amount := by
  cases move with
  | keep => exact le_rfl
  | pay share _ => exact share.positive.le

theorem amount_within (move : Change origin before) : move.amount ≤ before.remaining := by
  cases move with
  | keep => exact before.nonnegative
  | pay _ within => exact within

theorem after_exact (move : Change origin before) :
    move.after.remaining = before.remaining - move.amount := by
  cases move with
  | keep => exact (sub_zero _).symm
  | pay _ _ => rfl

theorem already_paid_is_kept (move : Change origin before) (paid : before.remaining = 0) :
    move = .keep := by
  cases move with
  | keep => rfl
  | pay share within => exact (not_le_of_gt share.positive (within.trans_eq paid)).elim

end Change

local notation "Row" => Occurrence seed community × Balance

/-- The dependent spine has one disposition at each position of the input
whole-ledger restriction. -/
inductive Changes : List Row → Type
  | nil : Changes []
  | cons {row : Row} {rows : List Row} : Change row.1 row.2 → Changes rows → Changes (row :: rows)

namespace Changes

def result : {rows : List Row} → Changes rows → List Row
  | _, .nil => []
  | _, .cons (row := row) head tail => (row.1, head.after) :: result tail

def assignedWhere (select : Occurrence seed community → Prop) [DecidablePred select] :
    {rows : List Row} → Changes rows → ℚ
  | _, .nil => 0
  | _, .cons (row := row) head tail =>
    (if select row.1 then head.amount else 0) + assignedWhere select tail

abbrev assignedFor (key : Key Party Good) {rows : List Row} (moves : Changes rows) : ℚ :=
  assignedWhere (fun origin => origin.key = key) moves

abbrev assignedForGood (good : Good) {rows : List Row} (moves : Changes rows) : ℚ :=
  assignedWhere (fun origin => origin.key.2.2 = good) moves

theorem result_origins {rows : List Row} (moves : Changes rows) :
    moves.result.map Prod.fst = rows.map Prod.fst := by
  induction moves with
  | nil => rfl
  | cons head _ ih => simp only [result, List.map_cons, ih]

theorem result_length {rows : List Row} (moves : Changes rows) :
    moves.result.length = rows.length := by
  induction moves with
  | nil => rfl
  | cons head _ ih => simp only [result, List.length_cons, ih]

def unchanged (rows : List Row) : Changes rows :=
  match rows with
  | [] => .nil
  | _ :: tail => .cons .keep (unchanged tail)

@[simp] theorem unchanged_result (rows : List Row) : (unchanged rows).result = rows := by
  induction rows with
  | nil => rfl
  | cons row rest prior =>
    cases row
    simp only [unchanged, result, Change.after, prior]

end Changes

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Allocation
