import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Dispatch
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (inspectList)
open Reparation.Actual (Script Balance)
open FixedPoint (Recipe InReserve KeepsPublicTerms)
open FixedPoint.OpenPeace.Operational (RepeatCode RecipeConditions RecipeIssue checkRecipe)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {loss : Reparation.Actual.Occurrence seed community} {front : Script Party Good Port Technology Instrument}

variable (settled : Current loss front)

local notation "Cycle" => settled.programme.law.duration settled.physical.raw
local notation "Roster" => people loss front

/-- Recurrence starts at the actual post-payment inventory. The original
ledger's native address does not impose its former stock on this cut. -/
structure ClearedOpening where
  allPaid : ∀ row ∈ settled.ledger.stack.balances, row.2.remaining = 0
  recipe : Recipe settled.programme (originalRaw loss) Roster settled.physical.raw Cycle

variable [DecidableEq (Request Party Good Port Technology Instrument)]
  (code : RepeatCode settled.programme settled.physical.raw)

inductive RenewalIssue
  | residual (origin : Reparation.Actual.Occurrence seed community) (balance : Balance)
      (original : (origin, balance) ∈ settled.ledger.stack.balances) (unpaid : balance.remaining ≠ 0)
  | recipe (issue : RecipeIssue settled.programme (originalRaw loss) settled.physical.raw Roster code)

/-- Inspect the actual cleared reserve once. The same checked recipe feeds
ordinary renewal and the signed whole-network dispatcher. -/
def inspectRenewal : Except (RenewalIssue settled code)
    { opening : ClearedOpening settled // opening.recipe.move.word = code.production } :=
  match inspectList (fun row => row.2.remaining = 0) settled.ledger.stack.balances with
  | .failure row original unpaid => .error (.residual row.1 row.2 original unpaid)
  | .clear allPaid =>
    match checkRecipe settled.programme (originalRaw loss) settled.physical.raw Roster code with
    | .inl issue => .error (.recipe issue)
    | .inr checked => .ok ⟨⟨allPaid, checked.val⟩, checked.property⟩

theorem inspectRenewal_accepts_the_cleared_actual_recipe
    (cleared : ∀ row ∈ settled.ledger.stack.balances, row.2.remaining = 0)
    (viable : RecipeConditions settled.programme (originalRaw loss) settled.physical.raw Roster code) :
    ∃ checked, inspectRenewal settled code = .ok checked := by
  unfold inspectRenewal
  cases inspectList (fun row => row.2.remaining = 0) settled.ledger.stack.balances with
  | failure row original unpaid => exact (unpaid (cleared row original)).elim
  | clear paid =>
    cases checkRecipe settled.programme (originalRaw loss) settled.physical.raw Roster code with
    | inl issue => exact (issue.refutes _ _ _ _ _ viable).elim
    | inr checked => exact ⟨⟨⟨paid, checked.val⟩, checked.property⟩, rfl⟩

def openRenewal : Refused settled (RenewalIssue settled code) ⊕ ClearedOpening settled :=
  match inspectRenewal settled code with
  | .error issue => .inl (refuse settled issue)
  | .ok checked => .inr checked.val

theorem openRenewal_writes_when_the_original_rows_and_recipe_are_paid
    (cleared : ∀ row ∈ settled.ledger.stack.balances, row.2.remaining = 0)
    (viable : RecipeConditions settled.programme (originalRaw loss) settled.physical.raw Roster code) :
    ∃ opening, openRenewal settled code = .inr opening := by
  obtain ⟨checked, accepted⟩ := inspectRenewal_accepts_the_cleared_actual_recipe settled code cleared viable
  exact ⟨checked.val, by rw [openRenewal, accepted]⟩

omit [DecidableEq (Request Party Good Port Technology Instrument)]

structure RenewalEpoch where
  state : Current loss front
  terms : state.programme = settled.programme
  reserve : InReserve settled.physical.raw state.physical.raw
  rows : state.ledger.stack.balances = settled.ledger.stack.balances

variable {settled} (opening : ClearedOpening settled)

def firstEpoch : RenewalEpoch settled :=
  ⟨settled, rfl, ⟨fun _ _ => le_rfl, rfl, rfl⟩, rfl⟩

structure RenewalRound (epoch : RenewalEpoch settled) where
  actual : PeriodWrite epoch.state epoch.state.programme
  next : RenewalEpoch settled
  exactNext : next.state = actual.next
  elapsed : epoch.state.physical.raw.clock + Cycle ≤ next.state.physical.raw.clock

variable (epoch : RenewalEpoch settled)

def renew : RenewalRound epoch := by
  let recipe : Recipe epoch.state.programme (originalRaw loss) Roster settled.physical.raw Cycle :=
    epoch.terms.symm ▸ opening.recipe
  let move := recipe.moveAt epoch.state.physical.raw epoch.reserve
  let actual := writePeriod epoch.state epoch.state.programme (.refl _) move
  have stock : actual.next.physical.raw = move.next := actual.exactStock
  have kept : InReserve settled.physical.raw actual.next.physical.raw :=
    stock.symm ▸ recipe.next_reserved _ _
  exact ⟨actual, ⟨actual.next, actual.programmeNext.trans epoch.terms, kept, actual.rows.trans epoch.rows⟩,
    rfl, stock.symm ▸ recipe.next_clock _ _⟩

def renewal : Nat → RenewalEpoch settled
  | 0 => firstEpoch (settled := settled)
  | n + 1 => (renew opening (renewal n)).next

theorem renewal_consumes_the_same_successor (n : Nat) :
    (renewal opening (n + 1)).state = (renew opening (renewal opening n)).actual.next :=
  (renew opening (renewal opening n)).exactNext

theorem every_renewal_keeps_the_original_rows_paid (n : Nat) :
    ∀ row ∈ (renewal opening n).state.ledger.stack.balances, row.2.remaining = 0 := by
  rw [(renewal opening n).rows]
  exact opening.allPaid

theorem renewal_clock_lower (n : Nat) :
    settled.physical.raw.clock + (n : ℚ) * Cycle ≤ (renewal opening n).state.physical.raw.clock := by
  induction n with
  | zero => simp [renewal, firstEpoch]
  | succ n earlier =>
    have advance := (renew opening (renewal opening n)).elapsed
    change (renewal opening n).state.physical.raw.clock + Cycle ≤
      (renewal opening (n + 1)).state.physical.raw.clock at advance
    rw [Nat.cast_succ]
    linarith only [advance, earlier]

theorem the_paid_original_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (renewal opening n).state.physical.raw.clock := by
  have positive := opening.recipe.law.positive
  obtain ⟨n, passed⟩ := exists_nat_gt ((bound - settled.physical.raw.clock) / Cycle)
  have advanced := (div_lt_iff₀ positive).mp passed
  have later := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left n start)) positive.le
  exact ⟨max n start, le_max_right _ _, by linarith only [advanced, later, renewal_clock_lower opening (max n start)]⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted
