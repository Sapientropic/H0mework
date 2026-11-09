import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Dispatch
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

abbrev Policy (Party Good Port Technology Instrument : Type) :=
  Nat → AnyAuthoritativeRootCurrent.{0} → RawCurrent Party Good Technology Instrument →
    Proposal Party Good Port Technology Instrument

variable (replies : Replies Party Good Port Technology Instrument)
  (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)

def history (policy : Policy Party Good Port Technology Instrument) : Nat → State
  | 0 => opening
  | n + 1 =>
    let before := history policy n
    (dispatch replies before (policy n before.ledger.resident.erase before.physical.raw)).next

def roundAt (policy : Policy Party Good Port Technology Instrument) (n : Nat) :
    Round (history replies opening policy n) :=
  let before := history replies opening policy n
  dispatch replies before (policy n before.ledger.resident.erase before.physical.raw)

def InPeace (current : State) : Prop :=
  current.ledger.stack.balances = opening.ledger.stack.balances ∧
    KeepsPublicTerms opening.programme current.programme

theorem every_proposal_stays_in_the_same_peace_region (current : State)
    (inside : InPeace opening current) (submitted : Proposal Party Good Port Technology Instrument) :
    InPeace opening (dispatch replies current submitted).next :=
  ⟨(dispatch replies current submitted).rows.trans inside.1,
    inside.2.trans (dispatch_keeps_the_original_public_terms replies current submitted)⟩

theorem history_stays_in_peace (policy : Policy Party Good Port Technology Instrument) (n : Nat) :
    InPeace opening (history replies opening policy n) := by
  induction n with
  | zero => exact ⟨rfl, .refl _⟩
  | succ n earlier =>
    exact every_proposal_stays_in_the_same_peace_region replies opening _ earlier _

theorem history_keeps_every_original_balance (policy : Policy Party Good Port Technology Instrument) (n : Nat) :
    (history replies opening policy n).ledger.stack.balances = opening.ledger.stack.balances :=
  (history_stays_in_peace replies opening policy n).1

theorem original_clock_lower_bound (policy : Policy Party Good Port Technology Instrument) (n : Nat) :
    opening.physical.raw.clock + (n : ℚ) * quantum ≤ (history replies opening policy n).physical.raw.clock := by
  induction n with
  | zero => simp [history]
  | succ n earlier =>
    have next := (roundAt replies opening policy n).clock
    change (history replies opening policy n).physical.raw.clock + quantum ≤
      (history replies opening policy (n + 1)).physical.raw.clock at next
    rw [Nat.cast_succ]
    linarith only [next, earlier]

theorem original_clock_is_cofinal_under_every_policy
    (policy : Policy Party Good Port Technology Instrument) (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (history replies opening policy n).physical.raw.clock := by
  have positive := opening.recipe.law.positive
  obtain ⟨n, beyond⟩ := exists_nat_gt ((bound - opening.physical.raw.clock) / quantum)
  have passed := (div_lt_iff₀ positive).mp beyond
  have monotone := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_max_left n start)) positive.le
  have clock := original_clock_lower_bound replies opening policy (max n start)
  exact ⟨max n start, le_max_right _ _, by linarith only [clock, monotone, passed]⟩

/-- The same region is closed under every submission and admissible
revision of the installed dispatch. All its runs use the original clock. -/
structure PeaceFixedPoint : Prop where
  oldPaid : ∀ row ∈ opening.ledger.stack.balances, row.2.remaining = 0
  closed : ∀ current : State, InPeace opening current →
    ∀ submitted, InPeace opening (dispatch replies current submitted).next
  originalLedger : ∀ policy n, (history replies opening policy n).ledger.stack.balances = opening.ledger.stack.balances
  originalTerms : ∀ policy n, KeepsPublicTerms opening.programme (history replies opening policy n).programme
  cofinal : ∀ policy start bound,
    ∃ n ≥ start, bound < (history replies opening policy n).physical.raw.clock
  strictlyCostly : ∀ (current : State), InPeace opening current →
    ∀ bid, AccountableReview replies current bid → ∀ weight : Good → ℚ, (∀ good, 0 < weight good) →
      materialPayoff bid (dispatch replies current (.review bid)).next.physical.raw
        (dispatch replies current .renew).next.physical.raw weight < 0

theorem buildPeaceFixedPoint (all : ∀ row ∈ opening.ledger.stack.balances, row.2.remaining = 0) :
    PeaceFixedPoint replies opening :=
  ⟨all, every_proposal_stays_in_the_same_peace_region replies opening,
    history_keeps_every_original_balance replies opening,
    fun policy n => (history_stays_in_peace replies opening policy n).2,
    original_clock_is_cofinal_under_every_policy replies opening,
    fun current _ bid review weight positive => by
      have quiet : (dispatch replies current .renew).next.physical.raw = current.move.next :=
        (productiveRound_reads_selected_production current .renew .renewed current.programme current.recipe).2.1
      rw [quiet]
      exact (every_accountable_attack_is_strictly_costly replies current bid review weight positive).2.2.2.2.2.2.2⟩

theorem PeaceFixedPoint.the_original_claims_remain_paid (fixed : PeaceFixedPoint replies opening)
    (policy : Policy Party Good Port Technology Instrument) (n : Nat) :
    ∀ row ∈ (history replies opening policy n).ledger.stack.balances, row.2.remaining = 0 := by
  rw [fixed.originalLedger policy n]
  exact fixed.oldPaid

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint
