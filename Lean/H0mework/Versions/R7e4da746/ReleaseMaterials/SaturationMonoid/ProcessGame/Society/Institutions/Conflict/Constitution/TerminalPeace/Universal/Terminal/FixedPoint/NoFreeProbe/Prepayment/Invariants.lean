import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Run
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Closure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {View : Type*}

local notation "State" => Current (seed := seed) (cut := cut) (community := community) origin people quantum

variable (tariff : Tariff Party Good Port Technology Instrument)
  (see : Current (seed := seed) (cut := cut) (community := community) origin people quantum → View)
  (home : AnyAuthoritativeRootCurrent.{0}) (orders : PaymentOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)

private theorem ordinary_preserves_stack (current : State) (revision : Option (ProductionOffer Party Good Port Technology Instrument)) :
    HEq (ordinary tariff replies current revision).next.ledger.stack current.ledger.stack := by
  have unpaid := ordinary_has_no_charge tariff replies current revision
  cases actual : ordinary tariff replies current revision with
  | renewed | revised => rfl
  | reviewed _ _ _ => rw [actual] at unpaid; contradiction

private theorem advance_preserves_stack (current : State) (due : Due Party Good Port Technology Instrument) :
    HEq (advance tariff replies current see home orders due).next.ledger.stack current.ledger.stack := by
  unfold advance
  cases selected tariff replies current see home orders due with
  | none => exact ordinary_preserves_stack tariff replies current due.revision
  | some payment => rcases payment with ⟨_, _⟩; rfl

variable (opening : Current (seed := seed) (cut := cut) (community := community) origin people quantum)
  (policy : AdaptivePolicy View Party Good Port Technology Instrument)

local notation "reached" => history tariff see home orders replies opening policy
local notation "atDue" => stepAt tariff see home orders replies opening policy

theorem history_succ (n : Nat) : (reached (n + 1)).1 = (atDue n).next := rfl

/-- The dependent original stack is carried intact, including its
row embeddings through the two writes of each prepaid assessment. -/
theorem history_keeps_the_entire_stack (n : Nat) :
    HEq (reached n).1.ledger.stack opening.ledger.stack := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [history_succ]
    let before := (reached n).1
    let input := policy n (reached n).2 before.physical.raw.clock (see before)
    exact (advance_preserves_stack tariff see home orders replies before input).trans prior

theorem history_keeps_original_accounts (n : Nat) : InPeace opening (reached n).1 := by
  induction n with
  | zero => exact ⟨rfl, .refl _⟩
  | succ n prior =>
    rw [history_succ]
    exact ⟨(atDue n).rows.trans prior.1, prior.2.trans (atDue n).keepsPublicTerms⟩

theorem original_clock_lower_bound_from (start elapsed : Nat) :
    (reached start).1.physical.raw.clock + (elapsed : ℚ) * quantum ≤
      (reached (start + elapsed)).1.physical.raw.clock := by
  induction elapsed with
  | zero => simp
  | succ elapsed prior =>
    have next := (atDue (start + elapsed)).clock
    rw [← history_succ] at next
    rw [Nat.cast_succ, ← Nat.add_assoc]
    linarith only [next, prior]

theorem original_clock_is_strictly_monotone :
    StrictMono (fun n => (reached n).1.physical.raw.clock) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [history_succ]
  exact (lt_add_of_pos_right _ opening.recipe.law.positive).trans_le (atDue n).clock

theorem original_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (reached n).1.physical.raw.clock := by
  have positive := opening.recipe.law.positive
  obtain ⟨elapsed, beyond⟩ := exists_nat_gt ((bound - (reached start).1.physical.raw.clock) / quantum)
  have crossed := (div_lt_iff₀ positive).mp beyond
  have lower := original_clock_lower_bound_from tariff see home orders replies opening policy start elapsed
  exact ⟨start + elapsed, Nat.le_add_right _ _, by linarith only [crossed, lower]⟩

/-- The original material receipt spends the order's literal clock
even if a later admission is presented under different public terms. -/
theorem an_actual_paid_wire_cannot_be_replayed {FutureView : Type*}
    (futureSee : State → FutureView) (futureTariff : Tariff Party Good Port Technology Instrument)
    (futureHome : AnyAuthoritativeRootCurrent.{0}) (futureOrders : PaymentOrders Party Good Port Technology Instrument)
    (visible : FutureView) {earlier later : Nat} {wire : Wire Party Good Port Technology Instrument}
    (paid : (atDue earlier).paidWire = some wire) (after : earlier < later) :
    inspectOrder futureSee futureTariff futureHome futureOrders visible (reached later).1.physical.raw.clock wire = none := by
  let before := (reached earlier).1
  let input := policy earlier (reached earlier).2 before.physical.raw.clock (see before)
  obtain ⟨consented, _, _⟩ := a_selected_order_has_its_own_prepaid_receipt tariff replies before see home orders input paid
  apply stale_order_erases
  rw [consented.stamp]
  exact original_clock_is_strictly_monotone tariff see home orders replies opening policy after

theorem every_due_ordinal_pays_needs_and_keeps_exit_and_growth (n : Nat) :
    let before := (reached n).1.physical
    let after := (reached (n + 1)).1.physical
    let read := (atDue n).round.visit.read
    read.effect.isAccepted = true ∧ read.effect.next = after ∧
      OriginalNeedFloor read.programme origin before.raw people read.commands ∧
      OriginalNeedFloor read.programme before.raw before.raw people read.commands ∧
      (∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
        Supply.Period read.programme origin before.raw [person] word) ∧
      (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
      (∃ person good, before.raw.stock person good < after.raw.stock person good) := by
  let step := atDue n
  have successor : step.round.next.physical = (reached (n + 1)).1.physical := by
    rw [history_succ]
    exact step.physical
  refine ⟨step.round.realWrite, step.round.physicalNext.trans successor, step.round.needs.1, step.round.needs.2,
    step.round.exit, step.round.noDamage, ?_⟩
  rw [← successor]
  exact step.round.growth

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment
