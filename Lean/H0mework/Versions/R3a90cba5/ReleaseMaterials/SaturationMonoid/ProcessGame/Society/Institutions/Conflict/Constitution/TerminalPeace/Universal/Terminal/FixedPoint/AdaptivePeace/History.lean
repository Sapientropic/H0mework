import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open private advance_preserves_stack from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Invariants

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)
local notation "Terms" => RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument
local notation "Slot" => NoFreeProbe.Due Party Good Port Technology Instrument

abbrev Policy (Party Good Port Technology Instrument : Type) :=
  Nat → List Observation → ℚ → (RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument) →
    NoFreeProbe.Due Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument) (replies : Replies Party Good Port Technology Instrument)

def commandedStep (state : St) (command : ℚ → Terms → Slot) : Step tariff home orders replies state :=
  advance tariff home orders replies state
    (command state.native.physical.raw.clock (Prepayment.registeredTerms state.native))

def transition (state : St) (command : ℚ → Terms → Slot) : St × Observation :=
  let actual := commandedStep tariff home orders replies state command
  (actual.next, actual.observe)

variable (opening : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : Policy Party Good Port Technology Instrument)

def history : Nat → St × List Observation :=
  NoFreeProbe.Erasure.run (transition tariff home orders replies) opening policy

local notation "Reached" => history tariff home orders replies opening policy

def stepAt (n : Nat) : Step tariff home orders replies (Reached n).1 :=
  let past := Reached n
  commandedStep tariff home orders replies past.1 (policy n past.2)

local notation "Visit" => stepAt tariff home orders replies opening policy

theorem history_succ (n : Nat) : (Reached (n + 1)).1 = (Visit n).next := rfl

theorem historical_coverage_is_monotone :
    Monotone (fun n => (Reached n).1.covered) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (Visit n).keeps_coverage

theorem coverage_has_exactly_its_original_paid_witnesses (key : Party × Good) (n : Nat) :
    key ∈ (Reached n).1.covered ↔ key ∈ opening.covered ∨
      ∃ i < n, key ∈ paidExposure tariff home orders replies (Reached i).1 (Visit i).source := by
  induction n with
  | zero => simp [history, NoFreeProbe.Erasure.run]
  | succ n earlier =>
    rw [history_succ, (Visit n).coverage_eq, Finset.mem_union, earlier]
    constructor
    · rintro ((already | ⟨i, before, listed⟩) | now)
      · exact Or.inl already
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt before, listed⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, now⟩
    · rintro (already | ⟨i, before, listed⟩)
      · exact Or.inl (Or.inl already)
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with earlier | same
        · exact Or.inl (Or.inr ⟨i, earlier, listed⟩)
        · subst i
          exact Or.inr listed

theorem every_old_scope_stays_closed {i j : Nat} (after : i ≤ j) :
    (Reached i).1.covered ⊆ (Reached j).1.covered :=
  historical_coverage_is_monotone tariff home orders replies opening policy after

theorem an_observed_scope_is_never_added_twice {i j : Nat} (after : i < j) (key : Party × Good)
    (observed : key ∈ paidExposure tariff home orders replies (Reached i).1 (Visit i).source) :
    key ∈ (Reached j).1.covered ∧ key ∉ ((Visit j).next.covered \ (Reached j).1.covered) := by
  have retained :=
    (coverage_has_exactly_its_original_paid_witnesses tariff home orders replies opening policy key j).mpr
      (.inr ⟨i, after, observed⟩)
  exact ⟨retained, fun duplicated => (Finset.mem_sdiff.mp duplicated).2 retained⟩

theorem every_novel_visit_strictly_increases_the_number_of_closed_scopes (n : Nat)
    (novel : ¬ paidExposure tariff home orders replies (Reached n).1 (Visit n).source ⊆ (Reached n).1.covered) :
    (Reached n).1.covered.card < (Reached (n + 1)).1.covered.card := by
  rw [history_succ]
  exact Finset.card_lt_card ((Visit n).strictly_extends_iff.mpr novel)

theorem an_old_scope_cannot_open_another_review {i j : Nat} (after : i ≤ j)
    (nonempty : paidExposure tariff home orders replies (Reached j).1 (Visit j).source ≠ ∅)
    (sameScope : paidExposure tariff home orders replies (Reached j).1 (Visit j).source ⊆ (Reached i).1.covered) :
    (Visit j).reply = .refused ∧ (Visit j).amendment = none := by
  have covered := sameScope.trans (every_old_scope_stays_closed tariff home orders replies opening policy after)
  generalize actual : Visit j = step at nonempty covered ⊢
  cases step with
  | ordinary _ safe => exact (nonempty safe).elim
  | refused _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | amended _ _ _ novel => exact (novel covered).elim

private theorem actual_stack_kept (state : St) (due : Slot) :
    HEq (advance tariff home orders replies state due).next.native.ledger.stack state.native.ledger.stack := by
  let step := advance tariff home orders replies state due
  have source : step.source = Prepayment.advanceRegistered tariff home orders state.native replies due :=
    resolve_keeps_the_actual_source tariff home orders replies state _
  refine step.same_stack.trans ?_
  rw [source, Prepayment.registered_dispatch_is_the_exact_private_dispatch]
  exact advance_preserves_stack tariff (fun current => Prepayment.registeredTerms current)
    home orders replies state.native due

theorem every_visit_preserves_the_original_stack (n : Nat) :
    HEq (Reached n).1.native.ledger.stack opening.native.ledger.stack := by
  induction n with
  | zero => rfl
  | succ n earlier =>
    rw [history_succ]
    let past := Reached n
    let due := policy n past.2 past.1.native.physical.raw.clock (Prepayment.registeredTerms past.1.native)
    exact (actual_stack_kept tariff home orders replies past.1 due).trans earlier

theorem every_visit_preserves_original_public_terms (n : Nat) :
    KeepsPublicTerms opening.native.programme (Reached n).1.native.programme := by
  induction n with
  | zero => exact .refl _
  | succ n earlier =>
    rw [history_succ, (Visit n).same_programme]
    exact earlier.trans (Visit n).source.keepsPublicTerms

theorem original_clock_lower_bound (start elapsed : Nat) :
    (Reached start).1.native.physical.raw.clock + (elapsed : ℚ) * quantum ≤
      (Reached (start + elapsed)).1.native.physical.raw.clock := by
  induction elapsed with
  | zero => simp
  | succ elapsed earlier =>
    let step := Visit (start + elapsed)
    have next := step.source.clock
    rw [← step.same_physical_successor, ← history_succ] at next
    rw [Nat.cast_succ, ← Nat.add_assoc]
    linarith only [next, earlier]

theorem original_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (Reached n).1.native.physical.raw.clock := by
  have positive := opening.native.recipe.law.positive
  obtain ⟨elapsed, beyond⟩ := exists_nat_gt ((bound - (Reached start).1.native.physical.raw.clock) / quantum)
  have crossed := (div_lt_iff₀ positive).mp beyond
  have lower := original_clock_lower_bound tariff home orders replies opening policy start elapsed
  exact ⟨start + elapsed, Nat.le_add_right _ _, by linarith only [crossed, lower]⟩

theorem every_due_visit_pays_needs_and_keeps_exit_and_growth (n : Nat) :
    let before := (Reached n).1.native.physical
    let after := (Reached (n + 1)).1.native.physical
    let read := (Visit n).source.round.visit.read
    read.effect.isAccepted = true ∧ read.effect.next = after ∧
      OriginalNeedFloor read.programme origin before.raw people read.commands ∧
      OriginalNeedFloor read.programme before.raw before.raw people read.commands ∧
      (∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
        Supply.Period read.programme origin before.raw [person] word) ∧
      (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
      (∃ person good, before.raw.stock person good < after.raw.stock person good) := by
  let step := Visit n
  let round := step.source.round
  have successor : round.next.physical = (Reached (n + 1)).1.native.physical := by
    rw [history_succ]
    exact step.source.physical.trans step.same_physical_successor.symm
  refine ⟨round.realWrite, round.physicalNext.trans successor, round.needs.1, round.needs.2,
    round.exit, round.noDamage, ?_⟩
  rw [← successor]
  exact round.growth

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace
