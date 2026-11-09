import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Repair
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material (OriginalNeedFloor)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open private actual_stack_kept from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.History

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

abbrev Terms (Party Good Port Technology Instrument : Type) :=
  RawLaw Party Good Port Technology Instrument × RawEvent Party Good Port Technology Instrument

abbrev Policy (Party Good Port Technology Instrument : Type) :=
  Nat → List AdaptivePeace.Observation → ℚ → Terms Party Good Port Technology Instrument →
    Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument) →
      Input Party Good Port Technology Instrument

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (opening : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (policy : Policy Party Good Port Technology Instrument)

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)

def transition (state : St) (command : ℚ → Terms Party Good Port Technology Instrument →
    Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument) →
    Input Party Good Port Technology Instrument) : St × AdaptivePeace.Observation :=
  let submitted := command state.adaptive.native.physical.raw.clock
    (Prepayment.registeredTerms state.adaptive.native) state.language
  (next tariff home orders openOrders replies state submitted,
    observe tariff home orders openOrders replies state submitted)

def history : Nat → St × List AdaptivePeace.Observation :=
  Erasure.run (transition tariff home orders openOrders replies) opening policy

local notation "Reached" => (history tariff home orders openOrders replies opening policy)

def inputAt (n : Nat) : Input Party Good Port Technology Instrument :=
  let past := Reached n
  policy n past.2 past.1.adaptive.native.physical.raw.clock
    (Prepayment.registeredTerms past.1.adaptive.native) past.1.language

local notation "Request" n => (inputAt tariff home orders openOrders replies opening policy n)
local notation "At" n => (Prod.fst (Reached n))
local notation "Effects" n => (scope tariff home orders openOrders replies (At n) (Request n))
local notation "Visit" n => (source tariff home orders openOrders replies (At n) (Request n))

theorem history_succ (n : Nat) :
    (At (n + 1)) = next tariff home orders openOrders replies (At n) (Request n) :=
  rfl

theorem history_keeps_original_stack (n : Nat) :
    HEq (At n).adaptive.native.ledger.stack opening.adaptive.native.ledger.stack := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [history_succ]
    exact (same_stack tariff home orders openOrders replies (At n) (Request n)).trans
      ((actual_stack_kept tariff home ((Request n).orders orders openOrders) ((Request n).replies replies)
        (At n).adaptive (Request n).due).trans prior)

theorem history_keeps_public_terms (n : Nat) :
    KeepsPublicTerms opening.adaptive.native.programme (At n).adaptive.native.programme := by
  induction n with
  | zero => exact .refl _
  | succ n prior =>
    rw [history_succ, same_programme]
    exact prior.trans (Visit n).keeps_public_terms

theorem history_keeps_original_rows (n : Nat) :
    (At n).adaptive.native.ledger.stack.balances = opening.adaptive.native.ledger.stack.balances := by
  induction n with
  | zero => rfl
  | succ n prior =>
    rw [history_succ, same_rows]
    let step := Visit n
    have same : step.next.native.ledger.stack.balances = step.source.next.ledger.stack.balances := by
      cases step <;> rfl
    exact same.trans (step.source.rows.trans prior)

theorem history_clock_bound (start elapsed : Nat) :
    (At start).adaptive.native.physical.raw.clock + (elapsed : ℚ) * quantum ≤
      (At (start + elapsed)).adaptive.native.physical.raw.clock := by
  induction elapsed with
  | zero => simp
  | succ elapsed prior =>
    let index := start + elapsed
    have tick := (Visit index).source.clock
    rw [← (Visit index).same_physical_successor, ← same_physical_successor, ← history_succ] at tick
    rw [Nat.cast_succ, ← Nat.add_assoc]
    linarith only [tick, prior]

theorem history_clock_is_cofinal (start : Nat) (bound : ℚ) :
    ∃ n ≥ start, bound < (At n).adaptive.native.physical.raw.clock := by
  have positive := opening.adaptive.native.recipe.law.positive
  obtain ⟨elapsed, beyond⟩ := exists_nat_gt
    ((bound - (At start).adaptive.native.physical.raw.clock) / quantum)
  have crossed := (div_lt_iff₀ positive).mp beyond
  have lower := history_clock_bound tariff home orders openOrders replies opening policy start elapsed
  exact ⟨start + elapsed, Nat.le_add_right _ _, by linarith only [crossed, lower]⟩

def LivingVisitAt (n : Nat) : Prop :=
    let before := (At n).adaptive.native.physical
    let after := (At (n + 1)).adaptive.native.physical
    let read := (Visit n).source.round.visit.read
    read.effect.isAccepted = true ∧ read.effect.next = after ∧
      OriginalNeedFloor read.programme origin before.raw people read.commands ∧
      OriginalNeedFloor read.programme before.raw before.raw people read.commands ∧
      (∀ person ∈ people, ∃ word, Supply.Registered read.programme before.raw word ∧
        Supply.Period read.programme origin before.raw [person] word) ∧
      (∀ item ∈ read.effect.execution.items, ∀ key, Reparation.loss read.programme.law community item key = 0) ∧
      (∃ person good, before.raw.stock person good < after.raw.stock person good)

theorem history_is_living_and_peaceful_at_every_visit (n : Nat) :
    LivingVisitAt tariff home orders openOrders replies opening policy n := by
  unfold LivingVisitAt
  let actual := Visit n
  let round := actual.source.round
  have physical : round.next.physical = (At (n + 1)).adaptive.native.physical := by
    rw [history_succ, same_physical_successor]
    exact actual.source.physical.trans actual.same_physical_successor.symm
  refine ⟨round.realWrite, round.physicalNext.trans physical, round.needs.1, round.needs.2,
    round.exit, round.noDamage, ?_⟩
  rw [← physical]
  exact round.growth

theorem language_history_is_monotone :
    Monotone (fun n => (At n).language.covered) := by
  apply monotone_nat_of_le_succ
  intro n
  exact keeps_coverage tariff home orders openOrders replies (At n) (Request n)

theorem each_new_expression_has_its_original_paid_visit
    (effect : Effect Party Good Port Technology Instrument) (n : Nat) :
    effect ∈ (At n).language.covered ↔ effect ∈ opening.language.covered ∨
      ∃ i < n, effect ∈ Effects i := by
  induction n with
  | zero => simp [history, Erasure.run]
  | succ n earlier =>
    rw [history_succ, coverage_eq, Set.mem_union, earlier]
    constructor
    · rintro ((already | ⟨i, before, found⟩) | now)
      · exact .inl already
      · exact .inr ⟨i, Nat.lt_succ_of_lt before, found⟩
      · exact .inr ⟨n, Nat.lt_succ_self n, now⟩
    · rintro (already | ⟨i, before, found⟩)
      · exact .inl (.inl already)
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ before) with prior | now
        · exact .inl (.inr ⟨i, prior, found⟩)
        · subst i
          exact .inr found

theorem every_recorded_effect_is_expressed_at_all_later_epochs {i j : Nat}
    (later : i < j) {effect : Effect Party Good Port Technology Instrument}
    (exposed : effect ∈ Effects i) :
    ∃ code : (At j).language.Code, effect ∈ (At j).language.denotes code :=
  (each_new_expression_has_its_original_paid_visit tariff home orders openOrders replies opening policy effect j).mpr
    (.inr ⟨i, later, exposed⟩)

theorem a_covered_scope_never_opens_another_amendment {i j : Nat}
    (later : i ≤ j) (covered : (Effects j) ⊆ (At i).language.covered) :
    amendment tariff home orders openOrders replies (At j) (Request j) = none := by
  exact (no_repair_iff tariff home orders openOrders replies (At j) (Request j)).mpr
    (covered.trans (language_history_is_monotone tariff home orders openOrders replies opening policy later))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
