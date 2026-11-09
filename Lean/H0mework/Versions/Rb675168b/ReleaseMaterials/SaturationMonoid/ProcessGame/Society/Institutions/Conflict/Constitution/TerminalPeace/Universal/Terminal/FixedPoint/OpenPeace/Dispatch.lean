import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Ingress
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Boundary
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Language

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)
open private AdaptivePeace.State.mk from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

/-- The right direction is reserved for a change to the registered public
terms. The left directions are exact actor and continuation pairs. -/
abbrev Effect (Party Good Port Technology Instrument : Type) :=
  Claim Party Good Port Technology Instrument ⊕ Unit

local notation "E" => Effect Party Good Port Technology Instrument
local notation "Grammar" => Language (RawEvent Party Good Port Technology Instrument) E
local notation "Write" => Installation.Live.Landed seed community cut Grammar

/-- The original resident runs the queue. The language reference is to
its last actual projection coface. -/
structure State (origin : RawCurrent Party Good Technology Instrument) (people : List Party) (quantum : ℚ) where
  private mk ::
  adaptive : AdaptivePeace.State (seed := seed) (cut := cut) (community := community) origin people quantum
  expansion : Option Write

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum

private def State.start
    (adaptive : AdaptivePeace.State (seed := seed) (cut := cut) (community := community) origin people quantum) : St :=
  ⟨adaptive, none⟩

def State.language (state : St) : Grammar :=
  (state.expansion.map Installation.Live.Landed.read).getD .initial

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (before : State (seed := seed) (cut := cut) (community := community) origin people quantum)
  (input : Input Party Good Port Technology Instrument)

def source : AdaptivePeace.Step tariff home (input.orders orders openOrders) (input.replies replies) before.adaptive :=
  AdaptivePeace.advance tariff home (input.orders orders openOrders) (input.replies replies) before.adaptive input.due

local notation "Actual" => source tariff home orders openOrders replies before input

variable {current : Current (seed := seed) (cut := cut) (community := community) origin people quantum}
  {bid : ReviewBid Party Good Port Technology Instrument}

/-- Compare only after the original material charge, using its before
read. A different representation of the same requested effects has
the same scope. -/
def paidEffects (paid : PaidReview current bid)
    (programme : ProgrammeSource.Input Party Good Port Technology Instrument) : Set E :=
  {effect | match effect with
    | .inl claim => claim ∈ paidLosses paid programme
    | .inr _ => ¬ KeepsPublicTerms paid.round.visit.read.programme programme}

@[simp] theorem paidEffects_loss (paid : PaidReview current bid)
    (programme : ProgrammeSource.Input Party Good Port Technology Instrument)
    (claim : Claim Party Good Port Technology Instrument) :
    Sum.inl claim ∈ paidEffects paid programme ↔ claim ∈ paidLosses paid programme :=
  Iff.rfl

@[simp] theorem paidEffects_public_terms (paid : PaidReview current bid)
    (programme : ProgrammeSource.Input Party Good Port Technology Instrument) :
    Sum.inr () ∈ paidEffects paid programme ↔ ¬ KeepsPublicTerms current.programme programme := by
  change (¬ KeepsPublicTerms paid.round.visit.read.programme programme) ↔ _
  rw [paid.round.programmeNext, paid.programme]

def scope : Set E :=
  match input with
  | .native _ => ∅
  | .proposal attempt =>
    match (Actual).source with
    | .ordinary _ _ => ∅
    | .prepaid _ _ paid => paidEffects paid attempt.programme

local notation "Scope" => scope tariff home orders openOrders replies before input

def languageWrite : Write :=
  Installation.Live.publish (Actual).next.native.ledger (before.language.repair Scope) true

def amendment : Option Write := by
  classical
  exact if Scope ⊆ before.language.covered then none
    else some (languageWrite tariff home orders openOrders replies before input)

local notation "Amendment" => amendment tariff home orders openOrders replies before input

def next : St :=
  match Amendment with
  | none => ⟨(Actual).next, before.expansion⟩
  | some landed => ⟨AdaptivePeace.State.mk {(Actual).next.native with ledger := landed.state} (Actual).next.amendment,
      some landed⟩

local notation "After" => next tariff home orders openOrders replies before input

theorem same_physical_successor : (After).adaptive.native.physical = (Actual).next.native.physical := by
  unfold next
  split <;> rfl

theorem same_programme : (After).adaptive.native.programme = (Actual).next.native.programme := by
  unfold next
  split <;> rfl

theorem same_recipe_gain (person : Party) (good : Good) :
    (After).adaptive.native.recipe.gain person good = (Actual).next.native.recipe.gain person good := by
  unfold next
  split <;> rfl

theorem same_stack : HEq (After).adaptive.native.ledger.stack (Actual).next.native.ledger.stack := by
  classical
  by_cases covered : Scope ⊆ before.language.covered
  · have absent : Amendment = none := by simp only [amendment, if_pos covered]
    rw [next, absent]
  · have written : Amendment = some (languageWrite tariff home orders openOrders replies before input) := by
      simp only [amendment, if_neg covered]
    rw [next, written]
    rfl

theorem same_rows :
    (After).adaptive.native.ledger.stack.balances = (Actual).next.native.ledger.stack.balances := by
  classical
  by_cases covered : Scope ⊆ before.language.covered
  · have absent : Amendment = none := by simp only [amendment, if_pos covered]
    rw [next, absent]
  · have written : Amendment = some (languageWrite tariff home orders openOrders replies before input) := by
      simp only [amendment, if_neg covered]
    rw [next, written]
    rfl

theorem physical_guards_unchanged : (After).adaptive.covered = (Actual).next.covered := by
  unfold next
  split <;> rfl

theorem no_repair_iff : Amendment = none ↔ Scope ⊆ before.language.covered := by
  classical
  by_cases covered : Scope ⊆ before.language.covered <;> simp [amendment, covered]

theorem scope_native (due : NoFreeProbe.Due Party Good Port Technology Instrument) :
    scope tariff home orders openOrders replies before (.native due) = ∅ :=
  rfl

theorem native_visit_is_unchanged (due : NoFreeProbe.Due Party Good Port Technology Instrument) :
    (next tariff home orders openOrders replies before (.native due)).adaptive =
      (AdaptivePeace.advance tariff home orders replies before.adaptive due).next := by
  have absent := (no_repair_iff tariff home orders openOrders replies before (.native due)).mpr
    (Set.empty_subset _)
  simp only [next, absent, source, Input.due, Input.orders, Input.replies]

theorem coverage_eq : (After).language.covered = before.language.covered ∪ Scope := by
  classical
  by_cases covered : Scope ⊆ before.language.covered
  · simp only [next, amendment, if_pos covered]
    exact (Set.union_eq_left.mpr covered).symm
  · simp only [next, amendment, if_neg covered]
    change (languageWrite tariff home orders openOrders replies before input).read.covered = _
    rw [languageWrite, Installation.Live.publish_reads_the_exact_payload, Language.covered_repair]

theorem keeps_coverage : before.language.covered ⊆ (After).language.covered := by
  rw [coverage_eq]
  exact Set.subset_union_left

theorem seals_scope : Scope ⊆ (After).language.covered := by
  rw [coverage_eq]
  exact Set.subset_union_right

/-- The open reply uses the old tariff visit's public clock and fixed
refusal. The coface itself does not occupy another physical slot. -/
def observe : AdaptivePeace.Observation :=
  (Actual).observe

theorem observation_lands_at_the_original_successor :
    (observe tariff home orders openOrders replies before input).landsAt = (After).adaptive.native.physical.raw.clock := by
  rw [same_physical_successor]
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
