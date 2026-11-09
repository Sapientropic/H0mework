import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.OpeningInheritance
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Landing
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.RevisionAuthority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open private OpenPeace.State.mk from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch
open private AdaptivePeace.State.mk from H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.AdaptivePeace.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}

local notation "Base" => OpenPeace.State (seed := seed) (cut := cut) (community := community) origin people quantum
local notation "Grammar" => Language (RawEvent Party Good Port Technology Instrument)
  (Effect Party Good Port Technology Instrument)
local notation "Landed" => Installation.Live.Landed seed community cut Grammar

/-- The material current owns the live whole ledger. The signed lanes are
dependent reads at its resident, and the next U7 calculus uses its world. -/
structure State (origin : RawCurrent Party Good Technology Instrument) (people : List Party) (quantum : ℚ) where
  private mk ::
  base : OpenPeace.State (seed := seed) (cut := cut) (community := community) origin people quantum
  lanes : SignedLanes Party Good Port Technology Instrument base.adaptive.native.ledger.resident
  u7 : LocalU7 base.adaptive.native.ledger.world

local notation "St" => State (seed := seed) (cut := cut) (community := community) origin people quantum

def start (base : Base)
    (lanes : SignedLanes Party Good Port Technology Instrument base.adaptive.native.ledger.resident)
    (inherited : InheritedCalculus base.adaptive.native.ledger.world) : St :=
  ⟨base, lanes, LocalU7.native inherited⟩

variable (home : AnyAuthoritativeRootCurrent.{0}) (replies : Replies Party Good Port Technology Instrument)
  (before : State (seed := seed) (cut := cut) (community := community) origin people quantum)
  (input : OpenPeace.Input Party Good Port Technology Instrument)

abbrev State.current (state : St) := state.base.adaptive.native

local notation "Quote" => before.lanes.tariff.read
local notation "Orders" => before.lanes.payment.read
local notation "OpenOrdersAt" => before.lanes.openPayment.read

def source := OpenPeace.source Quote home Orders OpenOrdersAt replies before.base input

def scope := OpenPeace.scope Quote home Orders OpenOrdersAt replies before.base input

local notation "Actual" => source home replies before input
local notation "Scope" => scope home replies before input
local notation "GrammarNow" => OpenPeace.State.language before.base
local notation "Prior" => AdaptivePeace.State.native (AdaptivePeace.Step.next (Actual))

def reviewLane : LocalU7 (Prior).ledger.world :=
  (adaptiveKeepsWorld (Actual)).symm ▸ before.u7

local notation "Lane" => reviewLane home replies before input

def failure (novel : ¬ Scope ⊆ (GrammarNow).covered) :=
  rootedFailure (Prior).ledger GrammarNow Scope Lane novel

def revision (novel : ¬ Scope ⊆ (GrammarNow).covered) :=
  revised (Prior).ledger GrammarNow Scope Lane novel

def languageWrite (novel : ¬ Scope ⊆ (GrammarNow).covered) : Landed :=
  revisedLanguageWrite (Prior).ledger GrammarNow Scope Lane novel

private def ordinary : St :=
  ⟨OpenPeace.State.mk (Actual).next before.base.expansion, before.lanes.afterAdaptive (Actual), Lane⟩

private def repaired (novel : ¬ Scope ⊆ (GrammarNow).covered) : St :=
  let write := languageWrite home replies before input novel
  let reads := revisedReads (Prior).ledger GrammarNow Scope Lane novel
  ⟨OpenPeace.State.mk (AdaptivePeace.State.mk { (Prior) with ledger := write.state } (Actual).next.amendment)
      (some write),
    (before.lanes.afterAdaptive (Actual)).map reads.carry,
    LocalU7.afterCoface (failure home replies before input novel)⟩

structure Step where
  private mk ::
  next : State (seed := seed) (cut := cut) (community := community) origin people quantum
  write : Option (Installation.Live.Landed seed community cut
    (Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument)))

/-- A paid expression failure emits its U8 first write. That resident
becomes the material input of the following round. -/
def advance : Step (seed := seed) (cut := cut) (community := community)
    (origin := origin) (people := people) (quantum := quantum) := by
  classical
  exact if novel : ¬ Scope ⊆ (GrammarNow).covered then
    ⟨repaired home replies before input novel, some (languageWrite home replies before input novel)⟩
  else ⟨ordinary home replies before input, none⟩

local notation "After" => Step.next (advance home replies before input)

private theorem selects_revision (novel : ¬ Scope ⊆ (GrammarNow).covered) :
    advance home replies before input =
      ⟨repaired home replies before input novel, some (languageWrite home replies before input novel)⟩ := by
  classical
  exact dif_pos novel

private theorem selects_ordinary (covered : Scope ⊆ (GrammarNow).covered) :
    advance home replies before input = ⟨ordinary home replies before input, none⟩ := by
  classical
  exact dif_neg (not_not.mpr covered)

theorem next_ledger (novel : ¬ Scope ⊆ (GrammarNow).covered) :
    (After).current.ledger = (languageWrite home replies before input novel).state := by
  rw [selects_revision home replies before input novel]
  rfl

set_option maxHeartbeats 500000 in
theorem next_reads_generated_first_write (novel : ¬ Scope ⊆ (GrammarNow).covered) :
    let generated := (revision home replies before input novel).generate
    (⟨generated.NewN, generated.newLivingRoot.generatedNextCurrentAt
      (.finite generated.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      (After).current.ledger.resident.erase := by
  have lands := revisedLedger_is_the_generated_first_write (Prior).ledger GrammarNow Scope Lane novel
  exact lands.trans (congrArg (fun ledger : Installation.Live.Ledger seed community cut =>
    ledger.resident.erase) (next_ledger home replies before input novel).symm)

theorem covered_next (covered : Scope ⊆ (GrammarNow).covered) :
    (After).base.adaptive = (Actual).next := by
  rw [selects_ordinary home replies before input covered]
  rfl

theorem same_physical : (After).current.physical = (Prior).physical := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    rfl
  · rw [selects_revision home replies before input covered]
    rfl

theorem same_programme : (After).current.programme = (Prior).programme := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    rfl
  · rw [selects_revision home replies before input covered]
    rfl

theorem same_recipe_word : (After).current.recipe.move.word = (Prior).recipe.move.word := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    rfl
  · rw [selects_revision home replies before input covered]
    rfl

theorem same_rows : (After).current.ledger.stack.balances = (Prior).ledger.stack.balances := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    rfl
  · rw [selects_revision home replies before input covered]
    rfl

theorem same_stack : HEq (After).current.ledger.stack (Prior).ledger.stack := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    rfl
  · rw [selects_revision home replies before input covered]
    rfl

theorem coverage_eq : (After).base.language.covered = (GrammarNow).covered ∪ Scope := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    exact (Set.union_eq_left.mpr covered).symm
  · rw [selects_revision home replies before input covered]
    change (languageWrite home replies before input covered).read.covered = _
    rw [languageWrite, revisedLanguageWrite_read, Language.covered_repair]

theorem write_iff : (advance home replies before input).write.isSome = true ↔ ¬ Scope ⊆ (GrammarNow).covered := by
  classical
  by_cases covered : Scope ⊆ (GrammarNow).covered
  · rw [selects_ordinary home replies before input covered]
    simp [covered]
  · rw [selects_revision home replies before input covered]
    simp [covered]

theorem unpaid_keeps_its_material_next (unpaid : (Actual).source.paidWire = none) :
    (advance home replies before input).write = none ∧ (After).base.adaptive = (Actual).next := by
  have covered : Scope ⊆ (GrammarNow).covered := by
    unfold scope
    rw [no_unpaid_scope Quote home Orders OpenOrdersAt replies before.base input unpaid]
    exact Set.empty_subset _
  classical
  exact ⟨by rw [selects_ordinary home replies before input covered], covered_next home replies before input covered⟩

theorem next_keeps_original_signatures :
    (After).lanes.tariff.read = Quote ∧
    (After).lanes.payment.read = Orders ∧
    (After).lanes.openPayment.read = OpenOrdersAt := by
  classical
  by_cases novel : ¬ Scope ⊆ (GrammarNow).covered
  · rw [selects_revision home replies before input novel]
    dsimp only [Step.next, repaired, State.lanes]
    let lanes := before.lanes.afterAdaptive (Actual)
    let reads := revisedReads (Prior).ledger GrammarNow Scope Lane novel
    have h := lanes.map_keeps_reads reads.carry reads.keeps
    have k := before.lanes.afterAdaptive_keeps_reads (Actual)
    exact ⟨h.1.trans k.1, h.2.1.trans k.2.1, h.2.2.trans k.2.2⟩
  · rw [selects_ordinary home replies before input (not_not.mp novel)]
    exact before.lanes.afterAdaptive_keeps_reads (Actual)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime
