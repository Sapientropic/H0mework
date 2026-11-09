import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface (RelativeExpressiveCapacity)
open NoFreeProbe
open NoFreeProbe.Prepayment (PaymentOrders)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

variable (tariff : Tariff Party Good Port Technology Instrument) (home : AnyAuthoritativeRootCurrent.{0})
  (orders : PaymentOrders Party Good Port Technology Instrument)
  (openOrders : OpenOrders Party Good Port Technology Instrument)
  (replies : Replies Party Good Port Technology Instrument)
  (before : State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase))
  (input : Input Party Good Port Technology Instrument)

local notation "Visit" => (source tariff home orders openOrders replies before input)
local notation "After" => (next tariff home orders openOrders replies before input)
local notation "Scope" => (scope tariff home orders openOrders replies before input)
local notation "Amendment" => (amendment tariff home orders openOrders replies before input)
local notation "Landed" => (languageWrite tariff home orders openOrders replies before input)
local notation "EffectType" => Effect Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

theorem no_repair_iff_every_effect_has_an_old_expression :
    Amendment = none ↔ ∀ effect ∈ Scope,
      ∃ code : before.language.Code, effect ∈ before.language.denotes code :=
  no_repair_iff tariff home orders openOrders replies before input

theorem a_language_write_has_an_exact_expression_failure :
    (Amendment).isSome = true ↔ ∃ effect ∈ Scope,
      ∀ code : before.language.Code, effect ∉ before.language.denotes code := by
  classical
  rw [Option.isSome_iff_ne_none, ne_eq, no_repair_iff]
  constructor
  · intro novel
    obtain ⟨effect, found, missing, _⟩ := before.language.gap_not_denotable Scope novel
    exact ⟨effect, found, missing⟩
  · rintro ⟨effect, found, missing⟩ covered
    obtain ⟨code, names⟩ := covered found
    exact missing code names

theorem language_first_write (novel : ¬ Scope ⊆ before.language.covered) :
    Amendment = some Landed ∧ (After).expansion = some Landed ∧
      (After).language = before.language.repair Scope ∧
      (⟨(Visit).next.native.ledger.world, (Installation.Live.action (Visit).next.native.ledger (Landed).read true).target.targetAnswerAndNext.nextCurrent⟩ :
        AnyAuthoritativeRootCurrent) = (After).adaptive.native.ledger.resident.erase := by
  have written : Amendment = some Landed := by simp only [amendment, if_neg novel]
  refine ⟨written, ?_, ?_, ?_⟩
  · simp only [next, written]
  · rw [next, written]
    rfl
  · rw [next, written]
    exact Installation.Live.the_canonical_write_is_the_published_whole_state _ _ _

theorem language_first_write_retains_original_projections
    (novel : ¬ Scope ⊆ before.language.covered)
    (projection : (Visit).next.native.ledger.resident.root.source.base.projectionLaw.Projection) :
    let original := (Visit).next.native.ledger.resident
    let arrived := (After).adaptive.native.ledger.resident
    ∃ restriction : arrived.root.source.base.projectionLaw.Projection,
      HEq (arrived.root.source.base.projectionLaw.outcomeAt restriction
        (arrived.root.emitted arrived.visit.current))
        (original.root.source.base.projectionLaw.outcomeAt projection
          (original.root.emitted original.visit.current)) := by
  have written := (language_first_write tariff home orders openOrders replies before input novel).1
  dsimp only
  rw [next, written]
  exact ⟨.inherited (.component projection),
    Installation.Live.earlier_reads_are_kept_at_the_landing _ _ _ projection⟩

theorem the_new_language_is_the_least_exact_extension (novel : ¬ Scope ⊆ before.language.covered) :
    let revised := before.language.repair Scope
    (After).language = revised ∧
      (∀ candidate : Set EffectType, revised.covered ⊆ candidate ↔
        before.language.covered ⊆ candidate ∧ Scope ⊆ candidate) ∧
      (∀ old : before.language.Code,
        revised.denotes (before.language.inherited Scope old) = before.language.denotes old) ∧
      revised.denotes (before.language.fresh Scope) = Scope \ before.language.covered ∧
      Nonempty (RelativeExpressiveCapacity before.language.Code revised.Code Unit) := by
  refine ⟨(language_first_write tariff home orders openOrders replies before input novel).2.2.1,
    before.language.least_repair_iff Scope, before.language.denotes_inherited Scope,
    before.language.denotes_fresh Scope, ⟨before.language.capacity Scope⟩⟩

theorem keeps_every_native_word (word : Word) :
    HEq (Physical.Public.compile (After).adaptive.native.programme (After).adaptive.native.physical (.execute word))
      (Physical.Public.compile (Visit).source.next.programme (Visit).source.next.physical (.execute word)) := by
  rw [same_physical_successor, same_programme]
  exact (Visit).keeps_every_native_word word

theorem keeps_productive_capacity (person : Party) (good : Good) :
    (After).adaptive.native.recipe.gain person good = (Visit).source.next.recipe.gain person good :=
  (same_recipe_gain tariff home orders openOrders replies before input person good).trans
    ((Visit).keeps_productive_capacity person good)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace
