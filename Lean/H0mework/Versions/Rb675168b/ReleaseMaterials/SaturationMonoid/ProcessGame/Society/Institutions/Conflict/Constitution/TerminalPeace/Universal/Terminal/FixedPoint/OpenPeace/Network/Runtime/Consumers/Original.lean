import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Advance
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Fixture

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Original

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe
open NoFreeProbe.Prepayment (CanPrepay registeredTerms)
open OriginalScopes OriginalOrders
open Reparation.Transport (sourceSupport)
open Supply.Consumers (refillWord)

noncomputable section

private abbrev At := Runtime.State (seed := TerminalPeace.Original.seed) (cut := Settlement.settledCut)
  (community := TerminalPeace.Original.community) OriginalReview.origin [false, true] 1
private abbrev InputAt := OpenPeace.Input Bool Bool Bool Unit Unit
private abbrev replies := OriginalReview.personalReplies false

def initial : At := Runtime.start OriginalFixture.base OriginalFixture.lanes OriginalFixture.inherited

private abbrev submit (ordinal : Fin 3) : InputAt := .proposal (proposal ordinal)
private abbrev turn (before : At) (input : InputAt) := Runtime.advance registration replies before input
private abbrev first := turn initial (submit 0)
private abbrev second := turn first.next (submit 1)
private abbrev known := turn second.next (submit 2)

private abbrev visit (before : At) (input : InputAt) :=
  Runtime.source registration replies before input

private abbrev observed (before : At) (input : InputAt) :=
  Runtime.scope registration replies before input

private def ReadsOriginal (before : At) : Prop :=
  before.lanes.tariff.read = quote ∧ before.lanes.payment.read = payment ∧
    before.lanes.openPayment.read = openPayment

private def AtOrdinal (before : At) (ordinal : Fin 3) : Prop :=
  before.base.adaptive.native.programme = OriginalRecipe.programme ∧
    before.base.adaptive.native.recipe.move.word = refillWord ∧
    (proposal ordinal).wire.clock = before.base.adaptive.native.physical.raw.clock

private theorem initial_reads : ReadsOriginal initial :=
  OriginalFixture.reads_the_three_original_installations

private theorem initial_ordinal : AtOrdinal initial 0 := by
  refine ⟨rfl, rfl, ?_⟩
  rw [clock_at]
  exact add_zero _

private theorem consent {before : At} {ordinal : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal) :
    CanPrepay (registeredTerms : OriginalReview.State → _) before.lanes.tariff.read registration
      ((submit ordinal).orders before.lanes.payment.read before.lanes.openPayment.read)
      (registeredTerms before.base.adaptive.native) before.base.adaptive.native.physical.raw.clock
      (proposal ordinal).wire := by
  rw [reads.1, reads.2.1, reads.2.2]
  exact can_pay before.base.adaptive.native ordinal ready.2.2 ready.1 ready.2.1

private abbrev charged {before : At} {ordinal : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal) :=
  ((consent reads ready).budget before.base.adaptive.native rfl rfl).write
    (before.lanes.tariff.read.positive (proposal ordinal).wire.attempted)

private theorem receipt {before : At} {ordinal : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal) :
    (visit before (submit ordinal)).source = .prepaid (proposal ordinal).wire
      (consent reads ready) (charged reads ready) :=
  OpenPeace.proposal_source_paid _ _ _ _ _ _ _ (consent reads ready)

private theorem paid_scope {before : At} {ordinal : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal) :
    observed before (submit ordinal) = paidEffects (charged reads ready) (proposal ordinal).programme :=
  OpenPeace.paid_proposal_scope _ _ _ _ _ _ _ (receipt reads ready)

private theorem source_reads_recipe {before : At} {input : InputAt} :
    (visit before input).next.native.recipe.move.word = (visit before input).source.next.recipe.move.word := by
  generalize visit before input = selected
  cases selected <;> rfl

private theorem debit_at_six {before : At} {ordinal : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal) :
    let round := (visit before (submit ordinal)).source.round
    ∃ item, round.visit.read.effect.execution.items[6]? = some item ∧
      item.request.signer = true ∧
      round.visit.read.programme.law.actualDebit item.before item.request =
        locate true [(true, 1/6), (true, 1/6), (true, 1/6)] ∧
      round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  dsimp only
  rw [receipt reads ready]
  have actual := (charged reads ready).original_expense
  let native := before.base.adaptive.native
  have word := (native.recipe.moveAt_word native.physical.raw native.reserved).trans ready.2.1
  rw [word] at actual
  obtain ⟨item, atSix, signer, debit, credit⟩ := actual
  have price : locate (bill before.lanes.tariff.read (proposal ordinal).wire).payer
      (bill before.lanes.tariff.read (proposal ordinal).wire).expenses =
        locate true [(true, 1/6), (true, 1/6), (true, 1/6)] := by
    rw [reads.1]
    rfl
  exact ⟨item, atSix, signer, debit.trans price, credit⟩

private theorem source_unpaid {before : At}
    (attempt : OpenPeace.Proposal Bool Bool Bool Unit Unit)
    (absent : ¬ CanPrepay (registeredTerms : OriginalReview.State → _) before.lanes.tariff.read registration
      ((Input.proposal attempt).orders before.lanes.payment.read before.lanes.openPayment.read)
      (registeredTerms before.base.adaptive.native) before.base.adaptive.native.physical.raw.clock attempt.wire) :
    (visit before (.proposal attempt)).source.paidWire = none := by
  let now := before.base.adaptive.native
  have denied := (Prepayment.inspectOrder_none_iff
    (registeredTerms : OriginalReview.State → _) before.lanes.tariff.read registration
    ((Input.proposal attempt).orders before.lanes.payment.read before.lanes.openPayment.read)
    (registeredTerms now) now.physical.raw.clock attempt.wire).mpr absent
  rw [visit, Runtime.source, OpenPeace.source, AdaptivePeace.advance, AdaptivePeace.resolve_keeps_the_actual_source,
    Prepayment.registered_dispatch_is_the_exact_private_dispatch, Prepayment.charged_wire_is_the_selected_order]
  have renewal : (Prepayment.ordinary before.lanes.tariff.read
      ((Input.proposal attempt).replies replies) now none).reply = .renewed := rfl
  dsimp only [now] at renewal denied
  simp [Input.due, Prepayment.selected, Prepayment.selectInAgenda, Prepayment.selectOrder, renewal, denied]

private theorem next_ordinal {before : At} {ordinal following : Fin 3}
    (reads : ReadsOriginal before) (ready : AtOrdinal before ordinal)
    (tick : following.val = ordinal.val + 1) :
    AtOrdinal (turn before (submit ordinal)).next following := by
  let landed := (turn before (submit ordinal)).next.current
  let selected := visit before (submit ordinal)
  have stateProgramme := Runtime.same_programme registration replies before (submit ordinal)
  have stateWord := Runtime.same_recipe_word registration replies before (submit ordinal)
  have statePhysical := Runtime.same_physical registration replies before (submit ordinal)
  have keptProgramme : selected.source.next.programme = before.current.programme := by
    rw [receipt reads ready]
    exact (charged reads ready).programme
  have keptWord : selected.source.next.recipe.move.word = before.current.recipe.move.word := by
    rw [receipt reads ready]
    rfl
  have physicalClock : selected.source.next.physical.raw.clock = before.current.move.next.clock := by
    rw [receipt reads ready]
    exact (charged reads ready).settledClock
  refine ⟨stateProgramme.trans (selected.same_programme.trans (keptProgramme.trans ready.1)),
    stateWord.trans (source_reads_recipe.trans (keptWord.trans ready.2.1)), ?_⟩
  change (proposal following).wire.clock = landed.physical.raw.clock
  rw [statePhysical, selected.same_physical_successor, physicalClock, next_clock before.current ready.1,
    ← ready.2.2, clock_at, clock_at]
  have elapsed : (following.val : ℚ) = (ordinal.val : ℚ) + 1 := by exact_mod_cast tick
  rw [elapsed, ← add_assoc]

private theorem first_exit_observed : exitEffect ∈ observed initial (submit 0) := by
  rw [paid_scope initial_reads initial_ordinal]
  exact dropLocal_paid_has_exit (charged initial_reads initial_ordinal) rfl

private theorem first_terms_absent : termsEffect ∉ observed initial (submit 0) := by
  rw [paid_scope initial_reads initial_ordinal]
  exact dropLocal_paid_has_no_terms (charged initial_reads initial_ordinal) rfl

private theorem first_novel : ¬ observed initial (submit 0) ⊆ initial.base.language.covered := by
  intro covered
  have impossible := covered first_exit_observed
  change exitEffect ∈ (Language.initial : Language (RawEvent Bool Bool Bool Unit Unit)
    (Effect Bool Bool Bool Unit Unit)).covered at impossible
  rw [Language.covered_initial] at impossible
  exact impossible

private theorem terms_are_new_after_the_first_write : termsEffect ∉ first.next.base.language.covered := by
  rw [Runtime.coverage_eq]
  change termsEffect ∉ (Language.initial : Language (RawEvent Bool Bool Bool Unit Unit)
    (Effect Bool Bool Bool Unit Unit)).covered ∪ observed initial (submit 0)
  rw [Language.covered_initial, Set.empty_union]
  exact first_terms_absent

private theorem first_landing_reads : ReadsOriginal first.next := by
  unfold ReadsOriginal
  obtain ⟨sameTariff, samePayment, sameOpen⟩ :=
    Runtime.next_keeps_original_signatures registration replies initial (submit 0)
  exact ⟨sameTariff.trans initial_reads.1, samePayment.trans initial_reads.2.1, sameOpen.trans initial_reads.2.2⟩

private theorem second_ordinal : AtOrdinal first.next 1 :=
  next_ordinal initial_reads initial_ordinal rfl

private theorem second_scope : observed first.next (submit 1) = {termsEffect} := by
  rw [paid_scope first_landing_reads second_ordinal]
  exact shifted_paid_scope (charged first_landing_reads second_ordinal) second_ordinal.1

private theorem second_novel : ¬ observed first.next (submit 1) ⊆ first.next.base.language.covered := by
  rw [second_scope, Set.singleton_subset_iff]
  exact terms_are_new_after_the_first_write

private theorem second_landing_reads : ReadsOriginal second.next := by
  unfold ReadsOriginal
  obtain ⟨sameTariff, samePayment, sameOpen⟩ :=
    Runtime.next_keeps_original_signatures registration replies first.next (submit 1)
  exact ⟨sameTariff.trans first_landing_reads.1, samePayment.trans first_landing_reads.2.1,
    sameOpen.trans first_landing_reads.2.2⟩

private theorem third_ordinal : AtOrdinal second.next 2 :=
  next_ordinal first_landing_reads second_ordinal rfl

private theorem terms_are_already_sealed : termsEffect ∈ second.next.base.language.covered := by
  rw [Runtime.coverage_eq]
  have sealed : termsEffect ∈ observed first.next (submit 1) := second_scope.symm ▸ Set.mem_singleton _
  exact Set.mem_union_right _ sealed

private theorem covered_write {before : At} {input : InputAt}
    (covered : observed before input ⊆ before.base.language.covered) :
    (turn before input).write = none := by
  classical
  unfold turn Runtime.advance
  simp only [dif_neg (not_not.mpr covered)]

private theorem keeps_rows (before : At) (input : InputAt) :
    (turn before input).next.current.ledger.stack.balances = before.current.ledger.stack.balances := by
  let selected := visit before input
  have rows : selected.next.native.ledger.stack.balances = selected.source.next.ledger.stack.balances := by
    cases selected <;> rfl
  exact (Runtime.same_rows registration replies before input).trans (rows.trans selected.source.rows)

/-- Each request actually pays at original material position six.
The second payment starts on the first generated U8 resident. -/
theorem two_paid_gaps_reenter_the_material_dispatcher :
    let firstRevision := (Runtime.revision registration replies initial (submit 0) first_novel).generate
    let secondRevision := (Runtime.revision registration replies first.next (submit 1) second_novel).generate
    let secondRound := (visit first.next (submit 1)).source.round
    (⟨firstRevision.NewN, firstRevision.newLivingRoot.generatedNextCurrentAt
      (.finite firstRevision.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      first.next.current.ledger.resident.erase ∧
    (⟨secondRevision.NewN, secondRevision.newLivingRoot.generatedNextCurrentAt
      (.finite secondRevision.newRoot.toRoot.initialVisit)⟩ : AnyAuthoritativeRootCurrent) =
      second.next.current.ledger.resident.erase ∧
    secondRound.next.ledger =
      (Installation.Live.publish first.next.current.ledger secondRound.visit.read true).state ∧
    first.next.current.ledger.stack.balances = [(TerminalPeace.Original.occurrence, Settlement.clearedBalance)] ∧
    second.next.current.ledger.stack.balances = [(TerminalPeace.Original.occurrence, Settlement.clearedBalance)] ∧
    (visit initial (submit 0)).source.paidWire = some (proposal 0).wire ∧
    (visit first.next (submit 1)).source.paidWire = some (proposal 1).wire := by
  have originalRows := OriginalFixture.opening_keeps_the_original_settlement.trans Settlement.settled_balances
  have firstRows := (keeps_rows initial (submit 0)).trans originalRows
  have secondRows := keeps_rows first.next (submit 1)
  exact ⟨Runtime.next_reads_generated_first_write registration replies initial (submit 0) first_novel,
    Runtime.next_reads_generated_first_write registration replies first.next (submit 1) second_novel,
    (visit first.next (submit 1)).source.round.ledgerNext, firstRows, secondRows.trans firstRows,
    congrArg Prepayment.Step.paidWire (receipt initial_reads initial_ordinal),
    congrArg Prepayment.Step.paidWire (receipt first_landing_reads second_ordinal)⟩

theorem the_original_cleared_debt_has_a_live_address_after_two_revisions :
    let ledger := second.next.current.ledger
    ∃ original, ledger.stack.read (sourceSupport Settlement.settledCut.native) original =
      .inr (TerminalPeace.Original.occurrence, Settlement.clearedBalance) ∧
      ∃ live : OpenResponsibilityAt ledger.world ledger.resident.support,
        live = ledger.originalRow original ∧ live.progressBudget = original.progressBudget := by
  have originalRows := OriginalFixture.opening_keeps_the_original_settlement.trans Settlement.settled_balances
  have firstRows := (keeps_rows initial (submit 0)).trans originalRows
  have secondRows := (keeps_rows first.next (submit 1)).trans firstRows
  apply second.next.current.ledger.every_balance_has_a_live_row
  rw [secondRows]
  exact List.mem_cons_self

theorem both_revisions_consume_an_original_half_unit_debit :
    ∀ cut : Fin 2,
      let round := if cut.val = 0 then (visit initial (submit 0)).source.round.visit.read
        else (visit first.next (submit 1)).source.round.visit.read
      ∃ item, round.effect.execution.items[6]? = some item ∧
        item.request.signer = true ∧
        round.programme.law.actualDebit item.before item.request =
          locate true [(true, 1/6), (true, 1/6), (true, 1/6)] ∧
        round.programme.law.actualCredit item.before item.request = [] := by
  intro cut
  have value : cut.val = 0 ∨ cut.val = 1 := by have bound := cut.isLt; omega
  rcases value with zero | one
  · rw [if_pos zero]
    exact debit_at_six initial_reads initial_ordinal
  · rw [if_neg (by omega)]
    exact debit_at_six first_landing_reads second_ordinal

/-- A fresh authorized repetition is charged in the second revised world
and consumes its already installed refusal language. -/
theorem the_covered_request_still_pays_without_a_third_revision :
    (visit second.next (submit 2)).source.paidWire = some (proposal 2).wire ∧
      known.write = none := by
  refine ⟨congrArg Prepayment.Step.paidWire (receipt second_landing_reads third_ordinal), ?_⟩
  apply covered_write
  rw [paid_scope second_landing_reads third_ordinal]
  change paidEffects (charged second_landing_reads third_ordinal) shifted ⊆ second.next.base.language.covered
  rw [shifted_paid_scope (charged second_landing_reads third_ordinal) third_ordinal.1]
  exact Set.singleton_subset_iff.mpr terms_are_already_sealed

private theorem wrong_unpaid :
    (visit first.next (.proposal (wrongSigner 1))).source.paidWire = none := by
  apply source_unpaid
  intro authorized
  have own := authorized.ownOrder
  rw [first_landing_reads.1, first_landing_reads.2.1, first_landing_reads.2.2] at own
  have absent := wrong_signer_has_no_order 1 first.next.current.physical.raw.clock
  exact Bool.false_ne_true (absent.symm.trans own)

private theorem stale_unpaid : (visit second.next (submit 1)).source.paidWire = none := by
  apply source_unpaid
  intro authorized
  have stale := authorized.stamp
  rw [← third_ordinal.2.2, clock_at, clock_at] at stale
  change OriginalReview.initial.physical.raw.clock + (1 : ℚ) =
    OriginalReview.initial.physical.raw.clock + 2 at stale
  linarith only [stale]

private theorem unpaid_write {before : At} (attempt : OpenPeace.Proposal Bool Bool Bool Unit Unit)
    (unpaid : (visit before (.proposal attempt)).source.paidWire = none) :
    (turn before (.proposal attempt)).write = none :=
  (Runtime.unpaid_keeps_its_material_next registration replies before (.proposal attempt) unpaid).1

theorem the_revised_resident_erases_wrong_signer_and_stale_orders :
    fundingScreen quote (wrongSigner 1).wire = true ∧
      (wrongSigner 1).wire.clock = first.next.current.physical.raw.clock ∧
      (visit first.next (.proposal (wrongSigner 1))).source.paidWire = none ∧
      (turn first.next (.proposal (wrongSigner 1))).write = none ∧
      (visit second.next (submit 1)).source.paidWire = none ∧
      (turn second.next (submit 1)).write = none :=
  ⟨wrong_signer_passes_public_screen 1, second_ordinal.2.2, wrong_unpaid,
    unpaid_write _ wrong_unpaid, stale_unpaid, unpaid_write _ stale_unpaid⟩

end

-- These signatures are consumed explicitly and contain the fully dependent
-- two-revision ledger. The generic premise index overflows on their types.
run_cmd Lean.modifyEnv fun env =>
  let names := ["two_paid_gaps_reenter_the_material_dispatcher",
    "the_original_cleared_debt_has_a_live_address_after_two_revisions"]
  names.foldl (fun env name => Lean.LibrarySuggestions.nameDenyListExt.addEntry env name) env

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Original
