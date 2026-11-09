import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalNetwork
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Payment

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open FixedPoint (KeepsPublicTerms)
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.NoFreeProbe (bill)
open FixedPoint.NoFreeProbe.Prepayment (BaseBudget CanPrepay registeredTerms uniform_registered_budget_iff)
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open RevisedOrders (openPayment)
open Supply.Consumers (refillWord)
open private wireFor harmless from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

noncomputable section

private abbrev start := actualNetwork.network.state
private abbrev home := actualNetwork.network.home
private abbrev At := type_of% start
private abbrev CurrentAt := type_of% start.current
private abbrev packet (slot : Fin 2) := RevisedOrders.proposal home slot
private abbrev submit (slot : Fin 2) := Input.proposal (packet slot)
private abbrev visit (before : At) (slot : Fin 2) := Runtime.source home namedReplies before (submit slot)
private abbrev turn (before : At) (slot : Fin 2) := Runtime.advance home namedReplies before (submit slot)
private abbrev scope (before : At) (slot : Fin 2) := Runtime.scope home namedReplies before (submit slot)

private def ReadsOriginal (state : At) : Prop :=
  state.lanes.tariff.read = quote ∧ state.lanes.payment.read = Runtime.OriginalOrders.payment ∧
    state.lanes.openPayment.read = openPayment

private def ReadyAt (state : At) (slot : Fin 2) : Prop :=
  state.current.programme = revised ∧ state.current.recipe.move.word = refillWord ∧
    (packet slot).wire.clock = state.current.physical.raw.clock

private theorem initial_reads : ReadsOriginal start := actualNetwork.network.signatures

private theorem initial_ready : ReadyAt start 0 := by
  refine ⟨actualNetwork.network.programme.trans
    (actualNetwork.paid.sameProgramme.trans actualTrial.revisedProgramme), actualNetwork.network.recipeWord, ?_⟩
  rw [RevisedOrders.original_clock, actualNetwork.actualStock]
  decide +kernel

private theorem can_file {before : At} {slot : Fin 2} (reads : ReadsOriginal before) (ready : ReadyAt before slot) :
    CanPrepay (registeredTerms : CurrentAt → _) before.lanes.tariff.read home
      ((submit slot).orders before.lanes.payment.read before.lanes.openPayment.read)
      (registeredTerms before.current) before.current.physical.raw.clock (packet slot).wire := by
  refine ⟨rfl, ready.2.2, ?_, both_original_parties_have_standing true, ?_,
    (uniform_registered_budget_iff before.current _).mpr ?_⟩
  · rw [reads.1]
    exact RevisedOrders.public_screen home slot
  · rw [reads.1, reads.2.1, reads.2.2, ← ready.2.2]
    exact RevisedOrders.original_orders_apply home slot
  · rw [reads.1, ready.2.1, congrArg (fun input => input.law) ready.1,
      payment_lands_at_the_actual_stock actualNetwork.paid]
    change BaseBudget revised.law afterClear refillWord (bill quote (wireFor harmless))
    refine ⟨?_, ?_, ?_, ⟨true, false, ?_⟩⟩
    · decide +kernel
    · intro person good
      cases person <;> cases good <;> decide +kernel
    · intro person good
      cases person <;> cases good <;> decide +kernel
    · decide +kernel

private abbrev debit {before : At} {slot : Fin 2} (reads : ReadsOriginal before) (ready : ReadyAt before slot) :=
  ((can_file reads ready).budget before.current rfl rfl).write
    (before.lanes.tariff.read.positive (packet slot).wire.attempted)

private theorem posted {before : At} {slot : Fin 2} (reads : ReadsOriginal before) (ready : ReadyAt before slot) :
    (visit before slot).source = .prepaid (packet slot).wire (can_file reads ready) (debit reads ready) :=
  proposal_source_paid _ _ _ _ _ _ _ (can_file reads ready)

private theorem paid_scope {before : At} {slot : Fin 2} (reads : ReadsOriginal before) (ready : ReadyAt before slot) :
    scope before slot = paidEffects (debit reads ready) (packet slot).programme :=
  paid_proposal_scope _ _ _ _ _ _ _ (posted reads ready)

private theorem paid_wire {before : At} {slot : Fin 2} (reads : ReadsOriginal before) (ready : ReadyAt before slot) :
    (visit before slot).source.paidWire = some (packet slot).wire := by
  rw [posted reads ready]
  rfl

private abbrev termsEffect : Effect Bool Bool Bool Unit Unit := .inr ()

private theorem first_scope : scope start 0 = {termsEffect} := by
  rw [paid_scope initial_reads initial_ready]
  let paid := debit initial_reads initial_ready
  have noLosses : paidLosses paid RevisedOrders.shifted = ∅ := by
    rw [paidLosses_eq]
    apply no_rewrite_of_existing_alphabet_has_no_losses
    · exact (congrArg (fun input => input.law) initial_ready.1).symm
    · intro request registered
      change request ∈ sourceAlphabet revised start.current.physical.raw
      rwa [initial_ready.1] at registered
  have terms : ¬ KeepsPublicTerms start.current.programme RevisedOrders.shifted := by
    rw [initial_ready.1]
    intro same
    have clock := congrArg (fun input => input.initial.clock) same
    change revised.initial.clock + 1 = revised.initial.clock at clock
    linarith only [clock]
  change paidEffects paid RevisedOrders.shifted = {termsEffect}
  ext effect
  cases effect with
  | inl claim => simp [paidEffects_loss, noLosses, termsEffect]
  | inr term =>
    cases term
    exact (paidEffects_public_terms paid RevisedOrders.shifted).trans ⟨fun _ => rfl, fun _ => terms⟩

private theorem first_novel : ¬ scope start 0 ⊆ start.base.language.covered := by
  rw [first_scope, actualNetwork.network.initialLanguage, Set.singleton_subset_iff]
  exact Set.notMem_empty _

private abbrev first := (turn start 0).next

private theorem first_reads : ReadsOriginal first := by
  have kept := Runtime.next_keeps_original_signatures home namedReplies start (submit 0)
  exact ⟨kept.1.trans initial_reads.1, kept.2.1.trans initial_reads.2.1, kept.2.2.trans initial_reads.2.2⟩

private theorem first_ready : ReadyAt first 1 := by
  let step := visit start 0
  have program : step.source.next.programme = start.current.programme := by
    rw [posted initial_reads initial_ready]
    exact (debit initial_reads initial_ready).programme
  have word : step.source.next.recipe.move.word = start.current.recipe.move.word := by
    rw [posted initial_reads initial_ready]
    rfl
  have keepsWord : step.next.native.recipe.move.word = step.source.next.recipe.move.word := by
    generalize step = selected
    cases selected <;> rfl
  refine ⟨(Runtime.same_programme home namedReplies start (submit 0)).trans
    (step.same_programme.trans (program.trans initial_ready.1)),
    (Runtime.same_recipe_word home namedReplies start (submit 0)).trans (keepsWord.trans (word.trans initial_ready.2.1)), ?_⟩
  have clock : step.source.next.physical.raw.clock = start.current.move.next.clock := by
    rw [posted initial_reads initial_ready]
    exact (debit initial_reads initial_ready).settledClock
  have tick : start.current.move.next.clock = start.current.physical.raw.clock + 1 := by
    change (start.current.programme.law.next start.current.physical.raw start.current.move.word).clock = _
    rw [congrArg (fun input => input.law) initial_ready.1]
    change start.current.physical.raw.clock + max 0 (1 : ℚ) = _
    norm_num
  change (packet 1).wire.clock = first.current.physical.raw.clock
  rw [Runtime.same_physical, step.same_physical_successor, clock, tick, actualNetwork.actualStock,
    RevisedOrders.original_clock]
  decide +kernel

private def schedule : Policy Bool Bool Bool Unit Unit :=
  fun n _ _ _ _ => if n = 0 then submit 0 else if n = 1 then submit 1 else .native ⟨none, []⟩

theorem the_revised_original_stock_generates_a_paid_u8_and_its_next :
    (visit start 0).source.paidWire = some (packet 0).wire ∧ (turn start 0).write.isSome = true ∧
    (liveHistory schedule 1).1.current.ledger = (Runtime.languageWrite home namedReplies start (submit 0) first_novel).state ∧
    (liveHistory schedule 2).1.current.ledger.stack.balances = actualNetwork.paid.next.ledger.stack.balances :=
  ⟨paid_wire initial_reads initial_ready, (Runtime.write_iff home namedReplies start (submit 0)).mpr first_novel,
    Runtime.next_ledger home namedReplies start (submit 0) first_novel,
    (Runtime.history_keeps_rows home namedReplies start schedule 2).trans actualNetwork.network.rows⟩

theorem the_u8_first_write_is_the_next_rounds_whole_input :
    let ledger := (Runtime.languageWrite home namedReplies start (submit 0) first_novel).state
    let round := (visit first 1).source.round
    let action := Installation.Live.action ledger round.visit.read true
    (⟨ledger.world, action.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      round.next.ledger.resident.erase := by
  exact (Runtime.the_revised_resident_drives_the_next_material_write home namedReplies start schedule 0 first_novel).1

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted.OriginalConsumer
