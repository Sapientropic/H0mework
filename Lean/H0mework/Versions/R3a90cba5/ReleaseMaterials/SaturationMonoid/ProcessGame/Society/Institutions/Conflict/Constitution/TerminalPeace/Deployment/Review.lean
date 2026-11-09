import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Opening
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Native

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material.Migration (sourceAlphabet)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Clearance.Joint.Reinterpreted
open Clearance.Joint.Reinterpreted.OriginalConsumer
open Supply.Consumers (refillWord)
open FixedPoint (KeepsPublicTerms)
open FixedPoint.OpenPeace
open FixedPoint.OpenPeace.Network
open FixedPoint.OpenPeace.Network.Runtime.Decision
open FixedPoint.NoFreeProbe (bill)
open FixedPoint.NoFreeProbe.Prepayment (CanPrepay BaseBudget registeredTerms uniform_registered_budget_iff)
open FixedPoint.OpenPeace.Network.Runtime.OriginalOrders (quote)
open private Reader.mk from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Run
open private defer from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Deferred.Start
open private afterSigned from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Reinterpreted.Consumers.OriginalDue.Settlement
open private signedStock from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Deployment.Opening
open private wireFor harmless from H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

noncomputable section

abbrev start := opening.network.state
abbrev home := opening.network.home
abbrev filed := Input.proposal (proposal home)
abbrev visit := Runtime.source home namedReplies start filed

theorem startLaw : start.current.programme = revised :=
  opening.network.programme.trans (opening.paid.sameProgramme.trans refusedLaw)

theorem startWord : start.current.recipe.move.word = refillWord := opening.network.recipeWord

private theorem consent : CanPrepay (registeredTerms : (type_of% start.current) → _)
    start.lanes.tariff.read home (filed.orders start.lanes.payment.read start.lanes.openPayment.read)
    (registeredTerms start.current) start.current.physical.raw.clock (proposal home).wire := by
  have reads := opening.network.signatures
  have stamp : (proposal home).wire.clock = start.current.physical.raw.clock := by
    rw [proposal_clock, opening.exactStock]
    decide +kernel
  refine ⟨rfl, stamp, ?_, both_original_parties_have_standing true, ?_,
    (uniform_registered_budget_iff start.current _).mpr ?_⟩
  · rw [reads.1]
    exact RevisedOrders.public_screen home 1
  · rw [reads.1, reads.2.1, reads.2.2, ← stamp]
    exact original_order home
  · have base := opening.paid.stock.trans signedStock
    rw [reads.1, startWord, congrArg (fun input => input.law) startLaw, base]
    change BaseBudget revised.law afterSigned refillWord (bill quote (wireFor harmless))
    refine ⟨?_, ?_, ?_, ⟨true, false, ?_⟩⟩
    · decide +kernel
    · intro person good
      cases person <;> cases good <;> decide +kernel
    · intro person good
      cases person <;> cases good <;> decide +kernel
    · decide +kernel

private abbrev debit :=
  (consent.budget start.current rfl rfl).write
    (start.lanes.tariff.read.positive (proposal home).wire.attempted)

private theorem posted :
    visit.source = .prepaid (proposal home).wire consent debit :=
  proposal_source_paid _ _ _ _ _ _ _ consent

theorem charged : visit.source.paidWire = some (proposal home).wire := by
  rw [posted]
  rfl

abbrev terms : Effect Bool Bool Bool Unit Unit := .inr ()

theorem originalScope : Runtime.scope home namedReplies start filed = {terms} := by
  rw [show Runtime.scope home namedReplies start filed = paidEffects debit (proposal home).programme from
    paid_proposal_scope _ _ _ _ _ _ _ posted]
  have noLosses : paidLosses debit RevisedOrders.shifted = ∅ := by
    rw [paidLosses_eq]
    apply no_rewrite_of_existing_alphabet_has_no_losses
    · exact (congrArg (fun input => input.law) startLaw).symm
    · intro request registered
      change request ∈ sourceAlphabet revised start.current.physical.raw
      rwa [startLaw] at registered
  have difference : ¬ KeepsPublicTerms start.current.programme RevisedOrders.shifted := by
    rw [startLaw]
    intro same
    have clock := congrArg (fun input => input.initial.clock) same
    change revised.initial.clock + 1 = revised.initial.clock at clock
    linarith only [clock]
  change paidEffects debit RevisedOrders.shifted = {terms}
  ext effect
  cases effect with
  | inl claim => simp [paidEffects_loss, noLosses, terms]
  | inr point =>
    cases point
    exact (paidEffects_public_terms debit RevisedOrders.shifted).trans ⟨fun _ => rfl, fun _ => difference⟩

private def reader : Reader start :=
  Reader.mk (fun point => match point with
    | .inl word => some (.isFalse (fun impossible =>
        (Set.notMem_empty (Sum.inl word : Effect Bool Bool Bool Unit Unit)) (by
          rw [← opening.network.initialLanguage]
          exact impossible)))
    | .inr _ => none) (fun _ => rfl)

abbrev deferredAnswer : Result home namedReplies start filed := .needsEvidence (proposal home).wire charged

def pending : Deferred home namedReplies start filed := defer (proposal home).wire charged

theorem the_named_review_opens_its_paid_gap :
    Runtime.Decision.advance home namedReplies start filed reader (Advice.raw start filed) [] = deferredAnswer ∧
      deferredAnswer.beginDeferred = some pending := by
  refine ⟨?_, rfl⟩
  have novel : ¬ Runtime.scope home namedReplies start filed ⊆ start.base.language.covered := by
    rw [originalScope, opening.network.initialLanguage, Set.singleton_subset_iff]
    exact Set.notMem_empty _
  apply advance_retains_an_unreadable_paid_scope _ _ _ _ _ _ _ _ charged novel
  intro point member
  rw [originalScope, Set.mem_singleton_iff] at member
  subst point
  rfl

def chargedStock : Original.Raw :=
  FixedPoint.afterCharge revised afterSigned refillWord true false [(true, 1/6), (true, 1/6), (true, 1/6)]

theorem pendingStock : pending.live.current.physical.raw = chargedStock := by
  rw [pending.physical, visit.same_physical_successor, posted]
  let funded := consent.budget start.current rfl rfl
  let charge := bill start.lanes.tariff.read (proposal home).wire
  have native := FixedPoint.charged_native_write start.current.physical start.current.move.paid funded.atCurrent
  have measured := congrArg (fun p : TerminalPeace.Universal.Runtime.Native Bool Bool Bool Unit Unit => p.raw)
    (debit.round.physicalNext.symm.trans native.2.2)
  change debit.round.next.physical.raw = _
  rw [measured]
  change FixedPoint.afterCharge start.current.programme start.current.physical.raw start.current.move.word
    charge.payer charge.port charge.expenses = chargedStock
  have word := (start.current.recipe.moveAt_word start.current.physical.raw start.current.reserved).trans startWord
  rw [word, startLaw, opening.exactStock]
  have literal : (charge.payer, charge.port, charge.expenses) =
      (true, false, [(true, 1/6), (true, 1/6), (true, 1/6)]) := by
    dsimp only [charge]
    rw [opening.network.signatures.1]
    rfl
  rw [show charge.payer = true from congrArg Prod.fst literal,
    show charge.port = false from congrArg (fun t => t.2.1) literal,
    show charge.expenses = _ from congrArg (fun t => t.2.2) literal]
  rfl

theorem pendingLaw : pending.live.current.programme = revised := by
  change visit.next.native.programme = _
  rw [visit.same_programme, posted]
  exact debit.programme.trans startLaw

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Deployment
