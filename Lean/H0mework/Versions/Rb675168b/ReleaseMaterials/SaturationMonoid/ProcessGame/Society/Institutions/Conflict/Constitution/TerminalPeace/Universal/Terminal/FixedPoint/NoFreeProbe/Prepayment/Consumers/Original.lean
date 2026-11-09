import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Dispatch
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Original

open Capitalism.Universal.Source.Program
open Conflict.Consumers.Evolving (levy)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

open private current tariff wireFor admits_one originalPaid renewal_word from
  H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Consumers.Original

noncomputable section

private abbrev Packet := Wire Bool Bool Bool Unit Unit
private abbrev RepliesAt := Replies Bool Bool Bool Unit Unit
private abbrev home := current.ledger.resident.erase
private abbrev originalWire := wireFor levy
private abbrev see : OriginalReview.State →
    RawLaw Bool Bool Bool Unit Unit × RawEvent Bool Bool Bool Unit Unit := registeredTerms

private def signedOrder (wire : Packet) : PaymentOrders Bool Bool Bool Unit Unit := by
  classical
  exact fun now billed person =>
    decide (now = wire.clock ∧ billed = bill tariff wire ∧ person = wire.payer)

private theorem own_literal_order (wire : Packet) :
    signedOrder wire wire.clock (bill tariff wire) wire.payer = true := by
  simp [signedOrder]

private theorem original_budget :
    BaseBudget current.programme.law Settlement.settledCut.raw current.recipe.move.word (bill tariff originalWire) := by
  let admitted := admits_one levy
  refine ⟨?_, admitted.fits.1, admitted.fits.2, admitted.surplus⟩
  have legal := admitted.legal
  unfold ReviewLegal at legal
  rw [renewal_word] at legal
  exact legal

private theorem consented :
    CanPrepay see tariff home (signedOrder originalWire) (see current)
      current.physical.raw.clock originalWire :=
  ⟨rfl, rfl, (admits_one levy).passes_public_screen, (admits_one levy).standing,
    own_literal_order originalWire, (uniform_registered_budget_iff current _).mpr original_budget⟩

private abbrev charge : PaidReview current (bill tariff originalWire) :=
  (consented.budget current rfl rfl).write (tariff.positive originalWire.attempted)

private def withOriginalOrder (replies : RepliesAt) :=
  advance tariff replies current see home (signedOrder originalWire) ⟨none, [originalWire]⟩

private theorem protected_writes (replies : RepliesAt) :
    withOriginalOrder replies = .prepaid originalWire consented charge := by
  have inspected : inspectOrder see tariff home (signedOrder originalWire)
      (see current) current.physical.raw.clock originalWire = some ⟨originalWire, consented⟩ := by
    simp [inspectOrder, consented, consented.screened]
  have renews : (ordinary tariff replies current none).reply = .renewed := rfl
  have selection : selected tariff replies current see home (signedOrder originalWire)
      ⟨none, [originalWire]⟩ = some ⟨originalWire, consented⟩ := by
    simp [selected, selectInAgenda, renews, selectOrder, inspected]
  simp only [withOriginalOrder, advance, selection, writeSelected, charge]

/-- Both private answers consume the same literal order at the same
original cut. Eligibility changes the published verdict only. -/
theorem the_original_private_answers_share_one_paid_physical_write :
    let denied := withOriginalOrder (OriginalReview.personalReplies false)
    let approved := withOriginalOrder (OriginalReview.personalReplies true)
    denied.reply = .prepaid .ineligible ∧ approved.reply = .prepaid (.reviewed true) ∧
      denied.paidWire = some originalWire ∧ approved.paidWire = some originalWire ∧
      denied.next.physical = approved.next.physical ∧
      denied.observe.landsAt = current.move.next.clock ∧ approved.observe.landsAt = current.move.next.clock ∧
      denied.next.ledger.stack.balances = current.ledger.stack.balances ∧
      approved.next.ledger.stack.balances = current.ledger.stack.balances := by
  dsimp only
  rw [protected_writes (OriginalReview.personalReplies false), protected_writes (OriginalReview.personalReplies true)]
  have deny := (assessment_ineligible_iff (OriginalReview.personalReplies false) charge).mpr rfl
  have yes := (assessment_reviewed_iff (OriginalReview.personalReplies true) charge true).mpr
    ⟨rfl, charge.answer_iff.mpr originalPaid.demand⟩
  exact ⟨congrArg Reply.prepaid deny, congrArg Reply.prepaid yes, rfl, rfl, rfl,
    assessment_exact_clock _ charge, assessment_exact_clock _ charge,
    assessment_rows _ charge, assessment_rows _ charge⟩

/-- Each private answer leaves the same half unit at the actual position
of the original debit, with no credit to the filing payer. -/
theorem every_private_answer_posts_the_original_half_debit (replies : RepliesAt) :
    let step := withOriginalOrder replies
    step.next.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) ∧
      ∃ item, step.round.visit.read.effect.execution.items[6]? = some item ∧
        item.request.signer = true ∧
        step.round.visit.read.programme.law.actualDebit item.before item.request =
          locate true [(true, 1/6), (true, 1/6), (true, 1/6)] ∧
        step.round.visit.read.programme.law.actualCredit item.before item.request = [] := by
  dsimp only
  rw [protected_writes replies]
  have half : (bill tariff originalWire).fee true true = (1/2 : ℚ) := by decide +kernel
  obtain ⟨item, atSix, signer, debit, credit⟩ := (assessment_original_expense replies charge).2
  rw [renewal_word] at atSix
  exact ⟨(assessment_stock replies charge true true).trans (congrArg Neg.neg half),
    item, atSix, signer, debit, credit⟩

private def oversized : Packet :=
  { originalWire with attempted := [levy, levy, levy, levy], tender := [(true, 3/2)] }

private theorem oversized_has_no_budget :
    ¬ BaseBudget current.programme.law Settlement.settledCut.raw current.recipe.move.word (bill tariff oversized) := by
  intro budget
  have fits := budget.fits true true
  change (bill tariff oversized).fee true true ≤ (OriginalRecipe.originalRecipe OriginalReview.origin).gain true true at fits
  have billAmount : (bill tariff oversized).fee true true = (3/2 : ℚ) := by decide +kernel
  rw [billAmount, OriginalRecipe.exact_gain] at fits
  norm_num at fits

/-- Even a personally signed tender covering the full displayed charge
erases when that charge would exhaust the original production budget. -/
theorem full_but_unspendable_tender_leaves_the_exact_ordinary_write (replies : RepliesAt) :
    fundingScreen tariff oversized = true ∧
      signedOrder oversized current.physical.raw.clock (bill tariff oversized) true = true ∧
      advance tariff replies current see home (signedOrder oversized) ⟨none, [oversized]⟩ =
        .ordinary (ordinary tariff replies current none) (ordinary_has_no_charge tariff replies current none) := by
  have noOrder : inspectOrder see tariff home (signedOrder oversized) (see current)
      current.physical.raw.clock oversized = none := by
    apply (inspectOrder_none_iff see tariff home (signedOrder oversized) _ _ _).mpr
    intro admitted
    exact oversized_has_no_budget ((uniform_registered_budget_iff current _).mp admitted.budget)
  refine ⟨by decide +kernel, own_literal_order oversized, ?_⟩
  apply unpaid_order_is_the_exact_ordinary_write
  rw [charged_wire_is_the_selected_order]
  simp [selected, selectInAgenda, selectOrder, noOrder]

/-- In the earlier dispatch, a nominally funded levy could read the
private qualification by observing the presence of the unpaid refusal. -/
theorem the_earlier_dispatch_distinguishes_the_private_answer_before_payment :
    (NoFreeProbe.advance tariff (OriginalReview.personalReplies true) current ⟨none, [originalWire]⟩).reply =
      .reviewed true ∧
    (NoFreeProbe.advance tariff (OriginalReview.personalReplies false) current ⟨none, [originalWire]⟩).reply =
      .renewed ∧
    (NoFreeProbe.advance tariff (OriginalReview.personalReplies false) current ⟨none, [originalWire]⟩).paidWire =
      none := by
  have refused := NoFreeProbe.Original.a_matching_wire_name_without_the_original_personal_reply_erases
  exact ⟨NoFreeProbe.Original.the_original_levy_posts_half_before_the_positive_reply.1,
    congrArg NoFreeProbe.Step.reply refused, congrArg NoFreeProbe.Step.paidWire refused⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Prepayment.Original
