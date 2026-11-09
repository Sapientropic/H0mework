import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Consumers.Work

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Original

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Continuation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Prepayment
open Supply.Consumers (refillWord)
open Conflict.Consumers.Evolving (levy)

noncomputable section

private abbrev base := OriginalReview.initial
private abbrev replies := OriginalReview.personalReplies false
private abbrev PacketAt := Wire Bool Bool Bool Unit Unit
private abbrev WorkWord := RawEvent Bool Bool Bool Unit Unit

private def orders : PaymentOrders Bool Bool Bool Unit Unit :=
  fun clock _ payer => payer && decide (clock = base.physical.raw.clock)

private def quoteWrite := Installation.Live.publish base.ledger quote true
private def ordersWrite := Installation.Live.publish quoteWrite.state orders true
private def now : OriginalReview.State := { base with ledger := ordersWrite.state }
private abbrev home := now.ledger.resident.erase

private def post (word : WorkWord) : PacketAt :=
  ⟨home, now.physical.raw.clock, true, true, word, (quote.parts word).bundle⟩

private theorem paid_parts : quote.parts [levy] = ⟨[(true,1/4)], [(true,1/2)], []⟩ := by
  simp only [quote, Tariff.parts, Desk.tariff, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    filing_bundle, examination_bundle]

private theorem exactBudget : BaseBudget now.programme.law Settlement.settledCut.raw
    now.recipe.move.word (bill quote (post [levy])) := by
  apply (budgetCheck_iff _ _ _ _).mp
  change budgetCheck OriginalRecipe.programme.law Settlement.settledCut.raw refillWord
    ⟨true, [levy], false, quote.parts [levy]⟩ = true
  rw [paid_parts, Settlement.settled_raw]
  decide +kernel

private theorem admitted :
    CanPrepay (registeredTerms : OriginalReview.State → _) quote home ordersWrite.read
      (registeredTerms now) now.physical.raw.clock (post [levy]) := by
  refine ⟨rfl, rfl, ?_, List.mem_cons_of_mem _ List.mem_cons_self, ?_,
    (uniform_registered_budget_iff now (bill quote (post [levy]))).mpr exactBudget⟩
  · simp [fundingScreen, post, bill, ReviewBid.expenses]
  · rw [show ordersWrite.read = orders from Installation.Live.publish_reads_the_exact_payload _ _ _]
    change (true && decide (base.physical.raw.clock = base.physical.raw.clock)) = true
    simp

private def paid := exactBudget.write (quote.positive [levy])

private def visit (word : WorkWord) :=
  advanceRegistered quoteWrite.read home ordersWrite.read now replies ⟨none, [post word]⟩

private theorem selects_the_original_work :
    visit [levy] = .prepaid (post [levy]) admitted paid := by
  rw [visit, registered_dispatch_is_the_exact_private_dispatch]
  change Prepayment.advance quote replies now registeredTerms home ordersWrite.read
    ⟨none, [post [levy]]⟩ = _
  have checked : inspectOrder (registeredTerms : OriginalReview.State → _) quote home ordersWrite.read
      (registeredTerms now) now.physical.raw.clock (post [levy]) = some ⟨post [levy], admitted⟩ := by
    simp [inspectOrder, admitted, admitted.screened]
  have renewed : (ordinary quote replies now none).reply = .renewed := rfl
  have pick : selected quote replies now registeredTerms home ordersWrite.read
      ⟨none, [post [levy]]⟩ = some ⟨post [levy], admitted⟩ := by
    simp [selected, selectInAgenda, renewed, selectOrder, checked]
  simp only [Prepayment.advance, pick, writeSelected, paid]
  rfl

/-- The fee computed from the original work is posted at the one native
cost position before the private refusal. -/
theorem original_metered_review_is_paid_once :
    let actual := visit [levy]
    actual.paidWire = some (post [levy]) ∧ actual.reply = .prepaid .ineligible ∧
    now.move.next.stock true true - actual.next.physical.raw.stock true true = (3/4 : ℚ) ∧
    actual.next.ledger.stack.balances = now.ledger.stack.balances ∧
    actual.next.physical.raw.clock = now.move.next.clock ∧
    ∃ item, actual.round.visit.read.effect.execution.items[now.move.word.length]? = some item ∧
      actual.round.visit.read.programme.law.actualDebit item.before item.request =
        locate true [(true,1/4), (true,1/2)] := by
  dsimp only
  rw [selects_the_original_work]
  have actual := actual_paid_work_has_one_original_debit desk the_original_filing_has_real_cost paid
  have quantity : desk.actualCost [levy] true = (3/4 : ℚ) := by
    rw [← desk.exact_quote the_original_filing_has_real_cost]
    change amount Bool (quote.parts [levy]).bundle true = _
    rw [one_original_request_costs_three_quarters]
    decide +kernel
  obtain ⟨item, atCost, _, debit, _⟩ := actual.2.2.2.2
  change paid.round.visit.read.programme.law.actualDebit item.before item.request =
    locate true (desk.filing.bundle ++ [levy].flatMap (fun req => (desk.review req).bundle)) at debit
  simp only [filing_bundle, List.flatMap_cons, examination_bundle, List.flatMap_nil, List.append_nil] at debit
  have denied := (assessment_ineligible_iff replies paid).mpr rfl
  exact ⟨rfl, congrArg Reply.prepaid denied, (actual.2.2.1 true).trans quantity, assessment_rows replies paid,
    actual.2.1, item, atCost, debit⟩

private theorem tooMuch :
    ¬ BaseBudget now.programme.law Settlement.settledCut.raw now.recipe.move.word
      (bill quote (post [levy, levy])) := by
  intro admitted
  have measured := admitted.fits true true
  have costs : quote.parts [levy, levy] = ⟨[(true,1/4)], [(true,1/2),(true,1/2)], []⟩ := by
    simp only [quote, Tariff.parts, Desk.tariff, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      filing_bundle, examination_bundle]
    rfl
  change amount Bool (quote.parts [levy, levy]).bundle true ≤
    Balance.gain OriginalRecipe.programme.law Settlement.settledCut.raw refillWord true true at measured
  have gain := OriginalRecipe.exact_gain OriginalReview.origin true true
  change Balance.gain OriginalRecipe.programme.law Settlement.settledCut.raw refillWord true true = 1 at gain
  rw [costs, gain] at measured
  exact (show ¬ amount Bool ([(true,1/4),(true,1/2),(true,1/2)] : Bundle Bool) true ≤ 1 from by
    decide +kernel) measured

theorem unaffordable_metered_work_cannot_be_prepaid :
    (visit [levy, levy]).paidWire = none := by
  rw [visit, registered_dispatch_is_the_exact_private_dispatch, charged_wire_is_the_selected_order]
  change (selected quote replies now registeredTerms home ordersWrite.read
    ⟨none, [post [levy, levy]]⟩).map Subtype.val = none
  have unfunded : ¬ CanPrepay (registeredTerms : OriginalReview.State → _) quote home ordersWrite.read
      (registeredTerms now) now.physical.raw.clock (post [levy, levy]) :=
    fun presented => tooMuch ((uniform_registered_budget_iff now _).mp presented.budget)
  have refused := (inspectOrder_none_iff (registeredTerms : OriginalReview.State → _) quote home ordersWrite.read
    (registeredTerms now) now.physical.raw.clock (post [levy, levy])).mpr unfunded
  unfold selected selectInAgenda selectOrder
  simp [refused]

theorem the_unfunded_bill_keeps_the_original_renewal :
    let actual := visit [levy, levy]
    actual.round = (ordinary quote replies now none).round ∧
      actual.next.physical.raw.clock = now.move.next.clock ∧
      actual.next.ledger.stack.balances = now.ledger.stack.balances := by
  dsimp only
  have unpaid := unaffordable_metered_work_cannot_be_prepaid
  rw [visit, registered_dispatch_is_the_exact_private_dispatch] at unpaid ⊢
  let due : Due Bool Bool Bool Unit Unit := ⟨none, [post [levy, levy]]⟩
  let actual := Prepayment.advance quote replies now registeredTerms home ordersWrite.read due
  change actual.paidWire = none at unpaid
  change actual.round = _ ∧ actual.next.physical.raw.clock = now.move.next.clock ∧
    actual.next.ledger.stack.balances = now.ledger.stack.balances
  have renewal := unpaid_order_is_the_exact_ordinary_write quote replies now registeredTerms home ordersWrite.read due unpaid
  change actual = _ at renewal
  rw [renewal]
  exact ⟨rfl, congrArg RawCurrent.clock
    (productiveRound_reads_selected_production now .renew .renewed now.programme now.recipe).2.1,
    (ordinary quote replies now none).rows⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Pricing.Original
