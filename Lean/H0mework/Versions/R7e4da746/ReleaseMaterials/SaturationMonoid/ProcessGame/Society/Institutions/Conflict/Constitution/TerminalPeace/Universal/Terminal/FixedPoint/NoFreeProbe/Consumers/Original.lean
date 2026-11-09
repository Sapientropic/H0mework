import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Dispatch
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalReview

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Original

open Capitalism.Universal.Source.Program
open Conflict.Consumers.Evolving (levy)
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

open private accountable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Consumers.OriginalReview

open private paidOrRenew from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Dispatch

noncomputable section

private abbrev current := OriginalReview.initial
private abbrev replies := OriginalReview.personalReplies true
private abbrev Packet := Wire Bool Bool Bool Unit Unit
private abbrev Instruction := Request Bool Bool Bool Unit Unit

private def tariff : Tariff Bool Bool Bool Unit Unit :=
  ⟨false, [(true, 1/6)], fun _ => [(true, 1/6)], fun _ => [(true, 1/6)],
    by decide +kernel, fun _ => by decide +kernel, fun _ => by decide +kernel,
    ⟨true, by decide +kernel⟩⟩

private def wireFor (request : Instruction) : Packet :=
  ⟨current.ledger.resident.erase, current.physical.raw.clock, true, true, [request], [(true, 1/2)]⟩

private def harmless : Instruction := ⟨true, [], false, [], .present⟩

private theorem renewal_word : current.move.word = Supply.Consumers.refillWord :=
  current.recipe.moveAt_word current.physical.raw current.reserved

private theorem originalPaid : AccountableReview replies current OriginalReview.bid :=
  accountable current rfl renewal_word

private theorem admits_one (request : Instruction) : Admitted tariff replies current (wireFor request) := by
  refine ⟨rfl, rfl, rfl, by change true ∈ [false, true]; decide, rfl, ?_, originalPaid.legal, originalPaid.fits, originalPaid.surplus⟩
  intro good
  change amount Bool [(true, 1/6), (true, 1/6), (true, 1/6)] good ≤ amount Bool [(true, 1/2)] good
  cases good <;> decide +kernel

private abbrev paid (request : Instruction) :=
  writePaidReview current (bill tariff (wireFor request)) (admits_one request).legal
    (admits_one request).fits (admits_one request).surplus (tariff.positive [request])

private theorem dispatch_one (request : Instruction) :
    advance tariff replies current ⟨none, [wireFor request]⟩ =
      .reviewed (wireFor request) (admits_one request) (paid request) := by
  have selected : select tariff replies current [wireFor request] = some ⟨wireFor request, admits_one request⟩ := by
    simp [select, checked, admits_one, (admits_one request).passes_public_screen]
  simp only [advance, paidOrRenew, selected, paid]

private theorem still_debits_half (request : Instruction) :
    (paid request).next.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) := by
  have half : (bill tariff (wireFor request)).fee true true = (1/2 : ℚ) := by
    change amount Bool [(true, 1/6), (true, 1/6), (true, 1/6)] true = _
    decide +kernel
  change (paid request).round.next.physical.raw.stock true true - current.move.next.stock true true = _
  simpa only [half] using (paid request).stock true true

private theorem harmless_has_no_foreign_debit :
    ¬ DemandsAggression (community := TerminalPeace.Original.community) current.programme.law
      current.physical.raw (bill tariff (wireFor harmless)) := by
  rintro ⟨item, listed, _, victim, good, _, _, net⟩
  have request : item = ⟨0, current.physical.raw, harmless⟩ := List.mem_singleton.mp listed
  subst item
  exact (lt_irrefl (flowAt ([] : Flow Bool Bool) victim good)) net

/-- The original levy is assessed only in the branch that has actually
burned its signer's three expenses. The original recovery rows survive. -/
theorem the_original_levy_posts_half_before_the_positive_reply :
    let step := advance tariff replies current ⟨none, [wireFor levy]⟩
    step.reply = .reviewed true ∧
      step.next.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) ∧
      step.next.ledger.stack.balances = current.ledger.stack.balances ∧
      ∃ item, step.round.visit.read.effect.execution.items[6]? = some item ∧
        item.request.signer = true ∧
        step.round.visit.read.programme.law.actualDebit item.before item.request =
          locate true [(true, 1/6), (true, 1/6), (true, 1/6)] := by
  change _ ∧ _ ∧ _ ∧ _
  rw [dispatch_one]
  have answer := (paid levy).answer_iff.mpr originalPaid.demand
  obtain ⟨item, atSix, signer, debit, _⟩ := (paid levy).original_expense
  rw [renewal_word] at atSix
  exact ⟨congrArg PublicReply.reviewed answer, still_debits_half levy, (paid levy).rows, item, atSix, signer, debit⟩

/-- The amount is payable even when the paid diagnosis finds no aggression. -/
theorem the_harmless_word_posts_half_before_the_negative_reply :
    let step := advance tariff replies current ⟨none, [wireFor harmless]⟩
    step.reply = .reviewed false ∧
      step.next.physical.raw.stock true true - current.move.next.stock true true = -(1/2 : ℚ) ∧
      step.next.ledger.stack.balances = current.ledger.stack.balances := by
  change _ ∧ _ ∧ _
  rw [dispatch_one]
  have answer : (paid harmless).answer = false :=
    Bool.eq_false_of_not_eq_true (fun yes => harmless_has_no_foreign_debit ((paid harmless).answer_iff.mp yes))
  exact ⟨congrArg PublicReply.reviewed answer, still_debits_half harmless, (paid harmless).rows⟩

private def free : Packet := { wireFor levy with tender := [] }
private def proxy : Packet := { wireFor levy with sender := false }
private def older : Packet := { wireFor levy with clock := current.physical.raw.clock - 1 }
private def fragment : Packet := { wireFor levy with tender := [(true, 1/4)] }

/-- A zero tender, proxy, stale clock and two quarter tenders all erase
from the due queue. The same original renewal runs at the same position. -/
theorem free_proxy_stale_and_split_traffic_erases :
    advance tariff replies current ⟨none, [free, proxy, older, fragment, fragment]⟩ = .renewed := by
  have rejectsFree : checked tariff replies current free = none :=
    (checked_eq_none_iff tariff replies current free).mpr
      (zero_tender_cannot_be_admitted tariff replies current free fun _ => rfl)
  have rejectsProxy : checked tariff replies current proxy = none :=
    mismatched_sender_is_rejected tariff replies current proxy (by decide)
  have rejectsOlder : checked tariff replies current older = none :=
    an_earlier_stamp_is_rejected tariff replies current older (sub_lt_self _ (by norm_num))
  have rejectsFragment : checked tariff replies current fragment = none :=
    a_tender_fragment_is_rejected tariff replies current fragment true (by decide +kernel)
  have unchanged : select tariff replies current [free, proxy, older, fragment, fragment] = none := by
    simp [select, rejectsFree, rejectsProxy, rejectsOlder, rejectsFragment]
  exact advance_depends_only_on_the_selected_admitted_wire tariff replies current
    ⟨none, [free, proxy, older, fragment, fragment]⟩ ⟨none, []⟩ rfl unchanged

theorem a_matching_wire_name_without_the_original_personal_reply_erases :
    let noConsent := OriginalReview.personalReplies false
    advance tariff noConsent current ⟨none, [wireFor levy]⟩ = .renewed := by
  intro noConsent
  have refused : checked tariff noConsent current (wireFor levy) = none :=
    an_absent_personal_reply_is_rejected tariff noConsent current (wireFor levy) rfl
  exact advance_depends_only_on_the_selected_admitted_wire tariff noConsent current
    ⟨none, [wireFor levy]⟩ ⟨none, []⟩ rfl (by simp [select, refused])

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.NoFreeProbe.Original
