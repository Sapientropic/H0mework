import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Run
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.FinancialFlow

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

private theorem step_appends_original_code
    (code : Distributed.Code Party Good Port Technology Instrument) (policy : code.Policy)
    (initial : RawCurrent Party Good Technology Instrument) (frame : code.Frame)
    (event : Distributed.Event Party Good Port Technology Instrument code.sites) :
    ∃ tail, (code.step policy initial frame event).word = frame.word ++ tail := by
  cases event with
  | adversary request => exact ⟨[request], rfl⟩
  | send sender recipient => exact ⟨code.sendCost sender recipient, rfl⟩
  | activate site => exact ⟨code.action policy site (frame.inbox site), rfl⟩
  | deliver address =>
      cases selected : frame.sent[address]? with
      | none => exact ⟨[], by simp only [Distributed.Code.step, selected, List.append_nil]⟩
      | some packet => exact ⟨code.deliveryCost packet.recipient, by simp only [Distributed.Code.step, selected]⟩

namespace Mechanism

variable (mechanism : Mechanism Party Good Port Technology Instrument) (nature : mechanism.Nature)

theorem the_sent_prefix_is_retained_in_the_whole_execution :
    ∃ tail, mechanism.word nature = (mechanism.sentFrame nature).word ++ tail := by
  have deliver : ∃ tail, (mechanism.deliveredFrame nature).word = (mechanism.sentFrame nature).word ++ tail := by
    unfold deliveredFrame
    split
    · exact step_appends_original_code _ _ _ _ _
    · exact ⟨[], (List.append_nil _).symm⟩
  have activate : ∃ tail, (mechanism.activeFrame nature).word = (mechanism.deliveredFrame nature).word ++ tail := by
    unfold activeFrame
    split
    · exact step_appends_original_code _ _ _ _ _
    · exact ⟨[], (List.append_nil _).symm⟩
  obtain ⟨a, ha⟩ := deliver
  obtain ⟨b, hb⟩ := activate
  exact ⟨a ++ b ++ mechanism.closing, by simp only [word, run, hb, ha, List.append_assoc]⟩

theorem the_trial_prefix_is_retained_in_the_whole_execution :
    ∃ tail, mechanism.word nature = mechanism.trialPrefix nature ++ tail := by
  have start : ∃ tail, (mechanism.initialFrame nature).word = mechanism.trialPrefix nature ++ tail :=
    ⟨[], by simp only [initialFrame, List.append_nil]⟩
  have send : ∃ tail, (mechanism.sentFrame nature).word = (mechanism.initialFrame nature).word ++ tail := by
    unfold sentFrame
    split
    · exact step_appends_original_code _ _ _ _ _
    · exact ⟨[], (List.append_nil _).symm⟩
  have deliver : ∃ tail, (mechanism.deliveredFrame nature).word = (mechanism.sentFrame nature).word ++ tail := by
    unfold deliveredFrame
    split
    · exact step_appends_original_code _ _ _ _ _
    · exact ⟨[], (List.append_nil _).symm⟩
  have activate : ∃ tail, (mechanism.activeFrame nature).word = (mechanism.deliveredFrame nature).word ++ tail := by
    unfold activeFrame
    split
    · exact step_appends_original_code _ _ _ _ _
    · exact ⟨[], (List.append_nil _).symm⟩
  obtain ⟨a, ha⟩ := start
  obtain ⟨b, hb⟩ := send
  obtain ⟨c, hc⟩ := deliver
  obtain ⟨d, hd⟩ := activate
  exact ⟨a ++ b ++ c ++ d ++ mechanism.closing, by
    simp only [word, run, hd, hc, hb, ha, List.append_assoc]⟩

theorem funding_is_the_literal_prefix_of_the_whole_trial :
    ∃ tail, mechanism.word nature = mechanism.funding ++ tail := by
  obtain ⟨tail, exactWord⟩ := mechanism.the_trial_prefix_is_retained_in_the_whole_execution nature
  exact ⟨mechanism.investmentWord ++ [nature] ++
      (if mechanism.invested then mechanism.probe else []) ++ tail, by
    simpa only [trialPrefix, beforeProbe, List.append_assoc] using exactWord⟩

theorem every_raw_nature_keeps_its_exact_original_item_after_the_commitment :
    ∃ item ∈ (mechanism.execution nature).items, item.request = nature ∧
      item.index = (mechanism.funding ++ mechanism.investmentWord).length ∧
      item.before = (mechanism.code.law.execute mechanism.code.initial 0
        (mechanism.funding ++ mechanism.investmentWord)).final := by
  obtain ⟨tail, exactWord⟩ := mechanism.the_trial_prefix_is_retained_in_the_whole_execution nature
  have shape : mechanism.word nature = (mechanism.funding ++ mechanism.investmentWord) ++
      nature :: ((if mechanism.invested then mechanism.probe else []) ++ tail) := by
    simpa only [trialPrefix, beforeProbe, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using exactWord
  unfold execution
  rw [shape, RawLaw.execute_append]
  simp only [RawLaw.execute, Nat.zero_add]
  exact ⟨_, List.mem_append_right _ List.mem_cons_self, rfl, rfl, rfl⟩

theorem a_real_financing_receipt_uses_the_same_trial_items
    (receipt : Financing.Disbursement mechanism.code.law mechanism.code.initial mechanism.funding mechanism.terms) :
    receipt.issue ∈ (mechanism.execution nature).items ∧ receipt.payout ∈ (mechanism.execution nature).items := by
  obtain ⟨tail, exactWord⟩ := mechanism.funding_is_the_literal_prefix_of_the_whole_trial nature
  unfold execution
  rw [exactWord, RawLaw.execute_append]
  exact ⟨List.mem_append_left _ receipt.issue_mem, List.mem_append_left _ receipt.payout_mem⟩

theorem actual_claims_keep_the_original_matrix_and_only_actual_changes
    (instrument : Instrument) (debtor creditor : Party) :
    (mechanism.after nature).claims instrument debtor creditor =
      mechanism.code.initial.claims instrument debtor creditor +
        mechanism.code.law.totalFinancialDelta (mechanism.execution nature).items instrument debtor creditor :=
  mechanism.code.law.execute_financial_balance mechanism.code.initial 0 _ instrument debtor creditor

theorem actual_investment_is_paid_before_the_unknown_nature
    (paid : mechanism.invested = true) :
    mechanism.funded = true ∧ mechanism.code.law.Valid mechanism.fundingAfter mechanism.investmentRequest ∧
      ∃ lot ∈ mechanism.investment, 0 < lot.2 := by
  have both : mechanism.funded = true ∧
      (mechanism.code.law.Valid mechanism.fundingAfter mechanism.investmentRequest ∧
        ∃ lot ∈ mechanism.investment, 0 < lot.2) := by
    simpa only [invested, Bool.and_eq_true, decide_eq_true_eq] using paid
  exact ⟨both.1, both.2.1, both.2.2⟩

theorem irreversible_investment_loss_is_the_original_borrowers_material
    (paid : mechanism.invested = true) (good : Good) :
    (mechanism.code.law.step mechanism.fundingAfter mechanism.investmentRequest).stock mechanism.terms.borrower good =
      mechanism.fundingAfter.stock mechanism.terms.borrower good - amount Good mechanism.investment good := by
  have accepted := (mechanism.actual_investment_is_paid_before_the_unknown_nature paid).2.1
  rw [RawLaw.step, if_pos accepted]
  simp [RawLaw.paidStep, RawLaw.debit, RawLaw.credit, investmentRequest, flowAt, locate, amount, Function.comp_def]

end Mechanism
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials
