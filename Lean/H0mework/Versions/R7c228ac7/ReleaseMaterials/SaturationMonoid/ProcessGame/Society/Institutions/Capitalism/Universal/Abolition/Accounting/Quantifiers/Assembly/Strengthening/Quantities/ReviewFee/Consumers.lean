import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Envelope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Registration
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifeTrace
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Consumers.Review

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Consumers

open Source.Program Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Evolving.Epoch
open Evolving.Epoch.Consumers
  (current original_complete no_review_is_preinstalled the_actual_public_source_admits_the_new_code
    reviewCode reviewFee the_original_root_really_installs_its_new_finite_programme)
open Innovation.Contribution.Pricing.Consumers.Actual (settledCut base base_raw_is_the_real_settled_cut)

noncomputable section

def amountCode (amount : ℚ) : ReviewSource.Control.Code Bool Bool Bool Unit Unit :=
  { reviewCode with fee := { reviewFee with operation := .use false [(false, amount)] .external } }

def atFee (amount : ℚ) := registration current (amountCode amount)

private theorem original_registration (amount : ℚ) :
    (atFee amount).raw = current.raw ∧ ¬ Pending (atFee amount) ∧
      (atFee amount).control.review =
        some (ReviewCursor.initial (amountCode amount) current.native.prefixLimit current.native.renewalLimit) :=
  registration_preserves_the_actual_source_and_installs_the_original_fee current (amountCode amount)
    original_complete no_review_is_preinstalled the_actual_public_source_admits_the_new_code

private theorem original_stock (amount : ℚ) : (atFee amount).raw.stock false false = 117 := by
  have before : current.raw = settledCut :=
    the_original_root_really_installs_its_new_finite_programme.2.symm.trans base_raw_is_the_real_settled_cut
  rw [(original_registration amount).1, before]
  rfl

private theorem original_currency_has_no_necessity_debit (amount : ℚ) :
    necessities (atFee amount) false false = 0 := by
  have same : (atFee amount).native.input = current.native.input :=
    Execution.next_input current (some (.review (amountCode amount)))
  unfold necessities
  rw [same]
  change max 0 (Source.Program.amount Bool [(true, 1)] false + Source.Program.amount Bool [] false) = 0
  decide +kernel

private theorem original_fee (amount : ℚ) (positive : 0 < amount) :
    ∃ fee : SelectedAt (atFee amount), selected? (atFee amount) = some fee ∧
      fee.fee.scope.amount = amount ∧ fee.fee.scope.payer = false ∧ fee.fee.scope.good = false := by
  let scope : Abolition.Review.FeeScope (amountCode amount).fee :=
    ⟨false, false, amount, rfl, positive⟩
  exact a_registered_positive_fee_is_selected_at_its_own_review_cut (atFee amount) (amountCode amount)
    current.native.prefixLimit current.native.renewalLimit scope (original_registration amount).2.2

theorem every_positive_fee_on_the_original_registration_has_its_exact_budget_and_write
    (amount : ℚ) (positive : 0 < amount) :
    ∃ fee : SelectedAt (atFee amount), selected? (atFee amount) = some fee ∧
      fee.fee.scope.amount = amount ∧
      (Fits (atFee amount) fee ↔ amount ≤ 117) ∧
      (amount ≤ 117 → PaidAt (atFee amount) fee) ∧
      (117 < amount →
        (Execution.next (atFee amount) none).raw = (atFee amount).raw ∧
        (Execution.next (atFee amount) none).control.review =
          some { fee.cursor with feePaid := false, halted := true } ∧
        Recorded (atFee amount) (script (atFee amount))) := by
  obtain ⟨fee, selected, value, payer, good⟩ := original_fee amount positive
  have ready := (original_registration amount).2.1
  refine ⟨fee, selected, value, ?_, ?_, ?_⟩
  · unfold Fits ceiling
    rw [value, payer, good, original_stock, original_currency_has_no_necessity_debit, sub_zero]
  · intro fits
    apply the_chosen_fee_debits_its_original_payer_and_activates_the_actual_review _ _ ready
    rw [value, payer, good, original_stock]
    exact fits
  · intro exceeds
    apply a_fee_shortfall_preserves_the_original_debts_and_reopens_recourse _ _ ready
    rw [value, payer, good, original_stock]
    exact exceeds

def originalFees : Set ℚ :=
  { amount | Nonempty (SafeAt (atFee amount)) }

theorem the_original_review_fee_domain_is_the_exact_positive_interval :
    originalFees = Set.Ioc 0 117 := by
  ext amount
  constructor
  · rintro ⟨safe⟩
    have cursor : safe.fee.cursor = ReviewCursor.initial (amountCode amount)
        current.native.prefixLimit current.native.renewalLimit :=
      Option.some.inj (safe.fee.original.symm.trans (original_registration amount).2.2)
    have original := safe.fee.originalOperation
    rw [cursor] at original
    change safe.fee.fee.request.operation = .use false [(false, amount)] .external at original
    have same := safe.fee.fee.scope.operation.symm.trans original
    injection same with payer goods
    have exactGood : safe.fee.fee.scope.good = false := congrArg Prod.fst (List.cons.inj goods).1
    have exactAmount : safe.fee.fee.scope.amount = amount := congrArg Prod.snd (List.cons.inj goods).1
    have positive : 0 < amount := exactAmount ▸ safe.fee.fee.scope.positive
    have protects := safe.protects
    unfold Fits ceiling at protects
    rw [exactAmount, payer, exactGood, original_stock, original_currency_has_no_necessity_debit, sub_zero] at protects
    exact ⟨positive, protects⟩
  · rintro ⟨positive, within⟩
    obtain ⟨fee, selected, _, fits, paid, _⟩ :=
      every_positive_fee_on_the_original_registration_has_its_exact_budget_and_write amount positive
    exact ⟨⟨fee, selected, (original_registration amount).2.1, paid within, fits.mpr within⟩⟩

theorem the_original_review_has_an_attained_ceiling_and_an_unattained_zero_floor :
    IsGreatest originalFees 117 ∧ IsGLB originalFees 0 ∧ (0 : ℚ) ∉ originalFees ∧
      ∀ tolerance : ℚ, 0 < tolerance → ∃ amount ∈ originalFees, amount < tolerance := by
  rw [the_original_review_fee_domain_is_the_exact_positive_interval]
  have near : ∀ tolerance : ℚ, 0 < tolerance → ∃ amount ∈ Set.Ioc (0 : ℚ) 117, amount < tolerance := by
    intro tolerance positive
    refine ⟨min 117 (tolerance / 2), ⟨lt_min (by norm_num) (by linarith), min_le_left _ _⟩, ?_⟩
    exact (min_le_right _ _).trans_lt (by linarith)
  refine ⟨⟨⟨by norm_num, le_rfl⟩, fun _ member => member.2⟩, ⟨fun _ member => member.1.le, ?_⟩,
    fun member => (lt_irrefl 0) member.1, near⟩
  intro bound lower
  by_contra! positive
  obtain ⟨value, member, closer⟩ := near bound positive
  exact (not_lt_of_ge (lower member)) closer

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.ReviewFee.Consumers
