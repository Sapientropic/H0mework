import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Production

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Countermodels.Nonattainment
noncomputable section

theorem the_root_reader_selects_the_original_payment (n : Nat) :
    (productionEnd n).actual.proposal (productionEnd n).reader = .primitive repay := by
  have length : (history2 n).length - initialHistory.length = 2 := by
    simp only [history2,history1,List.length_append,List.length_cons,List.length_nil]
    omega
  have currentLength := (congrArg (fun past => past.length - initialHistory.length)
    (the_root_production_has_the_literal_original_physical_past n)).trans length
  exact (the_actual_proposal_is_read_from_the_same_source_code (productionEnd n) n
    (the_root_production_keeps_the_source_reader n)).trans
      (the_source_reader_selects_its_exact_word_index n 2 (productionEnd n).actual.readerCursor
        (productionEnd n).actual.actual.account currentLength)

def paymentBody (n : Nat) := (productionEnd n).raw (the_root_production_leaves_no_hidden_pending_item n).2.2
def completed (n : Nat) := (paymentBody n).native

theorem the_root_payment_has_its_original_source_start (n : Nat) :
    (paymentBody n).start = Primitive.start (history2 n) repay :=
  the_current_root_selects_the_identical_original_primitive (productionEnd n)
    (the_root_production_leaves_no_hidden_pending_item n).2.2 (history2 n) repay
    (the_root_production_has_the_literal_original_physical_past n) (the_root_reader_selects_the_original_payment n)

theorem the_original_payment_is_source_valid (n : Nat) :
    (Physical.Public.interpreter input).Valid (Primitive.state input 0 0 (history2 n)).raw repay := by
  rw [the_active_physical_interpreter_is_the_same_source_law,the_second_physical_history_is_the_original_actual_production]
  exact original_debt_is_payable_after_production n

theorem the_payment_body_is_the_actual_root_action (n : Nat) :
    (paymentBody n).inquiry.erase = (RootInquiryProcessNode.answered (productionEnd n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (productionEnd n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (paymentBody n).inquiry) :=
  Position.raw_is_the_actual_root_resolution _ (the_root_production_leaves_no_hidden_pending_item n).2.2

theorem the_root_payment_has_its_actual_financial_head (n : Nat) :
    Public.Inquiry.HasWork (paymentBody n).frame (paymentBody n).actual.actual ∧
      Public.Accounting.registration? input 0 0 0 0 [] (paymentBody n).start (paymentBody n).actual.actual = none := by
  apply the_original_nonissue_body_is_an_actual_native_action (paymentBody n) (history2 n) repay
    (the_root_payment_has_its_original_source_start n) rfl rfl rfl (the_original_payment_is_source_valid n)
  intro instrument debtor holder quantity impossible
  cases impossible

theorem the_original_payment_is_actually_consumed_by_the_root (n : Nat) :
    (completed n).inquiry.erase = (RootInquiryProcessNode.answered (paymentBody n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (paymentBody n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (completed n).inquiry) :=
  Position.native_is_the_actual_root_resolution _ (the_root_payment_has_its_actual_financial_head n).1
    (the_root_payment_has_its_actual_financial_head n).2

theorem the_completed_root_leaves_no_hidden_pending_item (n : Nat) :
    (completed n).actual.actual.bodyPaid = true ∧ (completed n).actual.actual.position = 1 ∧
      ¬ Public.Inquiry.HasWork (completed n).frame (completed n).actual.actual :=
  the_original_single_head_is_completely_consumed (paymentBody n) (history2 n) repay
    (the_root_payment_has_its_original_source_start n) rfl rfl rfl (the_original_payment_is_source_valid n)

theorem the_root_payment_has_the_literal_original_native_account (n : Nat) :
    (completed n).actual.actual.account =
      Primitive.accountAfter input 0 0 (history2 n) [repay] (productionEnd n).actual.actual.account :=
  (the_root_consumes_the_identical_original_native_item (paymentBody n) (history2 n) repay
    (the_root_payment_has_its_original_source_start n) rfl rfl rfl (the_original_payment_is_source_valid n)).trans
      (congrArg (Primitive.accountAfter input 0 0 (history2 n) [repay])
        (the_actual_raw_body_uses_the_same_account_and_initial_native_position (productionEnd n)
          (the_root_production_leaves_no_hidden_pending_item n).2.2).1)

theorem the_completed_root_has_the_literal_original_physical_past (n : Nat) :
    (completed n).actual.readerCursor.past = history3 n :=
  the_paid_body_retains_its_exact_actual_history (completed n) (history2 n) repay
    (the_root_payment_has_its_original_source_start n) (the_completed_root_leaves_no_hidden_pending_item n).1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
