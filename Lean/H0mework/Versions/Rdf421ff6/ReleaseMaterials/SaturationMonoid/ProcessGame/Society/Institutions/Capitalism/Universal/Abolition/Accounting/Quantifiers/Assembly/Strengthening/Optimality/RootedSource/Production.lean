import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Upgrade
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Reader

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Countermodels.Nonattainment
noncomputable section

theorem the_root_upgrade_keeps_the_source_reader (n : Nat) : (upgradeEnd n).reader = reader n := rfl

theorem the_root_reader_selects_the_original_production (n : Nat) :
    (upgradeEnd n).actual.proposal (upgradeEnd n).reader = .primitive produce := by
  change reader n (upgradeEnd n).actual.readerCursor (upgradeEnd n).actual.actual.account = _
  unfold reader
  rw [the_root_upgrade_has_the_literal_original_physical_past]
  simp [history1,programme,word]

def productionBody (n : Nat) := (upgradeEnd n).raw (the_root_upgrade_leaves_no_hidden_pending_item n).2.2
def productionEnd (n : Nat) := (productionBody n).native

theorem the_root_production_keeps_the_source_reader (n : Nat) : (productionEnd n).reader = reader n :=
  (the_native_source_keeps_the_same_reader (productionBody n)).trans
    ((the_raw_source_keeps_the_same_reader (upgradeEnd n) (the_root_upgrade_leaves_no_hidden_pending_item n).2.2).trans
      (the_root_upgrade_keeps_the_source_reader n))

theorem the_root_production_has_its_original_source_start (n : Nat) :
    (productionBody n).start = Primitive.start (history1 n) produce :=
  the_current_root_selects_the_identical_original_primitive (upgradeEnd n)
    (the_root_upgrade_leaves_no_hidden_pending_item n).2.2 (history1 n) produce
    (the_root_upgrade_has_the_literal_original_physical_past n) (the_root_reader_selects_the_original_production n)

theorem the_original_production_is_source_valid (n : Nat) :
    (Physical.Public.interpreter input).Valid (Primitive.state input 0 0 (history1 n)).raw produce := by
  rw [the_active_physical_interpreter_is_the_same_source_law,the_first_physical_history_is_the_original_actual_upgrade]
  exact source_production_is_affordable n

theorem the_production_body_is_the_actual_root_action (n : Nat) :
    (productionBody n).inquiry.erase = (RootInquiryProcessNode.answered (upgradeEnd n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (upgradeEnd n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (productionBody n).inquiry) :=
  Position.raw_is_the_actual_root_resolution _ (the_root_upgrade_leaves_no_hidden_pending_item n).2.2

theorem the_root_production_has_its_actual_financial_head (n : Nat) :
    Public.Inquiry.HasWork (productionBody n).frame (productionBody n).actual.actual ∧
      Public.Accounting.registration? input 0 0 0 0 [] (productionBody n).start (productionBody n).actual.actual = none := by
  apply the_original_nonissue_body_is_an_actual_native_action (productionBody n) (history1 n) produce
    (the_root_production_has_its_original_source_start n) rfl rfl rfl (the_original_production_is_source_valid n)
  intro instrument debtor holder quantity impossible
  cases impossible

theorem the_original_production_is_actually_consumed_by_the_root (n : Nat) :
    (productionEnd n).inquiry.erase = (RootInquiryProcessNode.answered (productionBody n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (productionBody n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (productionEnd n).inquiry) :=
  Position.native_is_the_actual_root_resolution _ (the_root_production_has_its_actual_financial_head n).1
    (the_root_production_has_its_actual_financial_head n).2

theorem the_root_production_leaves_no_hidden_pending_item (n : Nat) :
    (productionEnd n).actual.actual.bodyPaid = true ∧ (productionEnd n).actual.actual.position = 1 ∧
      ¬ Public.Inquiry.HasWork (productionEnd n).frame (productionEnd n).actual.actual :=
  the_original_single_head_is_completely_consumed (productionBody n) (history1 n) produce
    (the_root_production_has_its_original_source_start n) rfl rfl rfl (the_original_production_is_source_valid n)

theorem the_root_production_has_the_literal_original_native_account (n : Nat) :
    (productionEnd n).actual.actual.account =
      Primitive.accountAfter input 0 0 (history1 n) [produce] (upgradeEnd n).actual.actual.account :=
  the_root_consumes_the_identical_original_native_item (productionBody n) (history1 n) produce
    (the_root_production_has_its_original_source_start n) rfl rfl rfl (the_original_production_is_source_valid n)

theorem the_root_production_has_the_literal_original_physical_past (n : Nat) :
    (productionEnd n).actual.readerCursor.past = history2 n :=
  the_paid_body_retains_its_exact_actual_history (productionEnd n) (history1 n) produce
    (the_root_production_has_its_original_source_start n) (the_root_production_leaves_no_hidden_pending_item n).1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
