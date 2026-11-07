import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Physical
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.NativeStep

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Countermodels.Nonattainment
noncomputable section

def upgradeBody (n : Nat) := (initial n).native
def upgradeEnd (n : Nat) := (upgradeBody n).native

theorem the_original_upgrade_is_source_valid (n : Nat) :
    (Physical.Public.interpreter input).Valid (Primitive.state input 0 0 initialHistory).raw (upgrade n) := by
  rw [the_active_physical_interpreter_is_the_same_source_law]
  exact source_revision_is_available _ n

theorem the_root_upgrade_has_its_actual_financial_head (n : Nat) :
    Public.Inquiry.HasWork (upgradeBody n).frame (upgradeBody n).actual.actual ∧
      Public.Accounting.registration? input 0 0 0 0 [] (upgradeBody n).start (upgradeBody n).actual.actual = none := by
  apply the_original_nonissue_body_is_an_actual_native_action (upgradeBody n) initialHistory (upgrade n)
    rfl rfl rfl rfl (the_original_upgrade_is_source_valid n)
  intro instrument debtor holder quantity impossible
  cases impossible

theorem the_original_upgrade_is_actually_consumed_by_the_root (n : Nat) :
    (upgradeEnd n).inquiry.erase = (RootInquiryProcessNode.answered (upgradeBody n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (upgradeBody n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (upgradeEnd n).inquiry) :=
  Position.native_is_the_actual_root_resolution _ (the_root_upgrade_has_its_actual_financial_head n).1
    (the_root_upgrade_has_its_actual_financial_head n).2

theorem the_root_upgrade_leaves_no_hidden_pending_item (n : Nat) :
    (upgradeEnd n).actual.actual.bodyPaid = true ∧ (upgradeEnd n).actual.actual.position = 1 ∧
      ¬ Public.Inquiry.HasWork (upgradeEnd n).frame (upgradeEnd n).actual.actual :=
  the_original_single_head_is_completely_consumed (upgradeBody n) initialHistory (upgrade n)
    rfl rfl rfl rfl (the_original_upgrade_is_source_valid n)

theorem the_root_upgrade_has_the_literal_original_native_account (n : Nat) :
    (upgradeEnd n).actual.actual.account =
      Primitive.accountAfter input 0 0 initialHistory [upgrade n] Native.originalAccount :=
  the_root_consumes_the_identical_original_native_item (upgradeBody n) initialHistory (upgrade n)
    rfl rfl rfl rfl (the_original_upgrade_is_source_valid n)

theorem the_root_upgrade_has_the_literal_original_physical_past (n : Nat) :
    (upgradeEnd n).actual.readerCursor.past = history1 n :=
  the_paid_body_retains_its_exact_actual_history (upgradeEnd n) initialHistory (upgrade n)
    rfl (the_root_upgrade_leaves_no_hidden_pending_item n).1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
