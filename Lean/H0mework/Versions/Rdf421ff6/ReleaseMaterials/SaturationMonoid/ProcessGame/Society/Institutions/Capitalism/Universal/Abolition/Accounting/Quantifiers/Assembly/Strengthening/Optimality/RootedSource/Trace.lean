import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

def actualHistory (n : Nat) : Fin 7 → Position input
  | ⟨0,_⟩ => initial n
  | ⟨1,_⟩ => upgradeBody n
  | ⟨2,_⟩ => upgradeEnd n
  | ⟨3,_⟩ => productionBody n
  | ⟨4,_⟩ => productionEnd n
  | ⟨5,_⟩ => paymentBody n
  | ⟨6,_⟩ => completed n

theorem every_step_of_the_generated_family_is_the_actual_root_resolution (n : Nat) (index : Fin 6) :
    (actualHistory n index.succ).inquiry.erase =
        (RootInquiryProcessNode.answered (actualHistory n index.castSucc).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (actualHistory n index.castSucc).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (actualHistory n index.succ).inquiry) := by
  fin_cases index
  · exact the_first_body_is_actually_resolved_by_the_root n
  · exact the_original_upgrade_is_actually_consumed_by_the_root n
  · exact the_production_body_is_the_actual_root_action n
  · exact the_original_production_is_actually_consumed_by_the_root n
  · exact the_payment_body_is_the_actual_root_action n
  · exact the_original_payment_is_actually_consumed_by_the_root n

def continuation (n : Nat) : Position input := (completed n).raw (the_completed_root_leaves_no_hidden_pending_item n).2.2

theorem the_retired_original_debt_does_not_seal_the_living_root (n : Nat) :
    (continuation n).inquiry.erase = (RootInquiryProcessNode.answered (completed n).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (completed n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (continuation n).inquiry) :=
  Position.raw_is_the_actual_root_resolution _ (the_completed_root_leaves_no_hidden_pending_item n).2.2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
