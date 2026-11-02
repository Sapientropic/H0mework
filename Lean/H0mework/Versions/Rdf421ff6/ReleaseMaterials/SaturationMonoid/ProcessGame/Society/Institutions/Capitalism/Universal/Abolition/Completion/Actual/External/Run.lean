import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External.Ingress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Bound.Actual
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open M14SourceGeneratedContributionMergeActionSource
open SourceNativeInquiryRuntime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (sourceStart : Nat) (datum : Macro.Ingress.Datum input 1 sourceStart)
  (prefixLimit renewalLimit : Nat)
  (reader : Macro.Raw.Reader input 1 (Macro.Ingress.cut input 1 sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "cut" => Macro.Ingress.cut input 1 sourceStart
local notation "externalFrame" => Macro.Ingress.frame input 1 sourceStart
local notation "current" => Macro.Runtime.actualFrame (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader
local notation "actualRun" => Macro.Runtime.run (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader

theorem the_first_actual_macro_account_is_the_complete_external_account :
    (current 0).nativeAccount =
      Epoch.Finance.Legacy.generated input 1 cut ((externalFrame).cursor input).account := by
  change (Macro.Ingress.nextVisit (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader).current.account = _
  exact Macro.Ingress.first_inquiry_keeps_the_same_drained_account (review := review)
    input 1 sourceStart datum prefixLimit renewalLimit reader

/-- This is an actual native continuation from the original external
financial state into the original mixed-law Engine history. It neither
reconstructs a current nor signs an inherited live slot as paid. -/
def nativeRun (tick : Nat) : (Epoch.Finance.process input 1 cut).Run
    (Epoch.Finance.Legacy.generated input 1 cut ((externalFrame).cursor input).account).current
    (current tick).nativeAccount.current := by
  rw [← the_first_actual_macro_account_is_the_complete_external_account (review := review)
    input sourceStart datum prefixLimit renewalLimit reader]
  change (Epoch.Finance.process input 1 cut).Run (current 0).account.current (current tick).account.current
  have same := Macro.Runtime.actual_internal_fold_is_the_same_registered_history (review := review)
    input 1 sourceStart datum prefixLimit renewalLimit reader 0 tick
  simp only [Nat.zero_add] at same
  rw [← same]
  exact Macro.Runtime.ActivatedFrame.afterNative (current 0) tick

theorem every_original_external_claim_and_history_entry_survives (tick : Nat) :
    (((externalFrame).cursor input).account.current.slots.map (Epoch.Finance.Legacy.slot input 1 cut)).map
        (Epoch.Finance.slotClaim input 1 cut) <+:
      (current tick).nativeAccount.current.slots.map (Epoch.Finance.slotClaim input 1 cut) ∧
    ((externalFrame).cursor input).account.current.history.map (Epoch.Finance.Legacy.lifecycle input 1 cut) <+:
      (current tick).nativeAccount.current.history := by
  have claims := Epoch.Finance.run_retains_all_claims input 1 cut
    (nativeRun (review := review) input sourceStart datum prefixLimit renewalLimit reader tick)
  rw [(Epoch.Finance.Legacy.every_slot_and_history_entry_is_retained input 1 cut
    ((externalFrame).cursor input).account).1] at claims
  exact ⟨claims, Epoch.Finance.Legacy.old_history_remains_a_prefix_of_every_native_extension input 1 cut
    ((externalFrame).cursor input).account (nativeRun (review := review) input sourceStart datum prefixLimit renewalLimit reader tick)⟩

theorem the_original_engine_consumes_the_external_source_action :
    RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      (Macro.Runtime.firstEvent (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader).rawReadout.resolution
      (Macro.Ingress.generated (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader) :=
  Macro.Runtime.first_ask_consumes_the_source_action (review := review)
    input 1 sourceStart datum prefixLimit renewalLimit reader

theorem every_actual_external_continuation_has_the_original_whole_ledger_next (tick : Nat) :
    (actualRun (tick + 1)).engine.node = .active (current tick).presentation ∧
    (actualRun (tick + 1)).engine.node.PreservesGeneratedLivingLawAt
      ((actualRun (tick + 1)).engine.registeredInquiryActivation
        (Macro.Runtime.event (review := review) input 1 sourceStart datum prefixLimit renewalLimit reader (actualRun (tick + 1))).input).query
      (actualRun (tick + 2)).engine.node ∧
    (actualRun (tick + 2)).engine.node = .active (current (tick + 1)).presentation :=
  ⟨Macro.Runtime.run_is_the_original_registered_history (review := review)
      input 1 sourceStart datum prefixLimit renewalLimit reader tick,
    Macro.Runtime.each_actual_attempt_has_the_original_complete_next (review := review)
      input 1 sourceStart datum prefixLimit renewalLimit reader (actualRun (tick + 1)),
    Macro.Runtime.run_is_the_original_registered_history (review := review)
      input 1 sourceStart datum prefixLimit renewalLimit reader (tick + 1)⟩

#print axioms the_first_actual_macro_account_is_the_complete_external_account
#print axioms nativeRun
#print axioms every_original_external_claim_and_history_entry_survives
#print axioms the_original_engine_consumes_the_external_source_action
#print axioms every_actual_external_continuation_has_the_original_whole_ledger_next

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.External
