import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion.Admitted
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion

open ResponsibilityLifecycle Source.Program Countermodels.Nonattainment
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

/-- An explicit completion test for this original source, not a new
Society root admission. The endpoint is computed from the original account. -/
def SourceAdmitted (code : Code) : Prop := RawCleared code ∧
  ∃ requests : RawEvent Bool Bool Unit Nat Unit,
    code = requests.map Compile.RawInput.primitive ∧
    (∀ item ∈ Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.events input 0 0 initialHistory requests,
      (item.interpreter input 0 0).Valid (item.instruction input 0 0).before (item.instruction input 0 0).request) ∧
    Nonempty (Native.finance.Run Native.originalAccount.current
      (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input 0 0 initialHistory requests Native.originalAccount).current) ∧
    Exit.Necessity.AllNeedsPaid law initial [false,true] (prefixWord ++ requests) ∧
    ∃ archive : TerminalArchive (Abolition.Root.Epoch.Finance.vocabulary input 0 0),
      (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input 0 0 initialHistory requests Native.originalAccount).current.slots = [.terminal archive] ∧
      archive.obligation = Native.originalObligation ∧ archive.obligation.content = .inr Native.originalClaim ∧
      Native.originalAccount.current.history <+:
        (Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive.accountAfter input 0 0 initialHistory requests Native.originalAccount).current.history

theorem each_actual_family_member_passes_the_complete_original_source_test (n : Nat) :
    SourceAdmitted (programme n) := by
  have complete := Native.every_source_candidate_is_a_real_complete_native_clearing n
  exact ⟨complete.rawCleared,word n,rfl,(Native.every_family_inventory_is_its_original_actual_requests n).2,
    complete.sameOriginalNativeRun,complete.originalLivingAndMaintenance,complete.actualArchive⟩

theorem any_completed_raw_candidate_has_a_cheaper_fully_accounted_source_completion
    (code : Code) (cleared : RawCleared code) :
    SourceAdmitted (improve code) ∧
      Cost.value fullReading input genesis (initialHistory ++ improve code) <
        Cost.value fullReading input genesis (initialHistory ++ code) := by
  have better := the_strict_improvement_keeps_the_complete_original_historical_cost RawCleared
    (fun _ paid => paid) each_candidate_actually_clears_the_complete_original_debt code cleared
  exact ⟨each_actual_family_member_passes_the_complete_original_source_test _,better.2⟩

theorem the_explicit_fully_accounted_source_test_has_no_complete_cost_minimizer :
    ¬ ∃ code : Code, SourceAdmitted code ∧ ∀ rival : Code, SourceAdmitted rival →
      Cost.value fullReading input genesis (initialHistory ++ code) ≤
        Cost.value fullReading input genesis (initialHistory ++ rival) :=
  no_admitted_full_history_attains_the_complete_social_cost_infimum SourceAdmitted
    (fun _ complete => complete.1) each_actual_family_member_passes_the_complete_original_source_test

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Completion
