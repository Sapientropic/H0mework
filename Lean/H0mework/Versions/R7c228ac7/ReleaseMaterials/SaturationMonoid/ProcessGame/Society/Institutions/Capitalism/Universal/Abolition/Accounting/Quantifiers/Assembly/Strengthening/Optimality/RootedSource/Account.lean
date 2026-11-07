import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Payment

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
open Countermodels.Nonattainment
noncomputable section

theorem the_completed_root_account_is_the_exact_original_native_clearing (n : Nat) :
    (completed n).actual.actual.account = Native.afterAccount n :=
  (the_root_payment_has_the_literal_original_native_account n).trans
    ((congrArg (Primitive.accountAfter input 0 0 (history2 n) [repay])
      (the_root_production_has_the_literal_original_native_account n)).trans
      (congrArg (fun account => Primitive.accountAfter input 0 0 (history2 n) [repay]
        (Primitive.accountAfter input 0 0 (history1 n) [produce] account))
        (the_root_upgrade_has_the_literal_original_native_account n)))

def physical (current : Position input) := Public.Accounting.physical input 0 0 0 0 [] current.start current.actual.actual

theorem the_completed_root_physical_current_is_the_exact_original_programme (n : Nat) :
    physical (completed n) = Programme.run input before (programme n) := by
  unfold physical Public.Accounting.physical
  rw [(the_completed_root_leaves_no_hidden_pending_item n).1]
  change Physical.Public.stateAt input 0 0 0 0 [] (Physical.next (completed n).start).past = _
  have past : (Physical.next (completed n).start).past = history3 n := by
    have source := the_completed_root_has_the_literal_original_physical_past n
    simpa only [Public.Inquiry.ActualAt.readerCursor,Public.Inquiry.ActualAt.snapshot,
      (the_completed_root_leaves_no_hidden_pending_item n).1,if_true,Physical.receive,
      Physical.Prefix.past_readback,List.nil_append] using source
  rw [past]
  exact (the_final_physical_history_is_the_original_actual_payment n).trans
    (each_candidate_is_its_actual_original_programme_run n).symm

theorem the_completed_root_has_retired_the_original_slot_without_erasing_its_claim (n : Nat) :
    ∃ archive : TerminalArchive (Epoch.Finance.vocabulary input 0 0),
      (completed n).actual.actual.account.current.slots = [.terminal archive] ∧
      archive.obligation = Native.originalObligation ∧ archive.obligation.content = .inr Native.originalClaim ∧
      Native.originalAccount.current.history <+: (completed n).actual.actual.account.current.history := by
  rw [the_completed_root_account_is_the_exact_original_native_clearing]
  exact Native.every_candidate_retires_the_same_original_slot_and_preserves_its_native_claim n

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
