import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native.Archive
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Needs

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
noncomputable section

theorem the_original_native_claim_is_retired_without_erasing_its_origin (n : Nat)
    (instrument : Unit) (debtor holder : Bool) :
    Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input 0 0 (afterAccount n).current instrument debtor holder = 0 := by
  obtain ⟨archive,terminal,identity,content,history⟩ := every_candidate_retires_the_same_original_slot_and_preserves_its_native_claim n
  simp [Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims,
    Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.slotClaims,terminal,
    Abolition.Root.Epoch.Finance.slotBalance]

structure CompleteAt (n : Nat) : Prop where
  rawCleared : RawCleared (programme n)
  sameOriginalNativeRun : Nonempty (finance.Run originalAccount.current (afterAccount n).current)
  actualArchive : ∃ archive : TerminalArchive (Abolition.Root.Epoch.Finance.vocabulary input 0 0),
    (afterAccount n).current.slots = [.terminal archive] ∧ archive.obligation = originalObligation ∧
    archive.obligation.content = .inr originalClaim ∧ originalAccount.current.history <+: (afterAccount n).current.history
  nativePrincipalZero : ∀ instrument debtor holder,
    Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ledgerClaims input 0 0 (afterAccount n).current instrument debtor holder = 0
  originalLivingAndMaintenance : Exit.Necessity.AllNeedsPaid law initial [false,true] (prefixWord ++ word n)
  literalFullCost : Cost.value fullReading input before (programme n) = 1 + epsilon n
  literalWholeHistoryCost : Cost.value fullReading input genesis (initialHistory ++ programme n) = 3 + epsilon n

theorem every_source_candidate_is_a_real_complete_native_clearing (n : Nat) : CompleteAt n where
  rawCleared := each_candidate_actually_clears_the_complete_original_debt n
  sameOriginalNativeRun := ⟨run n⟩
  actualArchive := every_candidate_retires_the_same_original_slot_and_preserves_its_native_claim n
  nativePrincipalZero := the_original_native_claim_is_retired_without_erasing_its_origin n
  originalLivingAndMaintenance := appending_a_real_future_does_not_erase_any_original_need_payment (word n)
  literalFullCost := (the_candidates_pay_the_same_actual_positive_maintenance_and_efficient_input n).2
  literalWholeHistoryCost := the_real_complete_history_has_cost_arbitrarily_close_to_its_unattained_floor n

theorem every_complete_programme_has_an_actually_native_cleared_cheaper_source_candidate
    (code : Code) (cleared : RawCleared code) :
    CompleteAt (indexFor (Cost.value fullReading input before code - 1)) ∧
      Cost.value fullReading input before (improve code) < Cost.value fullReading input before code :=
  ⟨every_source_candidate_is_a_real_complete_native_clearing _,
    (every_completed_original_programme_has_a_source_generated_strict_improvement code cleared).2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Countermodels.Nonattainment.Native
