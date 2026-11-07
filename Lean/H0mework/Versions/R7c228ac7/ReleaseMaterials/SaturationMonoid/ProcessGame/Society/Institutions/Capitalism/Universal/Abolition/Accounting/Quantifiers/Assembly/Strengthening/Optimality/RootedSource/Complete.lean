import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Faces
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

structure RootExecutedAt (n : Nat) : Prop where
  originalCurrent : (initial n).actual.actual.account = Native.originalAccount
  actualSteps : ∀ index : Fin 6,
    (actualHistory n index.succ).inquiry.erase =
        (RootInquiryProcessNode.answered (actualHistory n index.castSucc).inquiry PUnit.unit).erase ∧
      (RootInquiryProcessNode.active (actualHistory n index.castSucc).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
        (RootInquiryProcessNode.active (actualHistory n index.succ).inquiry)
  rootAccount : (completed n).accountFace.rootRead = Native.afterAccount n
  rootPhysical : (completed n).snapshotFace.rootRead.actual = Programme.run input before (programme n)
  nativeComplete : Native.CompleteAt n
  noPending : ¬ Public.Inquiry.HasWork (completed n).frame (completed n).actual.actual
  generatedNext : (continuation n).inquiry.erase =
      (RootInquiryProcessNode.answered (completed n).inquiry PUnit.unit).erase ∧
    (RootInquiryProcessNode.active (completed n).inquiry).PreservesGeneratedLivingLawAt PUnit.unit
      (RootInquiryProcessNode.active (continuation n).inquiry)

theorem every_original_source_candidate_is_actually_root_executed (n : Nat) : RootExecutedAt n where
  originalCurrent := the_actual_initial_cut_is_the_original_account n
  actualSteps := every_step_of_the_generated_family_is_the_actual_root_resolution n
  rootAccount := the_completed_root_itself_reads_the_original_retired_native_account n
  rootPhysical := the_completed_root_itself_reads_the_original_physical_payment n
  nativeComplete := Native.every_source_candidate_is_a_real_complete_native_clearing n
  noPending := (the_completed_root_leaves_no_hidden_pending_item n).2.2
  generatedNext := the_retired_original_debt_does_not_seal_the_living_root n

theorem every_complete_original_programme_has_a_cheaper_actually_root_executed_candidate
    (code : Code) (cleared : RawCleared code) :
    RootExecutedAt (indexFor (Cost.value fullReading input before code - 1)) ∧
      Cost.value fullReading input before (improve code) < Cost.value fullReading input before code :=
  ⟨every_original_source_candidate_is_actually_root_executed _,
    (every_completed_original_programme_has_a_source_generated_strict_improvement code cleared).2⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
