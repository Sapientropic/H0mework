import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource.Account

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Countermodels.Nonattainment
noncomputable section

namespace Position
variable (current : Position input)

def accountFace : SourceNativeRootSemanticFaceAt current.full.root current.visit where
  projection := (Public.Inquiry.installation current.frame current.reader).embed .nativeAccount
  active := current.actual
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected current.frame .nativeAccount _ current.actual

def snapshotFace : SourceNativeRootSemanticFaceAt current.full.root current.visit where
  projection := (Public.Inquiry.installation current.frame current.reader).embed .snapshot
  active := current.actual
  classifier_eq := Public.Inquiry.the_unique_source_active_is_selected current.frame .snapshot _ current.actual

theorem the_actual_root_face_reads_the_identical_whole_native_account :
    current.accountFace.rootRead = current.actual.actual.account := rfl

theorem the_actual_root_face_reads_the_identical_physical_current :
    current.snapshotFace.rootRead.actual = physical current := by
  change Physical.Public.stateAt input 0 0 0 0 [] current.actual.snapshot.past = physical current
  unfold physical Public.Accounting.physical Public.Inquiry.ActualAt.snapshot
  split <;> rfl

end Position

theorem the_completed_root_itself_reads_the_original_retired_native_account (n : Nat) :
    (completed n).accountFace.rootRead = Native.afterAccount n :=
  (Position.the_actual_root_face_reads_the_identical_whole_native_account _).trans
    (the_completed_root_account_is_the_exact_original_native_clearing n)

theorem the_completed_root_itself_reads_the_original_physical_payment (n : Nat) :
    (completed n).snapshotFace.rootRead.actual = Programme.run input before (programme n) :=
  (Position.the_actual_root_face_reads_the_identical_physical_current _).trans
    (the_completed_root_physical_current_is_the_exact_original_programme n)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.RootedSource
