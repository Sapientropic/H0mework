import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime.Process

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation.Control

noncomputable section

local instance : Finite native.root.toAuthoritativeRoot.source.projectionLaw.Projection := original.projectionFinite

def originalAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt native.root visit
    (Source.sourceEntry input native visit) := original.authority

def runtime (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit) :=
  Action.Runtime.runtime input native visit C.familyClaim originalOrigin word originalAuthority

def actualAdmission (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit) :=
  Action.Installation.generated input native visit C.familyClaim originalOrigin word originalAuthority

def actualState (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit) : Responsibility.Family.State C.familyClaim :=
  ((runtime word).tickAt 2).answer

theorem every_actual_word_is_declared_by_the_same_original_root
    (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit) :
    DebtAdmissionActualActionResumptionAt (actualAdmission word) (runtime word) 0 :=
  ⟨Action.Runtime.the_compulsory_admission_is_consumed_by_the_named_canonical_runtime
    input native visit C.familyClaim originalOrigin word originalAuthority⟩

theorem actualState_eq (word : RawEvent Scenario.Party Scenario.Good Bool Nat Unit) :
    actualState word = Source.observed input native visit C.familyClaim word :=
  eq_of_heq (Action.Runtime.the_actual_observed_answer_is_the_same_physical_update
    input native visit C.familyClaim originalOrigin word originalAuthority)

theorem the_same_named_runtime_really_pays_all_original_material_and_result_cells :
    Responsibility.Family.State.isPaid C.familyClaim (actualState C.matrixWord) := by
  rw [actualState_eq]
  exact the_actual_root_repair_pays_the_entire_original_matrix

theorem the_same_named_runtime_retains_the_exact_unpaid_nominal_credit_bearer :
    (actualState Responsibility.Consumer.nominalMatrixWord).remaining (0,.material) = 8 := by
  rw [actualState_eq]
  exact nominal_credit_retains_the_same_original_unpaid_bearer

theorem the_same_named_runtime_retains_the_real_paid_prefix_after_refusal :
    (actualState Responsibility.Consumer.paidPrefixThenRejected).remaining (0,.material) = 7 := by
  rw [actualState_eq]
  exact refusing_after_a_real_prefix_keeps_its_payment_in_the_original_account.1

#print axioms every_actual_word_is_declared_by_the_same_original_root
#print axioms the_same_named_runtime_really_pays_all_original_material_and_result_cells
#print axioms the_same_named_runtime_retains_the_real_paid_prefix_after_refusal

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer
