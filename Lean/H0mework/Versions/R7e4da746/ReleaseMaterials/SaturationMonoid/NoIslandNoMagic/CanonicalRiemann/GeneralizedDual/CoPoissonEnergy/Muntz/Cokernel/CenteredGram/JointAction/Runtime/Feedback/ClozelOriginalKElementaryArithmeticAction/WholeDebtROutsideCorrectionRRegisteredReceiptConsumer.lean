import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionRConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtROutsideCorrectionRRegisteredReceiptConsumer
namespace S
export OriginalKOutsideCorrectionRSource
  (rInput final_admissions_source final_admission_source final_correction_source finalCorrectionTrace_heq final_correction_value rTrace_heq r_input_binding r_equation r_paid)
end S
namespace A
export OriginalKOutsideCorrectionRAction
  (rResult rPayments actualTarget r_whole_next source_ledger source_visit source_occurrence r_result_source r_state_source r_trace_source r_value_source r_equation r_relation r_inverse first_action whole_first canonical_next retained_source_payload target_source_payload)
end A
namespace C
export OriginalWholeDebtROutsideCorrectionRConsumer
  (actual_input_source actual_source_equation actual_input_feet actual_output_feet actual_complete_update actual_input_Gamma)
end C
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

private def Facts : Prop :=
  (type_of% (S.final_admissions_source observation nontrivial half depth ordinal)) ∧
  (type_of% (S.final_admission_source observation nontrivial half depth ordinal)) ∧
  (type_of% (S.final_correction_source observation nontrivial half depth ordinal)) ∧
  (type_of% (S.finalCorrectionTrace_heq observation nontrivial half depth ordinal)) ∧
  (type_of% (S.final_correction_value observation nontrivial half depth ordinal)) ∧
  (type_of% (S.rTrace_heq observation nontrivial half depth ordinal)) ∧
  (type_of% (S.r_input_binding observation nontrivial half depth ordinal)) ∧
  (type_of% (S.r_equation observation nontrivial half depth ordinal)) ∧
  (type_of% (S.r_paid observation nontrivial half depth ordinal)) ∧
  (type_of% (A.source_ledger observation nontrivial half depth ordinal)) ∧
  (type_of% (A.source_visit observation nontrivial half depth ordinal)) ∧
  (type_of% (A.source_occurrence observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_result_source observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_state_source observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_trace_source observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_value_source observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_equation observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_relation observation nontrivial half depth ordinal)) ∧
  (type_of% (A.r_inverse observation nontrivial half depth ordinal)) ∧
  (type_of% (A.first_action observation nontrivial half depth ordinal)) ∧
  (type_of% (A.whole_first observation nontrivial half depth ordinal)) ∧
  (type_of% (A.canonical_next observation nontrivial half depth ordinal)) ∧
  (type_of% (A.retained_source_payload observation nontrivial half depth ordinal)) ∧
  (type_of% (A.target_source_payload observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_input_source observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_source_equation observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_input_feet observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_output_feet observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_complete_update observation nontrivial half depth ordinal)) ∧
  (type_of% (C.actual_input_Gamma observation nontrivial half depth ordinal)) ∧
  (∀ count : Nat, type_of% (A.r_whole_next observation nontrivial half depth ordinal count)) ∧
  (∀ side : Fin 2, type_of% (OriginalWholeDebtRCorrectionActionSource.actual_native_endpoints c side))

private def Receipt : Sort _ :=
  Σ' inputData : type_of% (S.rInput observation nontrivial half depth ordinal),
    PProd (inputData = S.rInput observation nontrivial half depth ordinal) (
  Σ' resultData : type_of% (A.rResult observation nontrivial half depth ordinal),
    PProd (resultData = A.rResult observation nontrivial half depth ordinal) (
  Σ' payments : type_of% (A.rPayments observation nontrivial half depth ordinal),
    PProd (payments = A.rPayments observation nontrivial half depth ordinal) (
  Σ' target : type_of% (A.actualTarget observation nontrivial half depth ordinal),
    PProd (target = A.actualTarget observation nontrivial half depth ordinal) (
      Facts observation nontrivial half depth ordinal))))

noncomputable opaque actual_original_correction_R_whole_next : Receipt observation nontrivial half depth ordinal := by
  exact ⟨S.rInput observation nontrivial half depth ordinal, rfl,
    A.rResult observation nontrivial half depth ordinal, rfl,
    A.rPayments observation nontrivial half depth ordinal, rfl,
    A.actualTarget observation nontrivial half depth ordinal, rfl,
    S.final_admissions_source observation nontrivial half depth ordinal,
    S.final_admission_source observation nontrivial half depth ordinal,
    S.final_correction_source observation nontrivial half depth ordinal,
    S.finalCorrectionTrace_heq observation nontrivial half depth ordinal,
    S.final_correction_value observation nontrivial half depth ordinal,
    S.rTrace_heq observation nontrivial half depth ordinal,
    S.r_input_binding observation nontrivial half depth ordinal,
    S.r_equation observation nontrivial half depth ordinal,
    S.r_paid observation nontrivial half depth ordinal,
    A.source_ledger observation nontrivial half depth ordinal,
    A.source_visit observation nontrivial half depth ordinal,
    A.source_occurrence observation nontrivial half depth ordinal,
    A.r_result_source observation nontrivial half depth ordinal,
    A.r_state_source observation nontrivial half depth ordinal,
    A.r_trace_source observation nontrivial half depth ordinal,
    A.r_value_source observation nontrivial half depth ordinal,
    A.r_equation observation nontrivial half depth ordinal,
    A.r_relation observation nontrivial half depth ordinal,
    A.r_inverse observation nontrivial half depth ordinal,
    A.first_action observation nontrivial half depth ordinal,
    A.whole_first observation nontrivial half depth ordinal,
    A.canonical_next observation nontrivial half depth ordinal,
    A.retained_source_payload observation nontrivial half depth ordinal,
    A.target_source_payload observation nontrivial half depth ordinal,
    C.actual_input_source observation nontrivial half depth ordinal,
    C.actual_source_equation observation nontrivial half depth ordinal,
    C.actual_input_feet observation nontrivial half depth ordinal,
    C.actual_output_feet observation nontrivial half depth ordinal,
    C.actual_complete_update observation nontrivial half depth ordinal,
    C.actual_input_Gamma observation nontrivial half depth ordinal,
    A.r_whole_next observation nontrivial half depth ordinal,
    OriginalWholeDebtRCorrectionActionSource.actual_native_endpoints c⟩

end OriginalWholeDebtROutsideCorrectionRRegisteredReceiptConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtROutsideCorrectionRRegisteredReceiptConsumer"

