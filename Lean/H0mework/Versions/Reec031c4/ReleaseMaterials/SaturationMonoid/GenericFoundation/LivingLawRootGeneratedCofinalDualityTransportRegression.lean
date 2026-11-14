import H0mework.Versions.Rb81a4438.Realization.Faces.DualityTransport
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.LivingLawRootGeneratedCofinalHistoryCochainCommonOccurrenceRegression
import H0mework.Versions.R453de275.Realization.Perfectification.Cofinal.LivingLawRootGeneratedCofinalRelationComplexKernel

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainDualityRegression

open CofinalHistorySettlement
open CofinalHistorySettlementFace
open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainCommonOccurrence.RootGeneratedCofinalHistoryCochainCommonStepAt
open CofinalHistoryCochainDuality
open CofinalHistoryCochainDuality.RootGeneratedCofinalHistoryCochainDualityStepAt
open SourceGeneratedDualEvaluation
open SourceNativeRootAuthorityRegression
open SourceNativeLedgerCompilerRegression

noncomputable section

universe u

/-! ## A nontrivial positive pairing -/

def genericRoot : RootedAccountedUnfolding Unit :=
  RootedAccountedUnfolding.zero ()

def integerPairing : ℤ →ₗ[ℤ] Module.Dual ℤ ℤ :=
  LinearMap.lsmul ℤ ℤ

def integerOccurrence (value : ℤ) : RootedAccountedUnfolding ℤ :=
  RootedAccountedUnfolding.zero value

theorem integerOccurrence_exact (value : ℤ) :
    (integerOccurrence value).root = value := by
  rfl

def integerFace : RootGeneratedDualEvaluationPairingAt
    genericRoot integerOccurrence integerOccurrence
    (RootedAccountedUnfolding.zero integerPairing) :=
  RootGeneratedDualEvaluationPairingAt.generate
    (left_exact := integerOccurrence_exact)
    (right_exact := integerOccurrence_exact)

theorem integerPairing_injective :
    Function.Injective integerPairing := by
  intro left right equality
  have evaluated := LinearMap.congr_fun equality (1 : ℤ)
  simpa [integerPairing, LinearMap.lsmul_apply] using evaluated

theorem integerPairing_surjective :
    Function.Surjective integerPairing := by
  intro functional
  refine ⟨functional 1, ?_⟩
  apply LinearMap.ext
  intro value
  rw [integerPairing, LinearMap.lsmul_apply]
  calc
    functional 1 • value = value • functional 1 := by
      simp [mul_comm]
    _ = functional (value • (1 : ℤ)) := (functional.map_smul value 1).symm
    _ = functional value := by simp

theorem integer_pairing_dualizable :
    ∃ leftEquiv : ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ,
      ∃ rightEquiv : ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ,
        settleDuality integerFace =
          .dualizable leftEquiv rightEquiv := by
  let leftEquiv : ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ :=
    LinearEquiv.ofBijective integerPairing
      ⟨integerPairing_injective, integerPairing_surjective⟩
  let rightEquiv : ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ := leftEquiv
  have left_settled :
      settleEvaluation integerPairing = .equivalence leftEquiv :=
    settleEvaluation_eq_equivalence_of_bijective integerPairing
      integerPairing_injective integerPairing_surjective
  have flip_eq : integerPairing.flip = integerPairing := by
    apply LinearMap.ext
    intro left
    apply LinearMap.ext
    intro right
    simp [integerPairing, LinearMap.lsmul_apply]
    ring
  have right_settled :
      settleEvaluation integerPairing.flip = .equivalence rightEquiv := by
    rw [flip_eq]
    simpa [rightEquiv] using left_settled
  refine ⟨leftEquiv, rightEquiv, ?_⟩
  apply settleDuality_of_both_equivalences integerFace leftEquiv rightEquiv
  · change settleEvaluation integerPairing = .equivalence leftEquiv
    exact left_settled
  · change settleEvaluation integerPairing.flip = .equivalence rightEquiv
    exact right_settled

/-! ## A zero pairing gives an explicit kernel residual -/

def zeroPairing : ℤ →ₗ[ℤ] Module.Dual ℤ ℤ := 0

def zeroFace : RootGeneratedDualEvaluationPairingAt
    genericRoot integerOccurrence integerOccurrence
    (RootedAccountedUnfolding.zero zeroPairing) :=
  RootGeneratedDualEvaluationPairingAt.generate
    (left_exact := integerOccurrence_exact)
    (right_exact := integerOccurrence_exact)

theorem zero_pairing_residual :
    ∃ coordinate : GeneratedEvaluationKernelCoordinate zeroFace.leftEvaluation,
      settleDuality zeroFace =
        .leftResidual (.kernelResidual coordinate) := by
  have zero_not_injective : ¬ Function.Injective zeroFace.leftEvaluation := by
    intro injective
    have equality :
        zeroFace.leftEvaluation (1 : ℤ) = zeroFace.leftEvaluation 0 := by
      change zeroPairing (1 : ℤ) = zeroPairing 0
      simp [zeroPairing]
    exact one_ne_zero (injective equality)
  obtain ⟨coordinate, settled⟩ :=
    settleEvaluation_eq_kernelResidual_of_not_injective
      zeroFace.leftEvaluation zero_not_injective
  exact ⟨coordinate,
    settleDuality_of_left_kernelResidual zeroFace coordinate settled⟩

/-! ## Source-installed common occurrence -/

abbrev N := CofinalHistoryCochainCommonOccurrenceRegression.N
abbrev V := CofinalHistoryCochainCommonOccurrenceRegression.V
abbrev BaseSource := CofinalHistoryCochainCommonOccurrenceRegression.BaseSource
abbrev sourceCommonLaw :=
  CofinalRelationGeneratedComplex.ofHistoryCommonLaw
    CofinalHistoryCochainCommonOccurrenceRegression.historyLaw

def sourcePairingAt : {current : V.Current} →
    (occurrence : BaseSource.source.toRootSource.actual.OccurrenceAt current) →
      RootedAccountedUnfolding
        ((sourceCommonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ]
          (sourceCommonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ)
  | _, _ => RootedAccountedUnfolding.zero 0

def sourceDualLaw :
    SourceNativeCofinalHistoryCochainDualityMaterialLaw BaseSource :=
  SourceNativeCofinalHistoryCochainDualityMaterialLaw.create
    sourceCommonLaw sourcePairingAt

def sourceAuthority : SourceNativeAuthoritySource N V where
  restructuringSource :=
    CofinalHistoryCochainCommonOccurrenceRegression.root.toAuthoritativeRoot.source.restructuringSource
  eventInventoryAdmission :=
    CofinalHistoryCochainCommonOccurrenceRegression.root.toAuthoritativeRoot.source.eventInventoryAdmission
  lawSurface :=
    CofinalHistoryCochainCommonOccurrenceRegression.root.toAuthoritativeRoot.source.lawSurface
  projectionLaw := sourceDualLaw.toProjectionLaw

def sourceLiving : SourceNativeLivingAuthoritySource N V where
  base := sourceAuthority
  terminalHandoff := sourceAuthority.emptyFaithfulTerminalHandoff
    (fun _current => by
      change IsEmpty PEmpty
      infer_instance)

def sourceRoot : SourceNativeLivingRootClosure N V where
  source := sourceLiving
  emitted := CofinalHistoryCochainCommonOccurrenceRegression.root.emitted
  compiler_commutes :=
    CofinalHistoryCochainCommonOccurrenceRegression.root.compiler_commutes

def sourceRecognition :
    SourceNativeCofinalHistoryCochainDualityRecognitionAt sourceRoot :=
  SourceNativeCofinalHistoryCochainDualityRecognitionAt.create
    sourceDualLaw
    (SourceNativeProjectionLaw.InstallationAt.refl
      sourceDualLaw.toProjectionLaw)

abbrev sourceVisit : SourceNativeTemporalVisitAt
    sourceRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite sourceRoot.toAuthoritativeRoot.toRoot.initialVisit

abbrev sourceStep : RootGeneratedCofinalHistoryCochainDualityStepAt
    sourceRecognition sourceVisit :=
  sourceRecognition.generateStepAt sourceVisit

theorem source_disposition_is_total :
    Nonempty (CommonDualityDisposition sourceStep) :=
  sourceStep.disposition_is_total

theorem source_pairing_root_is_common_root :
    sourceStep.commonStep.history.root = sourceStep.pairingFace.root :=
  sourceStep.common_root_eq_pairing_root

theorem source_step_preserves_root_ledger_next :
    HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit ∧
      HEq
        (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (sourceRecognition.installation.embed (.inr PUnit.unit))
          sourceStep.sourceOccurrence)
        (sourceRecognition.materialLaw.toProjectionLaw.outcomeAt
          (.inr PUnit.unit) sourceStep.sourceOccurrence) :=
  ⟨sourceStep.wholeLedgerWriteBack_eq_root,
    sourceStep.nextCurrent_eq_root,
    sourceStep.installedDuality_factorizes⟩

theorem source_pairing_action_is_root_installed :
    sourceStep.pairingFace.actualPairing =
        (sourceRecognition.materialLaw.toProjectionLaw.project
          (.inr PUnit.unit) sourceStep.sourceOccurrence PUnit.unit) ∧
      HEq
        (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (sourceRecognition.installation.embed (.inr PUnit.unit))
          sourceStep.sourceOccurrence)
        (sourceRecognition.materialLaw.toProjectionLaw.outcomeAt
          (.inr PUnit.unit) sourceStep.sourceOccurrence) ∧
      HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  sourceStep.sourcePairing_root_ledger_next

/-- The selected dual root now consumes the cochain complex and evaluator
computed from its installed raw relation history. -/
theorem source_relation_cochain_is_generated
    (value : (sourceStep.commonStep.cochainFace.termPresentation (-1)).cokernel) :
    sourceStep.commonStep.cochainFace.complex =
        CofinalRelationGeneratedComplex.ofHistory
          CofinalHistoryCochainCommonOccurrenceRegression.historyLaw
          sourceStep.sourceOccurrence ∧
      sourceStep.commonStep.faithful.actualGeneratorEvaluator =
        CofinalRelationGeneratedComplex.sourceEvaluator sourceStep.commonStep.history ∧
      FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
          (sourceStep.commonStep.cochainFace.termPresentation 1)
          (sourceStep.commonStep.cochainFace.differentialPresentedMap 0 1
            (sourceStep.commonStep.cochainFace.differentialPresentedMap (-1) 0 value)) = 0 ∧
      HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  ⟨rfl, rfl, sourceStep.commonStep.cochain_d_squared (-1) 0 1 value,
    sourceStep.wholeLedgerWriteBack_eq_root, sourceStep.nextCurrent_eq_root⟩

example : True := by
  fail_if_success exact sourceStep.callerPairing
  fail_if_success exact sourceStep.callerDuality
  fail_if_success exact sourceStep.callerEquivalence
  fail_if_success exact sourceStep.callerResidual
  exact True.intro

#print axioms integer_pairing_dualizable
#print axioms zero_pairing_residual
#print axioms source_disposition_is_total
#print axioms source_step_preserves_root_ledger_next
#print axioms source_pairing_action_is_root_installed
#print axioms source_relation_cochain_is_generated
#print axioms RootGeneratedDualEvaluationPairingAt.generate
#print axioms RootGeneratedDualEvaluationPairingAt.preserves_occurrences

end
end CofinalHistoryCochainDualityRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
