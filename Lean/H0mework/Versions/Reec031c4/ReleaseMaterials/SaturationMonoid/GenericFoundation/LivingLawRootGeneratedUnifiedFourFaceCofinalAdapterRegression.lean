import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedUnifiedFourFaceCofinalAdapter
import H0mework.Versions.Reec031c4.ReleaseMaterials.SaturationMonoid.GenericFoundation.LivingLawRootGeneratedCofinalDualityTransportRegression

/-!
# Root/ledger consumer for the unified four-face producer

The existing cofinal-duality source supplies the exact emitted occurrence.
The unified package is installed on that occurrence and its readback is
checked together with the parent's whole-ledger and generated-next equations.
This prevents a source-neutral generic package from becoming an unrooted
second authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UnifiedFourFaceCofinalAdapterRegression

open CofinalHistoryCochainDuality
open CofinalHistoryCochainDuality.RootGeneratedCofinalHistoryCochainDualityStepAt
open CofinalHistoryCochainDualityRegression
open UnifiedFourFace
open CofinalAllPrimeTopology
open SourceGeneratedPrimePowerCompletion

noncomputable section

abbrev unifiedInput := sourceStep.unifiedInput
abbrev unifiedGenerated := sourceStep.unifiedGenerated

theorem package_total :
    Nonempty (UnifiedFourFace.Generated (sourceStep.unifiedInput)) :=
  sourceStep.unifiedGenerated_total

theorem pairing_readback :
    (sourceStep.unifiedGenerated).embedding.comp
        (sourceStep.unifiedGenerated).canonical =
      UnifiedFourFace.RootDualEvaluation sourceStep.unifiedInput :=
  sourceStep.unifiedGenerated_readback

theorem canonical_perfect_pair_readback :
    (sourceStep.unifiedGenerated).canonicalPerfectPair.inclusion.comp
        (sourceStep.unifiedGenerated).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (UnifiedFourFace.RootDualEvaluation sourceStep.unifiedInput) :=
  sourceStep.unifiedGenerated_canonical_perfect_pair_readback

theorem exact_occurrence_reused :
    sourceStep.unifiedInput.occurrence = sourceStep.commonStep.history.root :=
  sourceStep.unifiedInput_occurrence

theorem actual_relation_cochain_reused :
    (sourceStep.unifiedGenerated.relationFace.root).1 =
        sourceStep.sourceOccurrence ∧
      HEq (sourceStep.unifiedGenerated.relationFace.root).2
        sourceStep.commonStep.faithful ∧
      (sourceStep.unifiedGenerated.cochainFace.root).1 =
        sourceStep.sourceOccurrence ∧
      HEq (sourceStep.unifiedGenerated.cochainFace.root).2
        sourceStep.commonStep.cochainFace :=
  ⟨sourceStep.unifiedGenerated_relation_source,
    sourceStep.unifiedGenerated_relation_actual,
    sourceStep.unifiedGenerated_cochain_source,
    sourceStep.unifiedGenerated_cochain_actual⟩

theorem actual_algebra_combinatorial_reused :
    HEq (sourceStep.unifiedGenerated.algebraFace.root).2
        sourceStep.pairingFace.actualPairing ∧
      HEq (sourceStep.unifiedGenerated.combinatorialFace.root).2
        sourceStep.commonStep.history :=
  ⟨sourceStep.unifiedGenerated_algebra_actual,
    sourceStep.unifiedGenerated_combinatorial_actual⟩

theorem generated_combinatorial_history_mono
    {first later : Nat} (order : first ≤ later) :
    ∀ event,
      event ∈ (sourceStep.unifiedGenerated.combinatorialFace.root).2.observedEvents first →
      event ∈ (sourceStep.unifiedGenerated.combinatorialFace.root).2.observedEvents later :=
  sourceStep.unifiedGenerated_combinatorial_history_mono order

theorem generated_topology_restriction_ledger_next
    (prime : Nat.Primes) (stage : Nat)
    (value :
      (sourceDualLaw.commonLaw.historyAt
        (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    (restriction (L :=
      (sourceDualLaw.commonLaw.historyAt
        (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier)
      prime stage).hom
        ((sourceStep.unifiedGenerated.topologicalFace.root).2.observation value prime) =
      stageProjection (L :=
        (sourceDualLaw.commonLaw.historyAt
          (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier)
        prime stage value ∧
      HEq
        (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (sourceRecognition.commonRecognition.installation.embed PUnit.unit)
          sourceStep.sourceOccurrence)
        (sourceDualLaw.commonLaw.toProjectionLaw.outcomeAt
          PUnit.unit sourceStep.sourceOccurrence) ∧
      HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  sourceStep.unifiedGenerated_topological_restriction_ledger_next prime stage value

theorem generated_topology_kernel_ledger_next
    (value :
      (sourceDualLaw.commonLaw.historyAt
        (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    (value ∈ LinearMap.ker
        (sourceStep.unifiedGenerated.topologicalFace.root).2.observation ↔
      ∀ prime : Nat.Primes, ∀ stage : Nat,
        ∃ divided :
          (sourceDualLaw.commonLaw.historyAt
            (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier,
          (prime.1 : ℤ) ^ (stage + 1) • divided = value) ∧
      HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  sourceStep.unifiedGenerated_topological_kernel_ledger_next value

theorem generated_topology_inseparable_zero_iff_kernel
    (value :
      (sourceDualLaw.commonLaw.historyAt
        (sourceStep.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    @Inseparable _
        (sourceStep.unifiedGenerated.topologicalFace.root).2.uniformity.toTopologicalSpace
        value 0 ↔
      value ∈ LinearMap.ker
        (sourceStep.unifiedGenerated.topologicalFace.root).2.observation :=
  sourceStep.unifiedGenerated_topological_inseparable_zero_iff_kernel value

theorem generated_logical_equation
    (first middle last : ℤ)
    (value :
      ((sourceDualLaw.commonLaw.cochainAt
        (sourceStep.unifiedGenerated.logicalFace.root).1).termPresentation first).cokernel) :
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        ((sourceDualLaw.commonLaw.cochainAt
          (sourceStep.unifiedGenerated.logicalFace.root).1).termPresentation last)
        ((sourceDualLaw.commonLaw.cochainAt
          (sourceStep.unifiedGenerated.logicalFace.root).1).differentialPresentedMap middle last
          ((sourceDualLaw.commonLaw.cochainAt
            (sourceStep.unifiedGenerated.logicalFace.root).1).differentialPresentedMap
              first middle value)) = 0 :=
  sourceStep.unifiedGenerated_logical_d_squared first middle last value

theorem generated_cochain_ledger_next
    (first middle last : ℤ)
    (value :
      ((sourceStep.unifiedGenerated.cochainFace.root).2.termPresentation first).cokernel) :
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        ((sourceStep.unifiedGenerated.cochainFace.root).2.termPresentation last)
        ((sourceStep.unifiedGenerated.cochainFace.root).2.differentialPresentedMap middle last
          ((sourceStep.unifiedGenerated.cochainFace.root).2.differentialPresentedMap
            first middle value)) = 0 ∧
      HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  ⟨sourceStep.unifiedGenerated_cochain_d_squared first middle last value,
    sourceStep.unified_wholeLedgerWriteBack_eq_root,
    sourceStep.unified_nextCurrent_eq_root⟩

theorem root_ledger_next_preserved :
    HEq sourceStep.wholeLedgerWriteBack
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          sourceVisit.current) ∧
      sourceStep.nextCurrent = sourceRoot.generatedNextCurrentAt sourceVisit :=
  ⟨sourceStep.unified_wholeLedgerWriteBack_eq_root,
    sourceStep.unified_nextCurrent_eq_root⟩

example : True := by
  fail_if_success exact sourceStep.callerPairing
  fail_if_success exact sourceStep.callerDuality
  fail_if_success exact sourceStep.callerEquivalence
  fail_if_success exact sourceStep.callerResidual
  trivial

#print axioms package_total
#print axioms pairing_readback
#print axioms canonical_perfect_pair_readback
#print axioms exact_occurrence_reused
#print axioms actual_relation_cochain_reused
#print axioms actual_algebra_combinatorial_reused
#print axioms generated_combinatorial_history_mono
#print axioms generated_topology_restriction_ledger_next
#print axioms generated_topology_kernel_ledger_next
#print axioms generated_topology_inseparable_zero_iff_kernel
#print axioms generated_logical_equation
#print axioms generated_cochain_ledger_next
#print axioms root_ledger_next_preserved

end
end UnifiedFourFaceCofinalAdapterRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
