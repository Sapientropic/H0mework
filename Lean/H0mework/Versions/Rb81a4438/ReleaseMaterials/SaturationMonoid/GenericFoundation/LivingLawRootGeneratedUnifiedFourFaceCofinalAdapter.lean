import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceKernel
import H0mework.Versions.Rb81a4438.Realization.Faces.DualityTransport
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel

/-!
# Root-controlled installation of the unified four-face producer

The source-polymorphic producer is installed here on the existing cofinal
history/cochain/duality step.  The input occurrence is exactly the common
step's emitted source occurrence; the evaluation is the installed pairing and
the faithful map is the common step's completion evaluation.  The package is
therefore a dependent face of the existing root, not a new source.  The
whole-ledger write-back and generated next are read directly from the parent
step.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalHistoryCochainDuality

open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open CofinalHistorySettlement
open CofinalFaithfulRealization
open CochainRelationPresentation
open FiniteAdditiveRelationPresentation
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open UnifiedFourFace
open CofinalAllPrimeTopology
open SourceGeneratedPrimePowerCompletion

noncomputable section

universe u

namespace RootGeneratedCofinalHistoryCochainDualityStepAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}
variable {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}

abbrev UnifiedSource
    (_step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    visit.current

abbrev UnifiedCarrier
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.commonStep.history.CompletionCarrier

/-- Dependent payloads keep each generated sibling attached to the source
    occurrence that produced it, including branches of the root unfolding. -/
abbrev UnifiedAlgebra
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    RootedAccountedUnfolding
      ((recognition.materialLaw.commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ]
        (recognition.materialLaw.commonLaw.historyAt occurrence).CompletionCarrier →ₗ[ℤ] ℤ)

def algebraAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedAlgebra step :=
  ⟨occurrence, recognition.materialLaw.pairingAt occurrence⟩

abbrev UnifiedCombinatorial
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    RootGeneratedCofinalHistoryAt
      (recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt occurrence)
      (recognition.materialLaw.commonLaw.historyLaw.seedAt occurrence)
      (recognition.materialLaw.commonLaw.historyLaw.continuationAt occurrence)

def combinatorialAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedCombinatorial step :=
  ⟨occurrence, recognition.materialLaw.commonLaw.historyAt occurrence⟩

/-- Every prime-power restriction is generated from the original presented
completion. No prime or observation tower is chosen by the input. -/
abbrev UnifiedTopological
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    TopologicalAt
      (recognition.materialLaw.commonLaw.historyAt occurrence)

def topologyAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedTopological step :=
  ⟨occurrence, TopologicalAt.generate
    (recognition.materialLaw.commonLaw.historyAt occurrence)⟩

/-- The logic coordinate is the already generated cochain equation itself,
    with its source occurrence retained; no excluded-middle branch enters. -/
abbrev UnifiedLogical
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    PLift (∀ first middle last : ℤ,
      ∀ value :
        ((recognition.materialLaw.commonLaw.cochainAt occurrence).termPresentation
          first).cokernel,
        finiteAdditiveRelationPresentation_cokernelEquiv _
            ((recognition.materialLaw.commonLaw.cochainAt occurrence).termPresentation last)
            ((recognition.materialLaw.commonLaw.cochainAt occurrence).differentialPresentedMap
              middle last
              ((recognition.materialLaw.commonLaw.cochainAt occurrence).differentialPresentedMap
                first middle value)) = 0)

def logicalAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedLogical step :=
  ⟨occurrence, ⟨fun first middle last value =>
    (recognition.materialLaw.commonLaw.cochainAt occurrence).differential_presentedMap_comp_zero
      first middle last value⟩⟩

abbrev UnifiedRelation
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    RootGeneratedCofinalFaithfulRealizationAt
      (recognition.materialLaw.commonLaw.historyAt occurrence)
      (recognition.materialLaw.commonLaw.evaluatorOccurrenceAt occurrence)

def relationAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedRelation step :=
  ⟨occurrence, recognition.materialLaw.commonLaw.faithfulAt occurrence⟩

abbrev UnifiedCochain
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  (occurrence : UnifiedSource step) ×
    RootGeneratedCochainRelationPresentationAt
      (recognition.materialLaw.commonLaw.historyAt occurrence).root
      (recognition.materialLaw.commonLaw.complexAt occurrence)

def cochainAt
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (occurrence : UnifiedSource step) : UnifiedCochain step :=
  ⟨occurrence, recognition.materialLaw.commonLaw.cochainAt occurrence⟩

abbrev UnifiedInput
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) : Type _ :=
  Input (UnifiedSource step) (UnifiedAlgebra step)
    (UnifiedCombinatorial step) (UnifiedTopological step) (UnifiedLogical step)
    (UnifiedRelation step) (UnifiedCochain step)
    (UnifiedCarrier step) (UnifiedCarrier step)

def unifiedInput
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    UnifiedInput step where
  occurrence := step.commonStep.history.root
  algebraAt := step.algebraAt
  combinatorialAt := step.combinatorialAt
  topologicalAt := step.topologyAt
  logicalAt := step.logicalAt
  relationAt := step.relationAt
  cochainAt := step.cochainAt
  dualEvaluationAt := fun _ => step.pairingFace.leftEvaluation
  faithfulAt := fun _ => LinearMap.id

def unifiedGenerated
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    UnifiedFourFace.Generated (unifiedInput step) :=
  UnifiedFourFace.generate (unifiedInput step)

@[simp] theorem unifiedInput_occurrence
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedInput step).occurrence = step.commonStep.history.root :=
  rfl

theorem unifiedGenerated_algebra_actual
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq (step.unifiedGenerated.algebraFace.root).2
      step.pairingFace.actualPairing := by
  have same := recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence
  change (step.commonStep.history.root).root = step.sourceOccurrence at same
  have payload :
      (step.commonStep.history.root.map step.algebraAt).root =
        step.algebraAt step.sourceOccurrence := by
    rw [RootedAccountedUnfolding.root_map]
    exact congrArg step.algebraAt same
  change HEq ((step.commonStep.history.root.map step.algebraAt).root).2
    step.pairingFace.actualPairing
  exact (Sigma.mk.inj payload).2

theorem unifiedGenerated_combinatorial_actual
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq (step.unifiedGenerated.combinatorialFace.root).2
      step.commonStep.history := by
  have same := recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence
  change (step.commonStep.history.root).root = step.sourceOccurrence at same
  have payload :
      (step.commonStep.history.root.map step.combinatorialAt).root =
        step.combinatorialAt step.sourceOccurrence := by
    rw [RootedAccountedUnfolding.root_map]
    exact congrArg step.combinatorialAt same
  change HEq ((step.commonStep.history.root.map step.combinatorialAt).root).2
    step.commonStep.history
  exact (Sigma.mk.inj payload).2

/-- The generated combinatorial sibling retains the original accumulated
    event history across actual continuation stages. -/
theorem unifiedGenerated_combinatorial_history_mono
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    {first later : Nat} (order : first ≤ later) :
    ∀ event,
      event ∈ (step.unifiedGenerated.combinatorialFace.root).2.observedEvents first →
      event ∈ (step.unifiedGenerated.combinatorialFace.root).2.observedEvents later :=
  (step.unifiedGenerated.combinatorialFace.root).2.observedEvents_mono order

theorem unifiedGenerated_topological_source
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.unifiedGenerated.topologicalFace.root).1 = step.sourceOccurrence := by
  change ((step.commonStep.history.root.map step.topologyAt).root).1 =
    step.sourceOccurrence
  rw [RootedAccountedUnfolding.root_map]
  exact recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence

/-- Every prime-power observation is an actual restriction of this history's
presented completion, with the original installed source and next retained. -/
theorem unifiedGenerated_topological_restriction_ledger_next
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (prime : Nat.Primes) (stage : Nat)
    (value :
      (recognition.materialLaw.commonLaw.historyAt
        (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    (restriction (L :=
      (recognition.materialLaw.commonLaw.historyAt
        (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier)
      prime stage).hom
        ((step.unifiedGenerated.topologicalFace.root).2.observation value prime) =
      stageProjection (L :=
        (recognition.materialLaw.commonLaw.historyAt
          (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier)
        prime stage value ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (recognition.commonRecognition.installation.embed PUnit.unit)
          step.sourceOccurrence)
        (recognition.materialLaw.commonLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨allPrime_restriction prime stage value,
    step.commonStep.installedCochain_factorizes,
    step.wholeLedgerWriteBack_eq_root,
    step.nextCurrent_eq_root⟩

/-- The exact topological loss remains a residual: precisely the elements
divisible by every power of every prime are observationally invisible. -/
theorem unifiedGenerated_topological_kernel_ledger_next
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (value :
      (recognition.materialLaw.commonLaw.historyAt
        (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    (value ∈ LinearMap.ker
        (step.unifiedGenerated.topologicalFace.root).2.observation ↔
      ∀ prime : Nat.Primes, ∀ stage : Nat,
        ∃ divided :
          (recognition.materialLaw.commonLaw.historyAt
            (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier,
          (prime.1 : ℤ) ^ (stage + 1) • divided = value) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨allPrimeKernel_iff value,
    step.wholeLedgerWriteBack_eq_root,
    step.nextCurrent_eq_root⟩

theorem unifiedGenerated_topological_inseparable_zero_iff_kernel
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (value :
      (recognition.materialLaw.commonLaw.historyAt
        (step.unifiedGenerated.topologicalFace.root).1).CompletionCarrier) :
    @Inseparable _
        (step.unifiedGenerated.topologicalFace.root).2.uniformity.toTopologicalSpace
        value 0 ↔
      value ∈ LinearMap.ker
        (step.unifiedGenerated.topologicalFace.root).2.observation :=
  (step.unifiedGenerated.topologicalFace.root).2.inseparable_zero_iff_kernel value

theorem unifiedGenerated_logical_source
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.unifiedGenerated.logicalFace.root).1 = step.sourceOccurrence := by
  change ((step.commonStep.history.root.map step.logicalAt).root).1 =
    step.sourceOccurrence
  rw [RootedAccountedUnfolding.root_map]
  exact recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence

theorem unifiedGenerated_logical_d_squared
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (first middle last : ℤ)
    (value :
      ((recognition.materialLaw.commonLaw.cochainAt
        (step.unifiedGenerated.logicalFace.root).1).termPresentation first).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        ((recognition.materialLaw.commonLaw.cochainAt
          (step.unifiedGenerated.logicalFace.root).1).termPresentation last)
        ((recognition.materialLaw.commonLaw.cochainAt
          (step.unifiedGenerated.logicalFace.root).1).differentialPresentedMap middle last
          ((recognition.materialLaw.commonLaw.cochainAt
            (step.unifiedGenerated.logicalFace.root).1).differentialPresentedMap
              first middle value)) = 0 :=
  (step.unifiedGenerated.logicalFace.root).2.down first middle last value

theorem unifiedGenerated_relation_source
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.unifiedGenerated.relationFace.root).1 = step.sourceOccurrence := by
  change ((step.commonStep.history.root.map step.relationAt).root).1 =
    step.sourceOccurrence
  rw [RootedAccountedUnfolding.root_map]
  exact recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence

theorem unifiedGenerated_relation_actual
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq (step.unifiedGenerated.relationFace.root).2
      step.commonStep.faithful := by
  have same := recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence
  change (step.commonStep.history.root).root = step.sourceOccurrence at same
  have payload :
      (step.commonStep.history.root.map step.relationAt).root =
        step.relationAt step.sourceOccurrence := by
    rw [RootedAccountedUnfolding.root_map]
    exact congrArg step.relationAt same
  change HEq ((step.commonStep.history.root.map step.relationAt).root).2
    step.commonStep.faithful
  exact (Sigma.mk.inj payload).2

theorem unifiedGenerated_cochain_source
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    (step.unifiedGenerated.cochainFace.root).1 = step.sourceOccurrence := by
  change ((step.commonStep.history.root.map step.cochainAt).root).1 =
    step.sourceOccurrence
  rw [RootedAccountedUnfolding.root_map]
  exact recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence

theorem unifiedGenerated_cochain_actual
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq (step.unifiedGenerated.cochainFace.root).2
      step.commonStep.cochainFace := by
  have same := recognition.materialLaw.commonLaw.historyLaw.rootOccurrenceAt_root
    step.sourceOccurrence
  change (step.commonStep.history.root).root = step.sourceOccurrence at same
  have payload :
      (step.commonStep.history.root.map step.cochainAt).root =
        step.cochainAt step.sourceOccurrence := by
    rw [RootedAccountedUnfolding.root_map]
    exact congrArg step.cochainAt same
  change HEq ((step.commonStep.history.root.map step.cochainAt).root).2
    step.commonStep.cochainFace
  exact (Sigma.mk.inj payload).2

/-- The unified cochain face now executes the common occurrence's actual
    presented differential, including its calculated relation quotient. -/
theorem unifiedGenerated_cochain_d_squared
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    (first middle last : ℤ)
    (value : ((step.unifiedGenerated.cochainFace.root).2.termPresentation first).cokernel) :
    finiteAdditiveRelationPresentation_cokernelEquiv _
        ((step.unifiedGenerated.cochainFace.root).2.termPresentation last)
        ((step.unifiedGenerated.cochainFace.root).2.differentialPresentedMap middle last
          ((step.unifiedGenerated.cochainFace.root).2.differentialPresentedMap
            first middle value)) = 0 :=
  (step.unifiedGenerated.cochainFace.root).2.differential_presentedMap_comp_zero
    first middle last value

theorem unifiedGenerated_readback
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedGenerated step).embedding.comp
        (unifiedGenerated step).canonical =
      UnifiedFourFace.RootDualEvaluation (unifiedInput step) :=
  UnifiedFourFace.generated_dual_readback (unifiedInput step)

theorem unifiedGenerated_canonical_perfect_pair_readback
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    (unifiedGenerated step).canonicalPerfectPair.inclusion.comp
        (unifiedGenerated step).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding
        (UnifiedFourFace.RootDualEvaluation (unifiedInput step)) :=
  SourceGeneratedCanonicalPerfectPair.generated_readback
    (UnifiedFourFace.RootDualEvaluation (unifiedInput step))

theorem unifiedGenerated_total
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    Nonempty (UnifiedFourFace.Generated (unifiedInput step)) :=
  UnifiedFourFace.generated_total (unifiedInput step)

theorem unified_wholeLedgerWriteBack_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    HEq (step.wholeLedgerWriteBack)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.wholeLedgerWriteBack_eq_root

@[simp] theorem unified_nextCurrent_eq_root
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit)
    :
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  step.nextCurrent_eq_root

end RootGeneratedCofinalHistoryCochainDualityStepAt

end
end CofinalHistoryCochainDuality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
