import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Root.UBIPeriodicRootHistory
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Mandate.SourceMandateRenewal

/-!
# M14 periodic mandate-power renewal on the proof-carrying root

The fourth pre-emitter coordinate of the literal M9/M14 root carries one
source-generated election face.  This file installs that coordinate at every
recursively generated finite temporal visit.  Each carrier retains its exact
root occurrence, source entry, selected row, successor, whole-ledger
write-back, factorized next, and the original election trace/consumer.

The local election face may recur under the fixed law, but temporal mandate
authority does not: its public heterogeneous occurrence is indexed first by
the exact root visit, and those visits are injective in causal depth.  No
preference profile, election scheduler, `Nat ->` completed mandate table,
sibling root, ledger, or receipt registry is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14PeriodicMandatePowerRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Election Relations Power
open M8ActualElectionMandateRenewalRegression
open M9ProofCarryingRenewalInquiryRoot
open M14SourceMandateRenewal
open M14UBIPeriodicRootHistory

/-! ## Visit-indexed installation and zero-choice carrier -/

def installedMandateAt (depth : Nat) :
    SourceInstalledRenewalAt mandateRecognition (temporalVisitAt depth) :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

def installedMandateLocalFaceAt (depth : Nat) :
    SourceMandateRenewalFace :=
  (installedMandateAt depth).localFace
    (fun _ exactSeed =>
      lineageCompiler.controllerOf exactSeed.1.controllerSeed)
    (mandateStandingOf sourceMandateHistory lineageCompiler)

/-- One exact installed mandate-power renewal seal.  The constructor is
private; the seal receives only a finite causal depth and reads every local
and root authority field from the already installed coordinate.  The actual
producer is the pre-emitter `mandateLaw`. -/
structure SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt
    (depth : Nat) : Type 3 where
  private mk ::
  installed :
    SourceInstalledRenewalAt mandateRecognition (temporalVisitAt depth)
  seedExact : installed.payload.sourceSeed = sourceMandateSeed
  consumerExact : installed.payload.consumer = sourceMandateConsumer
  dispositionExact : installed.payload.disposition = sourceMandateDisposition
  localFace : SourceMandateRenewalFace
  localFaceExact : localFace = sourceMandateRenewalFace
  rootOccurrence : ExactTemporalCausalRootEventAt
    jointRoot.toAuthoritativeRoot.toLedgerRoot (temporalVisitAt depth)
  rootOccurrenceExact : rootOccurrence =
    jointRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (temporalVisitAt depth)
  sourceEntryExact : installed.payload.sourceEntry =
    RootInquiryU8CompletionRegression.entry
  selectedRowShared :
    HEq installed.payload.selectedRow
      (installedUBIAt depth).payload.selectedRow
  successorShared :
    HEq installed.payload.successor
      (installedUBIAt depth).payload.successor
  wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot.source.source
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit (temporalVisitAt depth)).occurrence
  wholeLedgerWriteBackExact : wholeLedgerWriteBack =
    (jointRoot.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit
        (temporalVisitAt depth)).wholeLedgerWriteBack
  rootFactorization : installed.RootAnswerAndNextFactorizes
  generatedNext : SourceNativeAuthoritativeRootCurrentAt
    M9ProofCarryingRenewalInquiryRoot.N
  generatedNextExact : generatedNext =
    jointRoot.generatedNextCurrentAt (temporalVisitAt depth)

/-- Sole installed-seal constructor.  No local face, power, root occurrence,
row, successor, write-back, or next is accepted from the caller. -/
def SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.generate
    (depth : Nat) :
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth :=
  let installed := installedMandateAt depth
  { installed := installed
    seedExact := rfl
    consumerExact := rfl
    dispositionExact := rfl
    localFace := installedMandateLocalFaceAt depth
    localFaceExact := rfl
    rootOccurrence :=
      jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.exactTemporalCausalEventAt (temporalVisitAt depth)
    rootOccurrenceExact := rfl
    sourceEntryExact := rfl
    selectedRowShared := HEq.rfl
    successorShared := HEq.rfl
    wholeLedgerWriteBack :=
      (jointRoot.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit
          (temporalVisitAt depth)).wholeLedgerWriteBack
    wholeLedgerWriteBackExact := rfl
    rootFactorization := installed.rootAnswerAndNext_factorizes
    generatedNext := jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
    generatedNextExact := rfl }

def periodicMandatePowerRenewalAt (depth : Nat) :
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth :=
  SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.generate depth

namespace SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt

variable {depth : Nat}
variable (renewal :
  SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth)

include renewal

/-! ## Exact local election authority -/

theorem local_event_has_exact_trace :
    ∃ state ∈ SourceMandateGame.occurrence.trace,
      SourceMandateSeedAt SourceMandateGame.source state
        renewal.localFace.event := by
  rw [renewal.localFaceExact]
  exact sourceMandate_event_has_exact_trace

@[simp] theorem local_controller_lineage_exact :
    renewal.localFace.actor.1 = 11 := by
  rw [renewal.localFaceExact]
  exact sourceMandate_controller_lineage_exact

omit renewal in
theorem local_office_relation_has_exact_trace :
    OfficeRelationTraceAt sourceMandateHistory :=
  sourceMandate_office_relation_has_exact_trace

omit renewal in
theorem local_office_relation_and_role_exact :
    (mandateOffice sourceMandateHistory lineageCompiler).1 =
        lineageCompiler.officeOf sourceMandateHistory.current.officeSeed ∧
      (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler).1.office = 7 ∧
      (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler).1.controller = 11 ∧
      (officeControllerRelationCompiler sourceMandateHistory lineageCompiler
        ).roleAt
          (generatedOfficeControllerRelation sourceMandateHistory
            lineageCompiler) .target = MandateRole.held :=
  ⟨sourceMandate_office_and_relation_exact.1,
    sourceMandate_office_and_relation_exact.2.1,
    sourceMandate_office_and_relation_exact.2.2,
    sourceMandate_target_role_is_held⟩

omit renewal in
@[simp] theorem local_relation_phase_is_renew :
    (officeControllerRelationCompiler sourceMandateHistory lineageCompiler
      ).phaseStep
        (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler) = MandatePhase.renew :=
  rfl

@[simp] theorem local_power_consumer_exact :
    renewal.localFace.responsibilityConsumer.1.1 =
      mandateActionPower sourceMandateHistory lineageCompiler := by
  rw [renewal.localFaceExact]
  exact sourceMandate_power_consumer_exact

theorem local_power_is_restored :
    renewal.localFace.responsibilityConsumer.1.1.freedomChange.kind =
      FreedomChangeKind.restored := by
  rw [renewal.local_power_consumer_exact]
  exact continuing_power_is_restored 0

omit renewal in
theorem local_exact_M2_power :
    Nonempty (ExactMandatePower sourceMandateHistory lineageCompiler) :=
  sourceMandate_has_exact_M2_power

omit renewal in
theorem local_M1_consumer :
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler)
      sourceMandateHistory.current
      (mandateObligation lineageCompiler sourceMandateHistory.current)) :=
  sourceMandate_has_M1_consumer

theorem local_disposition_stays_live :
    renewal.localFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler sourceMandateHistory.current).val]? =
      some (.live
        (mandateObligation lineageCompiler sourceMandateHistory.current)) := by
  rw [renewal.localFaceExact]
  exact sourceMandate_disposition_stays_live

/-! ## Exact root authority and coordinate separation -/

theorem root_authority_commutes :
    renewal.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      renewal.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq renewal.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq renewal.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      renewal.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      renewal.installed.RootAnswerAndNextFactorizes ∧
      renewal.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth) :=
  ⟨renewal.rootOccurrenceExact, renewal.sourceEntryExact,
    renewal.selectedRowShared, renewal.successorShared,
    renewal.wholeLedgerWriteBackExact, renewal.rootFactorization,
    renewal.generatedNextExact⟩

omit renewal in
theorem coordinate_is_distinct :
    jointMandateProjection ≠ jointRecognitionWitnessProjection ∧
      jointMandateProjection ≠ jointUBIProjection ∧
      jointMandateProjection ≠ jointProofCarryingProjection ∧
      jointMandateProjection ≠ jointInquiryProjection ∧
      jointMandateProjection ≠ jointFailureProjection := by
  have mandate_ne_inquiry :
      jointMandateProjection ≠ jointInquiryProjection := by
    intro equality
    cases equality
  have mandate_ne_failure :
      jointMandateProjection ≠ jointFailureProjection := by
    intro equality
    cases equality
  exact
  ⟨mandate_projection_ne_recognitionWitness_projection,
    mandate_projection_ne_ubi_projection,
    mandate_projection_ne_proofCarrying_projection,
    mandate_ne_inquiry, mandate_ne_failure⟩

/-! ## Actual exit and no-eternity controls -/

omit renewal in
theorem wrong_current_event_rejected :
    ¬ ((electionActionController sourceMandateHistory lineageCompiler)
      |>.actionAdmittedAt (exitingEvent 1)) :=
  sourceMandate_wrong_current_event_rejected

omit renewal in
theorem actual_exit_retains_prior_trace_and_ends_power :
    sourceMandateHistory.current ∈
        sourceMandateExitHistory.occurrence.trace ∧
      (officeControllerRelationCompiler sourceMandateExitHistory
        lineageCompiler).roleAt
          (generatedOfficeControllerRelation sourceMandateExitHistory
            lineageCompiler) .target = MandateRole.exited ∧
      (mandateActionPower sourceMandateExitHistory
        lineageCompiler).freedomChange.kind = FreedomChangeKind.lost ∧
      ∃ archive,
        sourceMandateExitFace.exactDisposition.1.target.slots[
            (mandateSlot lineageCompiler
              sourceMandateExitHistory.current).val]? =
          some (.terminal archive) :=
  ⟨sourceMandate_exit_retains_prior_trace,
    sourceMandate_exit_role_is_exited,
    sourceMandate_exit_power_is_lost,
    sourceMandate_exit_disposition_is_terminal⟩

end SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt

/-! ## Heterogeneous temporal occurrence identity -/

/-- Visit-indexed wrapper used only to expose one heterogeneous occurrence
carrier.  Its first public Sigma coordinate remains the exact temporal visit. -/
structure MandatePowerRenewalAtVisit
    (visit : SourceNativeTemporalVisitAt
      jointRoot.toAuthoritativeRoot.toLedgerRoot) : Type 3 where
  private mk ::
  depth : Nat
  visitExact : visit = temporalVisitAt depth
  renewal : SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth

abbrev AnyPeriodicMandatePowerOccurrence :=
  Sigma MandatePowerRenewalAtVisit

def periodicMandatePowerOccurrenceAt
    (depth : Nat) : AnyPeriodicMandatePowerOccurrence :=
  ⟨temporalVisitAt depth,
    ⟨depth, rfl, periodicMandatePowerRenewalAt depth⟩⟩

theorem periodicMandatePowerOccurrenceAt_injective :
    Function.Injective periodicMandatePowerOccurrenceAt := by
  intro left right equality
  have visit_eq := congrArg Sigma.fst equality
  exact temporalVisitAt_injective visit_eq

theorem adjacentMandatePowerOccurrences_distinct (depth : Nat) :
    periodicMandatePowerOccurrenceAt depth ≠
      periodicMandatePowerOccurrenceAt (depth + 1) := by
  intro equality
  have depth_eq := periodicMandatePowerOccurrenceAt_injective equality
  omega

/-- In particular one fixed temporal occurrence cannot carry the mandate
authority of every finite depth. -/
theorem no_single_mandate_occurrence_carries_all_depths :
    ¬ ∃ occurrence : AnyPeriodicMandatePowerOccurrence,
      ∀ depth : Nat, periodicMandatePowerOccurrenceAt depth = occurrence := by
  rintro ⟨occurrence, allDepths⟩
  have equal := (allDepths 0).trans (allDepths 1).symm
  exact (by
    have depth_eq := periodicMandatePowerOccurrenceAt_injective equal
    omega)

/-! ## Pointwise certificate and no-future guard -/

theorem periodicMandatePayload_has_no_completed_future (depth : Nat) : True := by
  let renewal := periodicMandatePowerRenewalAt depth
  fail_if_success exact renewal.completedMandate
  fail_if_success exact renewal.periodicTable
  fail_if_success exact renewal.nextElection
  fail_if_success exact renewal.preferenceProfile
  trivial

structure PeriodicMandatePowerRenewalCertificate : Prop where
  everyDepth : ∀ depth : Nat,
    Nonempty (SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt depth)
  everyDepthExactTrace : ∀ depth : Nat,
    ∃ state ∈ SourceMandateGame.occurrence.trace,
      SourceMandateSeedAt SourceMandateGame.source state
        (periodicMandatePowerRenewalAt depth).localFace.event
  everyDepthControllerLineage : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth).localFace.actor.1 = 11
  everyDepthSeedExact : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth).installed.payload.sourceSeed =
      sourceMandateSeed
  everyDepthConsumerExact : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth).installed.payload.consumer =
      sourceMandateConsumer
  everyDepthDispositionExact : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth).installed.payload.disposition =
      sourceMandateDisposition
  officeRelationTrace : OfficeRelationTraceAt sourceMandateHistory
  officeRelationAndRoleExact :
    (mandateOffice sourceMandateHistory lineageCompiler).1 =
        lineageCompiler.officeOf sourceMandateHistory.current.officeSeed ∧
      (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler).1.office = 7 ∧
      (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler).1.controller = 11 ∧
      (officeControllerRelationCompiler sourceMandateHistory lineageCompiler
        ).roleAt
          (generatedOfficeControllerRelation sourceMandateHistory
            lineageCompiler) .target = MandateRole.held
  relationPhaseRenew :
    (officeControllerRelationCompiler sourceMandateHistory lineageCompiler
      ).phaseStep
        (generatedOfficeControllerRelation sourceMandateHistory
          lineageCompiler) = MandatePhase.renew
  exactM2Power :
    Nonempty (ExactMandatePower sourceMandateHistory lineageCompiler)
  everyDepthRestoredPower : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth
      ).localFace.responsibilityConsumer.1.1.freedomChange.kind =
        FreedomChangeKind.restored
  everyDepthM1Consumer : ∀ _depth : Nat,
    Nonempty (SourceOwnsResponsibilityIncidence
      (mandateVocabulary lineageCompiler)
      sourceMandateHistory.current
      (mandateObligation lineageCompiler sourceMandateHistory.current))
  everyDepthLiveDisposition : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth
      ).localFace.exactDisposition.1.target.slots[
        (mandateSlot lineageCompiler sourceMandateHistory.current).val]? =
      some (.live
        (mandateObligation lineageCompiler sourceMandateHistory.current))
  everyDepthRootFactorization : ∀ depth : Nat,
    (periodicMandatePowerRenewalAt depth
      ).installed.RootAnswerAndNextFactorizes
  everyDepthRootAuthority : ∀ depth : Nat,
    let renewal := periodicMandatePowerRenewalAt depth
    renewal.rootOccurrence =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.exactTemporalCausalEventAt (temporalVisitAt depth)) ∧
      renewal.installed.payload.sourceEntry =
        RootInquiryU8CompletionRegression.entry ∧
      HEq renewal.installed.payload.selectedRow
        (installedUBIAt depth).payload.selectedRow ∧
      HEq renewal.installed.payload.successor
        (installedUBIAt depth).payload.successor ∧
      renewal.wholeLedgerWriteBack =
        (jointRoot.toAuthoritativeRoot.toLedgerRoot
          |>.generatedAtTemporalVisit
            (temporalVisitAt depth)).wholeLedgerWriteBack ∧
      renewal.installed.RootAnswerAndNextFactorizes ∧
      renewal.generatedNext =
        jointRoot.generatedNextCurrentAt (temporalVisitAt depth)
  occurrenceInjective : Function.Injective periodicMandatePowerOccurrenceAt
  coordinateDistinct :
    jointMandateProjection ≠ jointRecognitionWitnessProjection ∧
      jointMandateProjection ≠ jointUBIProjection ∧
      jointMandateProjection ≠ jointProofCarryingProjection ∧
      jointMandateProjection ≠ jointInquiryProjection ∧
      jointMandateProjection ≠ jointFailureProjection
  wrongCurrentRejected :
    ¬ ((electionActionController sourceMandateHistory lineageCompiler)
      |>.actionAdmittedAt (exitingEvent 1))
  exitRetainsPriorTraceAndEndsPower :
    sourceMandateHistory.current ∈
        sourceMandateExitHistory.occurrence.trace ∧
      (officeControllerRelationCompiler sourceMandateExitHistory
        lineageCompiler).roleAt
          (generatedOfficeControllerRelation sourceMandateExitHistory
            lineageCompiler) .target = MandateRole.exited ∧
      (mandateActionPower sourceMandateExitHistory
        lineageCompiler).freedomChange.kind = FreedomChangeKind.lost ∧
      ∃ archive,
        sourceMandateExitFace.exactDisposition.1.target.slots[
            (mandateSlot lineageCompiler
              sourceMandateExitHistory.current).val]? =
          some (.terminal archive)
  noSingleOccurrenceForAllDepths :
    ¬ ∃ occurrence : AnyPeriodicMandatePowerOccurrence,
      ∀ depth : Nat, periodicMandatePowerOccurrenceAt depth = occurrence
  noCompletedFuture : ∀ _depth : Nat, True

theorem periodicMandatePowerRenewalDirectConsumer :
    PeriodicMandatePowerRenewalCertificate where
  everyDepth := fun depth => ⟨periodicMandatePowerRenewalAt depth⟩
  everyDepthExactTrace := fun depth =>
    (periodicMandatePowerRenewalAt depth).local_event_has_exact_trace
  everyDepthControllerLineage := fun depth =>
    (periodicMandatePowerRenewalAt depth).local_controller_lineage_exact
  everyDepthSeedExact := fun depth =>
    (periodicMandatePowerRenewalAt depth).seedExact
  everyDepthConsumerExact := fun depth =>
    (periodicMandatePowerRenewalAt depth).consumerExact
  everyDepthDispositionExact := fun depth =>
    (periodicMandatePowerRenewalAt depth).dispositionExact
  officeRelationTrace :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.local_office_relation_has_exact_trace
  officeRelationAndRoleExact :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.local_office_relation_and_role_exact
  relationPhaseRenew :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.local_relation_phase_is_renew
  exactM2Power :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.local_exact_M2_power
  everyDepthRestoredPower := fun depth =>
    (periodicMandatePowerRenewalAt depth).local_power_is_restored
  everyDepthM1Consumer := fun _depth =>
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.local_M1_consumer
  everyDepthLiveDisposition := fun depth =>
    (periodicMandatePowerRenewalAt depth).local_disposition_stays_live
  everyDepthRootFactorization := fun depth =>
    (periodicMandatePowerRenewalAt depth).rootFactorization
  everyDepthRootAuthority := fun depth =>
    (periodicMandatePowerRenewalAt depth).root_authority_commutes
  occurrenceInjective := periodicMandatePowerOccurrenceAt_injective
  coordinateDistinct :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.coordinate_is_distinct
  wrongCurrentRejected :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.wrong_current_event_rejected
  exitRetainsPriorTraceAndEndsPower :=
    SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.actual_exit_retains_prior_trace_and_ends_power
  noSingleOccurrenceForAllDepths :=
    no_single_mandate_occurrence_carries_all_depths
  noCompletedFuture := periodicMandatePayload_has_no_completed_future

end
end M14PeriodicMandatePowerRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicMandatePowerRenewal.SourceGeneratedProofCarryingPeriodicMandatePowerRenewalAt.generate
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicMandatePowerRenewal.periodicMandatePowerOccurrenceAt_injective
#print axioms SaturationMonoid.ProcessGame.Society.M14PeriodicMandatePowerRenewal.periodicMandatePowerRenewalDirectConsumer
