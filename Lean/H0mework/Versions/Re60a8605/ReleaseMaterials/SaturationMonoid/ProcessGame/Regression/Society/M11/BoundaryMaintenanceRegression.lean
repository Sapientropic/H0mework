/-
Copyright (c) 2026 Luciano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luciano
-/
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityRenewalRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityDebitedRun
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M11.GeneratedSocialSpaceRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Space.BoundaryMaintenance

/-!
# M11 boundary-maintenance regression

This regression fixes a boundary-maintenance restriction before constructing
the root authority source.  It reuses the M10 occurrence/rate compiler,
singleton root source and exact first maintenance debit, together with the M11
crossing seeds, endpoints, flow and boundary classifier.  The installed M8
renewal therefore reads one exact boundary certificate and one actual debit
event from its pre-emitter payload; the local run cannot be attached after the
root occurrence has already been emitted.

The M11 display fixture uses a one-constructor `BoundaryLabel`, whereas the M10
actual debit uses `PUnit` as its lifecycle lineage.  The fixed compiler below
retains the same exact crossings and all source seed incidences while choosing
the lifecycle-compatible `PUnit` lineage image before the root is built.  No
post-emitter cast, second ledger, registry, or social scheduler is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M11BoundaryMaintenanceRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity Space

abbrev LocalGame := M10OccurrenceCapacityProcessFixture.game
abbrev LocalSeed := M10OccurrenceCapacityProcessFixture.Seed
abbrev LocalSeedAt := M10OccurrenceCapacityProcessFixture.seedAt
abbrev LocalLineage := M10OccurrenceCapacityProcessFixture.Lineage
abbrev localLineageOf := M10OccurrenceCapacityProcessFixture.lineageOf
abbrev localFocalSeed := M10OccurrenceCapacityProcessFixture.focalSeed
abbrev rateCompiler :=
  M11GeneratedSocialSpaceCrossingFixture.rateCompiler

/-! ## Fixed crossing/lineage source -/

/-- Maintenance view of the existing M11 crossing compiler.  It preserves the
same M10 queue positions, site/boundary seeds, endpoint incidences, flows and
classifier, while fixing the boundary image in the exact lifecycle lineage
carrier used by the M10 debit fixture. -/
def maintenanceCrossingCompiler : SourceOwnedCrossingCompiler.{0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0} rateCompiler where
  SiteSeed := M11GeneratedSocialSpaceCrossingFixture.SiteSeed
  SiteSeedAt := M11GeneratedSocialSpaceCrossingFixture.siteSeedAt
  SiteLineage := M11GeneratedSocialSpaceCrossingFixture.SiteLineage
  siteLineageOf := M11GeneratedSocialSpaceCrossingFixture.siteLineageOf
  originSeedAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.originSeedAt
  targetSeedAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.targetSeedAt
  originSeedIncidence :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.originSeedIncidence
  targetSeedIncidence :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.targetSeedIncidence
  FlowPayloadAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.FlowPayloadAt
  flowPayloadAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.flowPayloadAt
  BoundarySeed := M11GeneratedSocialSpaceCrossingFixture.BoundarySeed
  BoundarySeedAt := M11GeneratedSocialSpaceCrossingFixture.boundarySeedAt
  BoundaryLineage := fun _source => PUnit
  boundaryLineageOf := fun _source _seed => PUnit.unit
  BoundaryActiveAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.BoundaryActiveAt
  BoundaryInactiveAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.BoundaryInactiveAt
  classifyBoundary :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.classifyBoundary
  boundarySeedAt :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.boundarySeedAt
  boundarySeedIncidence :=
    M11GeneratedSocialSpaceCrossingFixture.crossingCompiler.boundarySeedIncidence

/-- Zero-choice maintenance space over the fixed compiler above. -/
def maintenanceSocialSpace :
    SourceGeneratedSocialSpaceAt maintenanceCrossingCompiler :=
  SourceGeneratedSocialSpaceAt.generate maintenanceCrossingCompiler

/-- The maintenance lineage choice does not alter crossing occurrence
identity or chronological order. -/
theorem maintenance_crossingTrace_eq_display_crossingTrace :
    maintenanceSocialSpace.crossingTrace =
      M11GeneratedSocialSpaceRegression.socialSpace.crossingTrace :=
  rfl

abbrev firstCrossing :=
  M11GeneratedSocialSpaceCrossingFixture.firstCrossing

private theorem first_boundary_isSome :
    (maintenanceCrossingCompiler.boundaryCertificate?
      firstCrossing).isSome := by
  rfl

/-- Exact source-classified first boundary certificate.  Its private
production constructor is accessed only through the compiler classifier. -/
def firstBoundaryCertificateProof :
    maintenanceCrossingCompiler.BoundaryCertificateAt firstCrossing :=
  (maintenanceCrossingCompiler.boundaryCertificate?
    firstCrossing).get first_boundary_isSome

def firstBoundaryCertificate :
    maintenanceCrossingCompiler.AnyBoundaryCertificate :=
  ⟨firstCrossing, firstBoundaryCertificateProof⟩

@[simp] theorem firstBoundaryCertificate_crossing :
    firstBoundaryCertificate.crossing = firstCrossing :=
  rfl

theorem firstBoundaryCertificate_mem :
    firstBoundaryCertificate ∈ maintenanceSocialSpace.boundaryCertificates := by
  apply List.mem_filterMap.mpr
  refine ⟨firstCrossing,
    maintenanceCrossingCompiler.exactCrossing_mem firstCrossing, ?_⟩
  unfold SourceOwnedCrossingCompiler.boundaryCertificateEntry?
  rw [← Option.some_get first_boundary_isSome]
  rfl

/-! ## Pre-emitter restriction and fixed renewal root -/

abbrev DebitP := M10OccurrenceCapacityDebitedRunFixture.P
abbrev DebitProcess :=
  M10OccurrenceCapacityDebitedRunFixture.debitProcess

/-- Fixed exact restriction: boundary classification and debit event are
present before the renewal law is installed into the root source. -/
def maintenanceRestriction : BoundaryMaintenanceRestrictionAt
    maintenanceSocialSpace DebitP DebitProcess localFocalSeed where
  certificate := firstBoundaryCertificate
  certificate_mem := firstBoundaryCertificate_mem
  seed_eq_focal := rfl
  sourceState := M10OccurrenceCapacityDebitedRunFixture.sourceState
  edge := M10OccurrenceCapacityDebitedRunFixture.firstMaintenance
  lineage := PUnit.unit
  debitEvent := M10OccurrenceCapacityDebitedRunFixture.DebitEvent.first
  boundaryLineage_heq := by
    change HEq PUnit.unit PUnit.unit
    rfl

abbrev MaintenanceConsumerAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  BoundaryMaintenanceRestrictionAt maintenanceSocialSpace
    DebitP DebitProcess seed

abbrev MaintenanceDispositionAt
    (_seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  PUnit

/-- Regression-only M8 renewal law whose compiled consumer is the exact
maintenance restriction above. -/
def renewalLaw : SourceNativeRenewalProjectionLaw
    (M10OccurrenceCapacityRootSourceFixture.baseAuthoritySource
      |>.restructuringSource.toLedgerSource)
    LocalGame LocalSeed LocalSeedAt
    MaintenanceConsumerAt MaintenanceDispositionAt where
  ActiveAt := fun {_current} _occurrence => PUnit
  InactiveAt := fun {_current} _occurrence => PEmpty
  classify := fun {_current} _occurrence => .inl PUnit.unit
  compile := by
    intro current occurrence _active
    cases current
    rcases occurrence with ⟨support, event⟩
    cases support
    cases event
    exact RootRestrictedRenewalPayloadAt.generate
      localFocalSeed maintenanceRestriction PUnit.unit
      M10OccurrenceCapacityRootSourceFixture.entry
      M10OccurrenceCapacityRootSourceFixture.sourceRow
      M10OccurrenceCapacityRootSourceFixture.successor
  sourceSeed_reflects_rootOccurrence := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence
      _leftActive _rightActive _seedEq
    cases leftCurrent
    cases rightCurrent
    rcases leftOccurrence with ⟨leftSupport, leftEvent⟩
    rcases rightOccurrence with ⟨rightSupport, rightEvent⟩
    cases leftSupport
    cases rightSupport
    cases leftEvent
    cases rightEvent
    rfl

/-- Complete source identity with the exact maintenance coordinate installed
before the root emitter is supplied. -/
def authoritySource : SourceNativeAuthoritySource
    M10OccurrenceCapacityRootSourceFixture.N
    M10OccurrenceCapacityRootSourceFixture.V :=
  withRenewalProjection
    M10OccurrenceCapacityRootSourceFixture.baseAuthoritySource renewalLaw

/-- Regression-only root over the existing M10 singleton source and emitter. -/
def root : SourceNativeLivingRootClosure
    M10OccurrenceCapacityRootSourceFixture.N
    M10OccurrenceCapacityRootSourceFixture.V where
  source :=
    { base := authoritySource
      terminalHandoff := authoritySource.emptyFaithfulTerminalHandoff
        (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := M10OccurrenceCapacityRootSourceFixture.emitted
  compiler_commutes := fun _ => rfl

def visit : SourceNativeTemporalVisitAt
    root.toAuthoritativeRoot.toLedgerRoot :=
  .finite root.toAuthoritativeRoot.toRoot.initialVisit

def installation : SourceNativeProjectionLaw.InstallationAt
    renewalLaw.toProjectionLaw
    root.toAuthoritativeRoot.source.projectionLaw :=
  renewalComponent
    M10OccurrenceCapacityRootSourceFixture.baseAuthoritySource renewalLaw

def recognition : SourceNativeBoundaryMaintenanceRecognitionAt
    root maintenanceSocialSpace DebitP DebitProcess
      MaintenanceDispositionAt where
  law := renewalLaw
  installation := installation

/-- Source-installed renewal generated at the exact root visit. -/
def installedRenewal : SourceInstalledRenewalAt recognition visit :=
  SourceInstalledRenewalAt.generate PUnit.unit rfl

/-- The stronger pre-emitter projection retains the exact operational row and
budget already exercised by the M10 renewal-root fixture. -/
theorem installed_row_agrees_with_existing_M10_renewal :
    installedRenewal.operationalAuthority.operationalStanding =
        M10OccurrenceCapacityRenewalRootFixture.installedRenewal.operationalAuthority.operationalStanding ∧
      installedRenewal.operationalAuthority.operationalStanding.progressBudget =
        M10OccurrenceCapacityRenewalRootFixture.installedRenewal.operationalAuthority.operationalStanding.progressBudget :=
  ⟨rfl, rfl⟩

/-- Installed maintenance is a zero-field seal over the pre-emitter payload. -/
def maintenance : SourceInstalledBoundaryMaintenanceAt installedRenewal :=
  sourceInstalledBoundaryMaintenance installedRenewal

/-! ## Installed exact chain -/

@[simp] theorem installed_sourceSeed_eq_focal :
    installedRenewal.payload.sourceSeed = localFocalSeed :=
  rfl

@[simp] theorem installed_consumer_eq_restriction :
    installedRenewal.payload.consumer = maintenanceRestriction :=
  rfl

@[simp] theorem maintenance_certificate_eq :
    maintenance.boundaryCertificate = firstBoundaryCertificate :=
  rfl

@[simp] theorem maintenance_exactCrossing_eq :
    maintenance.exactCrossing = firstCrossing :=
  rfl

/-- The production readout consumes the exact first M10 debit event. -/
@[simp] theorem actualMaintenanceDebit_eq_firstDebit :
    maintenance.actualMaintenanceDebit =
      M10OccurrenceCapacityDebitedRunFixture.firstDebit :=
  rfl

/-- The installed native run is exactly one actual lifecycle edge. -/
@[simp] theorem maintenanceRun_events_length :
    maintenance.maintenanceRun.events.length = 1 :=
  rfl

@[simp] theorem maintained_boundaryStanding_eq_source_obligation :
    maintenance.boundaryStanding =
      M10OccurrenceCapacityDebitedRunFixture.admissionPayload.toObligation :=
  rfl

/-- Exact target liveness follows from the source-owned debit receipt. -/
theorem target_live_after_singleton_maintenance :
    maintenance.restriction.edge.target.slots[
      maintenance.actualMaintenanceDebit.slot]? =
        some (.live maintenance.boundaryStanding) :=
  maintenance.boundaryStanding_live_at_target

/-- The singleton actual debit reduces the fixed budget from two to one. -/
@[simp] theorem target_budget_eq_one :
    DebitProcess.budgetAt maintenance.restriction.edge.target
      maintenance.restriction.lineage = 1 :=
  rfl

/-- Boundary image and actual maintained standing retain one source lineage. -/
theorem maintained_standing_has_boundary_lineage : HEq
    maintenance.boundaryStanding.lineage
    (maintenanceCrossingCompiler.boundaryLineageOf LocalGame.source
      maintenance.boundarySourceSeed) :=
  maintenance.boundaryStanding_lineage_heq_boundaryLineage

/-- Independent downstream consumer of the complete installed chain. -/
def consumer : BoundaryMaintenanceConsumerAt maintenance :=
  maintenance.independentConsumer

def exactRootResponsibilityConsumer :
    RenewalResponsibilityConsumerAt
      installedRenewal.operationalAuthority :=
  consumer.rootConsumer

def exactWholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence :=
  consumer.wholeLedgerWriteBack

theorem installed_factorizes_root_answer_and_next :
    installedRenewal.RootAnswerAndNextFactorizes :=
  consumer.rootFactorization

/-- The local singleton run issues no scheduler result.  Both installed and
independent readouts return only the existing root-generated next. -/
theorem local_run_reads_only_root_generated_next :
    maintenance.generatedNext = root.generatedNextCurrentAt visit ∧
      consumer.generatedNext = root.generatedNextCurrentAt visit :=
  ⟨rfl, consumer.generatedNext_eq⟩

/-- Full independent answer-and-next seam requested by the regression. -/
theorem exact_boundary_debit_whole_root_consumer :
    consumer.certificate = firstBoundaryCertificate ∧
      consumer.exactCrossing = firstCrossing ∧
      consumer.actualDebit =
        M10OccurrenceCapacityDebitedRunFixture.firstDebit ∧
      consumer.debitedRun.length = 1 ∧
      maintenance.restriction.edge.target.slots[
        consumer.actualDebit.slot]? =
          some (.live consumer.boundaryStanding) ∧
      installedRenewal.RootAnswerAndNextFactorizes ∧
      consumer.generatedNext = root.generatedNextCurrentAt visit := by
  refine ⟨rfl, rfl, rfl, ?_, consumer.target_live,
    consumer.rootFactorization, consumer.generatedNext_eq⟩
  rfl

/-! ## Negative controls -/

/-- Same lifecycle budget, but no source-owned debit events. -/
def noDebitProcess : NativeCarryDebitProcess DebitP where
  budgetAt := M10OccurrenceCapacityDebitedRunFixture.budgetAt
  DebitEvent := fun {_source} _edge _lineage => PEmpty
  debitReceipt := by
    intro source edge lineage event
    exact nomatch event

/-- A source boundary certificate exists, yet without an actual debit event
the complete pre-emitter restriction is empty.  Thus neither a bare boundary
seed nor its certificate generates standing. -/
theorem certificate_without_debit_cannot_install_standing :
    Nonempty maintenanceCrossingCompiler.AnyBoundaryCertificate ∧
      IsEmpty (BoundaryMaintenanceRestrictionAt maintenanceSocialSpace
        DebitP noDebitProcess localFocalSeed) := by
  refine ⟨⟨firstBoundaryCertificate⟩, ⟨?_⟩⟩
  intro restriction
  exact nomatch restriction.debitEvent

/-- A negative crossing classifier over the same actual queue. -/
def inactiveCrossingCompiler : SourceOwnedCrossingCompiler.{0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0} rateCompiler where
  SiteSeed := maintenanceCrossingCompiler.SiteSeed
  SiteSeedAt := maintenanceCrossingCompiler.SiteSeedAt
  SiteLineage := maintenanceCrossingCompiler.SiteLineage
  siteLineageOf := maintenanceCrossingCompiler.siteLineageOf
  originSeedAt := maintenanceCrossingCompiler.originSeedAt
  targetSeedAt := maintenanceCrossingCompiler.targetSeedAt
  originSeedIncidence := maintenanceCrossingCompiler.originSeedIncidence
  targetSeedIncidence := maintenanceCrossingCompiler.targetSeedIncidence
  FlowPayloadAt := maintenanceCrossingCompiler.FlowPayloadAt
  flowPayloadAt := maintenanceCrossingCompiler.flowPayloadAt
  BoundarySeed := maintenanceCrossingCompiler.BoundarySeed
  BoundarySeedAt := maintenanceCrossingCompiler.BoundarySeedAt
  BoundaryLineage := maintenanceCrossingCompiler.BoundaryLineage
  boundaryLineageOf := maintenanceCrossingCompiler.boundaryLineageOf
  BoundaryActiveAt := fun _crossing => PEmpty
  BoundaryInactiveAt := fun _crossing => PUnit
  classifyBoundary := fun _crossing => .inr PUnit.unit
  boundarySeedAt := fun _crossing active => nomatch active
  boundarySeedIncidence := fun _crossing active => nomatch active

def inactiveSocialSpace :
    SourceGeneratedSocialSpaceAt inactiveCrossingCompiler :=
  SourceGeneratedSocialSpaceAt.generate inactiveCrossingCompiler

@[simp] theorem inactive_crossingTrace_eq_actual_trace :
    inactiveSocialSpace.crossingTrace = maintenanceSocialSpace.crossingTrace :=
  rfl

@[simp] theorem inactive_boundaryCertificates_eq_nil :
    inactiveSocialSpace.boundaryCertificates = [] :=
  rfl

/-- Raw queue crossings plus an exact debit do not satisfy the restriction
when the source classifier emits no exact boundary certificate. -/
theorem unclassified_crossing_cannot_pair_with_exact_debit :
    IsEmpty (BoundaryMaintenanceRestrictionAt inactiveSocialSpace
      DebitP DebitProcess localFocalSeed) := by
  refine ⟨?_⟩
  intro restriction
  exact PEmpty.elim restriction.certificate.proof.active

/-- Every inhabited restriction necessarily recovers the exact crossing,
source classifier and actual debit receipt together. -/
theorem restriction_forces_exact_crossing_debit_relation
    (restriction : BoundaryMaintenanceRestrictionAt maintenanceSocialSpace
      DebitP DebitProcess localFocalSeed) :
    restriction.certificate.crossing ∈
        maintenanceSocialSpace.crossingTrace ∧
      maintenanceCrossingCompiler.boundaryCertificate?
          restriction.certificate.crossing =
        some restriction.certificate.proof ∧
      HEq
        (maintenanceCrossingCompiler.boundaryLineageOf LocalGame.source
          restriction.certificate.sourceSeed)
        restriction.lineage ∧
      Nonempty (ActualMaintenanceDebit DebitP DebitProcess.budgetAt
        restriction.edge restriction.lineage) := by
  have provenance := maintenanceSocialSpace.boundaryCertificate_provenance
    restriction.certificate restriction.certificate_mem
  exact ⟨provenance.1, provenance.2,
    restriction.boundaryLineage_heq,
    ⟨DebitProcess.debitReceipt restriction.debitEvent⟩⟩

/-- No inhabitant of the restriction can carry a non-exact
crossing/debit relation. -/
theorem nonExact_crossing_debit_relation_is_rejected
    (restriction : BoundaryMaintenanceRestrictionAt maintenanceSocialSpace
      DebitP DebitProcess localFocalSeed)
    (nonExact : ¬ (
      restriction.certificate.crossing ∈
          maintenanceSocialSpace.crossingTrace ∧
        maintenanceCrossingCompiler.boundaryCertificate?
            restriction.certificate.crossing =
          some restriction.certificate.proof ∧
        HEq
          (maintenanceCrossingCompiler.boundaryLineageOf LocalGame.source
            restriction.certificate.sourceSeed)
          restriction.lineage ∧
        Nonempty (ActualMaintenanceDebit DebitP DebitProcess.budgetAt
          restriction.edge restriction.lineage))) :
    False :=
  nonExact (restriction_forces_exact_crossing_debit_relation restriction)

end
end M11BoundaryMaintenanceRegression
end Society
end ProcessGame
end SaturationMonoid
