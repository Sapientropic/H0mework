import H0mework.Society.Renewal.InstalledRenewalProjection
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityProcess
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessRelationFixture

/-!
# M14 root-independent essential-service restoration

The fixed occurrence compiler's one-unit source prefix contains tenure but
not the compiler-generated health unit.  This fixture turns that exact source
fact into a local maintenance restriction and a type-indexed action restoring
the health seed at `middleUnit`.

No living root, temporal occurrence, ledger row, target prefix, portfolio,
capacity, next current, repair, or U8 authority appears in the local payload.
A later root may install the law only by supplying its own existing generic
renewal shell.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceEssentialServiceRestoration

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations Renewal Capacity
open M10OccurrenceCapacityProcessFixture
open M14EssentialAccessRelationFixture

abbrev LocalGame := M10OccurrenceCapacityProcessFixture.game
abbrev LocalSeed := M10OccurrenceCapacityProcessFixture.Seed
abbrev LocalSeedAt := M10OccurrenceCapacityProcessFixture.seedAt

/-! Freeze the fixture compiler's otherwise-polymorphic unit universe. -/
abbrev serviceQueueCompiler : SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    LocalGame LocalSeed LocalSeedAt
      M10OccurrenceCapacityProcessFixture.Lineage
      M10OccurrenceCapacityProcessFixture.lineageOf focalSeed :=
  M10OccurrenceCapacityProcessFixture.compiler

abbrev EssentialDomainSeed :=
  essentialAccessRelationCompiler.ExactRelationSeed

/-! ## Compiler-owned domain/unit assignment -/

/-- The service occurrence assigned to a relation event is computed by the
existing occurrence compiler.  The function returns a queue occurrence, not
a served slot or a success verdict. -/
def essentialServiceUnitOfEvent :
    EssentialAccessEvent → serviceQueueCompiler.QueueUnit
  | .tenure => firstUnit
  | .health => middleUnit
  | .platform => recurrentUnit

def healthDomainSeed : EssentialDomainSeed :=
  exactEssentialAccessSeed .health

def healthServiceUnit : serviceQueueCompiler.QueueUnit :=
  essentialServiceUnitOfEvent .health

/-- Exact source units visible before the maintenance action.  This list is a
readout of the sole compiler queue, never a producer input. -/
def maintenanceSourceUnits : List serviceQueueCompiler.QueueUnit :=
  serviceQueueCompiler.queue.take 1

@[simp] theorem maintenanceSourceUnits_eq_first :
    maintenanceSourceUnits = [firstUnit] :=
  rfl

theorem tenureServiceUnit_mem_maintenanceSource :
    essentialServiceUnitOfEvent .tenure ∈ maintenanceSourceUnits := by
  simp [essentialServiceUnitOfEvent, maintenanceSourceUnits]

theorem firstUnit_ne_healthServiceUnit : firstUnit ≠ healthServiceUnit := by
  exact SourceOwnedOccurrenceRateCompiler.QueueUnit.ne_of_position_ne
    serviceQueueCompiler first_middle_positions_are_distinct

theorem healthServiceUnit_not_mem_maintenanceSource :
    healthServiceUnit ∉ maintenanceSourceUnits := by
  simpa [healthServiceUnit, essentialServiceUnitOfEvent,
    maintenanceSourceUnits] using firstUnit_ne_healthServiceUnit.symm

theorem tenure_health_domainSeeds_ne :
    exactEssentialAccessSeed .tenure ≠ healthDomainSeed := by
  intro equality
  have events := congrArg Subtype.val equality
  cases events

/-! ## Source restriction and applied action -/

/-- Exact source-side maintenance cause at the recurrent focal seed. -/
structure SourceEssentialServiceMaintenanceRestrictionAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) : Type where
  private mk ::
  seed_eq : seed = focalSeed
  healthInterest : essentialAccessRelationCompiler.GeneratedInterestAt
    healthActor healthRelation
  healthPhase : essentialAccessRelationCompiler.phaseStep healthRelation =
    EssentialAccessSector.health
  healthTargetRole : essentialAccessRelationCompiler.RelationRoleAt
    healthActor healthRelation .target EssentialAccessRole.healthProvider
  tenureUnitPresent :
    essentialServiceUnitOfEvent .tenure ∈ maintenanceSourceUnits
  healthUnitMissing : healthServiceUnit ∉ maintenanceSourceUnits

def sourceEssentialServiceMaintenanceRestriction :
    SourceEssentialServiceMaintenanceRestrictionAt focalSeed where
  seed_eq := rfl
  healthInterest := M14EssentialAccessRelationFixture.healthInterest
  healthPhase := health_phase_is_generated
  healthTargetRole := ⟨M14EssentialAccessRelationFixture.healthInterest, rfl⟩
  tenureUnitPresent := tenureServiceUnit_mem_maintenanceSource
  healthUnitMissing := healthServiceUnit_not_mem_maintenanceSource

/-- The applied action is indexed by the exact health relation seed and exact
compiler queue occurrence it must restore. -/
structure SourceAppliedEssentialServiceRestorationAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source)
    (domain : EssentialDomainSeed)
    (unit : serviceQueueCompiler.QueueUnit) : Type where
  private mk ::
  seed_eq : seed = focalSeed
  domain_eq : domain = healthDomainSeed
  unit_eq : unit = healthServiceUnit
  sourceCause : SourceEssentialServiceMaintenanceRestrictionAt seed

abbrev ExactSourceAppliedEssentialServiceRestorationAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  SourceAppliedEssentialServiceRestorationAt seed healthDomainSeed
    healthServiceUnit

def sourceGeneratedHealthServiceRestoration :
    ExactSourceAppliedEssentialServiceRestorationAt focalSeed where
  seed_eq := rfl
  domain_eq := rfl
  unit_eq := rfl
  sourceCause := sourceEssentialServiceMaintenanceRestriction

namespace SourceAppliedEssentialServiceRestorationAt

/-- Exact domain readout from the action's type index. -/
def domainAt
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    {domain : EssentialDomainSeed} {unit : serviceQueueCompiler.QueueUnit}
    (_action : SourceAppliedEssentialServiceRestorationAt seed domain unit) :
    EssentialDomainSeed :=
  domain

/-- Exact queue occurrence readout from the action's type index. -/
def unitAt
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    {domain : EssentialDomainSeed} {unit : serviceQueueCompiler.QueueUnit}
    (_action : SourceAppliedEssentialServiceRestorationAt seed domain unit) :
    serviceQueueCompiler.QueueUnit :=
  unit

/-- Minimum prefix length that contains the indexed queue occurrence.  This is
a downstream calculation, not a field accepted by the action producer. -/
def requiredCut
    {seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source}
    {domain : EssentialDomainSeed} {unit : serviceQueueCompiler.QueueUnit}
    (_action : SourceAppliedEssentialServiceRestorationAt seed domain unit) :
    Nat :=
  unit.position.val + 1

@[simp] theorem exact_requiredCut_eq_two :
    requiredCut sourceGeneratedHealthServiceRestoration = 2 :=
  rfl

end SourceAppliedEssentialServiceRestorationAt

/-! ## Exact-index negative controls -/

instance tenureDomainRestoration_isEmpty : IsEmpty
    (SourceAppliedEssentialServiceRestorationAt focalSeed
      (exactEssentialAccessSeed .tenure) healthServiceUnit) :=
  ⟨fun action => tenure_health_domainSeeds_ne action.domain_eq⟩

instance firstUnitRestoration_isEmpty : IsEmpty
    (SourceAppliedEssentialServiceRestorationAt focalSeed
      healthDomainSeed firstUnit) :=
  ⟨fun action => firstUnit_ne_healthServiceUnit action.unit_eq⟩

/-! ## Root-polymorphic law mouth -/

abbrev EssentialServiceMaintenanceConsumerAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  SourceEssentialServiceMaintenanceRestrictionAt seed

abbrev EssentialServiceRestorationDispositionAt
    (seed : SourceSeed M10OccurrenceCapacityProcessFixture.occurrenceOf
      LocalSeed LocalSeedAt LocalGame.source) :=
  ExactSourceAppliedEssentialServiceRestorationAt seed

abbrev SourceEssentialServiceRestorationLawAt
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    (source : SourceNativeLedgerSource N RootV) :=
  SourceNativeRenewalProjectionLaw source LocalGame LocalSeed LocalSeedAt
    EssentialServiceMaintenanceConsumerAt
    EssentialServiceRestorationDispositionAt

/-- Assemble the exact local service action with a later root's existing
entry/row/successor shell. -/
def sourceEssentialServiceRestorationLaw
    {N : WorldRelationNetwork}
    {RootV : ConstructiveRoot.Vocabulary}
    {source : SourceNativeLedgerSource N RootV}
    (shell : SourceNativeRenewalRootShellAt source) :
    SourceEssentialServiceRestorationLawAt source :=
  SourceNativeRenewalProjectionLaw.ofRootShell shell focalSeed
    sourceEssentialServiceMaintenanceRestriction
    sourceGeneratedHealthServiceRestoration

/-! ## Mouth-level no-forgery controls -/

theorem noMaintenanceCause_noRestoration
    (noCause : IsEmpty
      (SourceEssentialServiceMaintenanceRestrictionAt focalSeed)) :
    IsEmpty (ExactSourceAppliedEssentialServiceRestorationAt focalSeed) :=
  ⟨fun action => noCause.false action.sourceCause⟩

theorem maintenance_action_has_no_target_future_fields : True := by
  fail_if_success exact sourceGeneratedHealthServiceRestoration.targetPrefix
  fail_if_success exact sourceGeneratedHealthServiceRestoration.portfolio
  fail_if_success exact sourceGeneratedHealthServiceRestoration.capacity
  fail_if_success exact sourceGeneratedHealthServiceRestoration.nextCurrent
  fail_if_success exact sourceGeneratedHealthServiceRestoration.repair
  fail_if_success exact sourceGeneratedHealthServiceRestoration.u8Core
  trivial

end
end M14SourceEssentialServiceRestoration
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialServiceRestoration.sourceEssentialServiceMaintenanceRestriction
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialServiceRestoration.sourceGeneratedHealthServiceRestoration
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialServiceRestoration.sourceEssentialServiceRestorationLaw
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceEssentialServiceRestoration.noMaintenanceCause_noRestoration
