import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityProcess
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.Fixture.OccurrenceCapacityRenewalRoot
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityConsumer

/-!
# M10 occurrence-capacity phase regression

One installed renewal and one source-owned position-indexed rate compiler
generate exact cuts one, two, and three.  The resulting phase authorities are
stable, critical, and anomie respectively.  Capacity remains the installed
operational standing's progress budget `2`; no rate, capacity, queue, or phase
tag is supplied to a producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityPhaseRegression

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal Capacity
open M10OccurrenceCapacityProcessFixture
open M10OccurrenceCapacityRenewalRootFixture

/-! Freeze the fixture compiler's otherwise-polymorphic trivial unit
universe so every dependent certificate field names one literal compiler. -/
abbrev phaseCompiler : SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    game Seed seedAt Lineage lineageOf installedRenewal.payload.sourceSeed := by
  change SourceOwnedOccurrenceRateCompiler.{0, 0, 0, 0, 0}
    game Seed seedAt Lineage lineageOf focalSeed
  exact M10OccurrenceCapacityProcessFixture.compiler

@[simp] theorem phaseCompiler_queue_eq :
    phaseCompiler.queue = [firstUnit, middleUnit, recurrentUnit] := by
  change M10OccurrenceCapacityProcessFixture.compiler.queue =
    [firstUnit, middleUnit, recurrentUnit]
  exact compiled_queue_eq

/-! ## Exact source-bounded cuts and phases -/

def cutOne : SourceGeneratedExactQueuePrefixAt
    (installed := installedRenewal) phaseCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate
    (installed := installedRenewal) phaseCompiler
    ⟨1, by rw [phaseCompiler_queue_eq]; decide⟩

def cutTwo : SourceGeneratedExactQueuePrefixAt
    (installed := installedRenewal) phaseCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate
    (installed := installedRenewal) phaseCompiler
    ⟨2, by rw [phaseCompiler_queue_eq]; decide⟩

def cutThree : SourceGeneratedExactQueuePrefixAt
    (installed := installedRenewal) phaseCompiler :=
  SourceGeneratedExactQueuePrefixAt.generate
    (installed := installedRenewal) phaseCompiler
    ⟨3, by rw [phaseCompiler_queue_eq]; decide⟩

def stablePhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutOne :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedRenewal phaseCompiler cutOne

def criticalPhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutTwo :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedRenewal phaseCompiler cutTwo

def anomiePhase : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutThree :=
  SourceGeneratedOccurrenceCapacityPhaseAt.generate
    installedRenewal phaseCompiler cutThree

@[simp] theorem cutOne_units :
    cutOne.units = [firstUnit] :=
  queue_take_one

@[simp] theorem cutTwo_units :
    cutTwo.units = [firstUnit, middleUnit] :=
  queue_take_two

@[simp] theorem cutThree_units :
    cutThree.units = [firstUnit, middleUnit, recurrentUnit] :=
  queue_take_three

@[simp] theorem stable_rate_eq_one : stablePhase.rate = 1 :=
  rfl

@[simp] theorem critical_rate_eq_two : criticalPhase.rate = 2 :=
  rfl

@[simp] theorem anomie_rate_eq_three : anomiePhase.rate = 3 :=
  rfl

@[simp] theorem stable_capacity_eq_two : stablePhase.capacity = 2 :=
  rfl

@[simp] theorem critical_capacity_eq_two : criticalPhase.capacity = 2 :=
  rfl

@[simp] theorem anomie_capacity_eq_two : anomiePhase.capacity = 2 :=
  rfl

@[simp] theorem stable_phase_exact : stablePhase.phaseTag = .stable := by
  exact stablePhase.phaseTag_eq_stable_iff.mpr (by decide)

@[simp] theorem critical_phase_exact : criticalPhase.phaseTag = .critical := by
  exact criticalPhase.phaseTag_eq_critical_iff.mpr rfl

@[simp] theorem anomie_phase_exact : anomiePhase.phaseTag = .anomie := by
  exact anomiePhase.phaseTag_eq_anomie_iff.mpr (by decide)

@[simp] theorem stable_spare_eq_one : stablePhase.spare = 1 :=
  rfl

@[simp] theorem stable_backlog_eq_nil : stablePhase.backlog = [] :=
  stablePhase.stable_backlog_eq_nil stable_phase_exact

@[simp] theorem critical_spare_eq_zero : criticalPhase.spare = 0 :=
  criticalPhase.critical_spare_eq_zero critical_phase_exact

@[simp] theorem critical_backlog_eq_nil : criticalPhase.backlog = [] :=
  criticalPhase.critical_backlog_eq_nil critical_phase_exact

@[simp] theorem anomie_backlog_eq_recurrent :
    anomiePhase.backlog = [recurrentUnit] :=
  rfl

@[simp] theorem anomie_backlog_length_eq_one :
    anomiePhase.backlog.length = 1 :=
  rfl

theorem anomie_backlog_length_eq_rate_sub_capacity :
    anomiePhase.backlog.length =
      anomiePhase.rate - anomiePhase.capacity :=
  anomiePhase.anomie_backlog_length anomie_phase_exact

theorem exactCutsOneTwoThree_generate_threePhases :
    stablePhase.phaseTag = .stable ∧
      criticalPhase.phaseTag = .critical ∧
        anomiePhase.phaseTag = .anomie :=
  ⟨stable_phase_exact, critical_phase_exact, anomie_phase_exact⟩

/-! ## Exact recurrent occurrence retained in backlog -/

theorem recurrentUnit_mem_anomieBacklog :
    recurrentUnit ∈ anomiePhase.backlog := by
  simp

def recurrentBacklogOccurrence : phaseCompiler.ExactQueueUnit :=
  anomiePhase.exactBacklogUnit recurrentUnit
    recurrentUnit_mem_anomieBacklog

@[simp] theorem recurrentBacklogOccurrence_position :
    recurrentBacklogOccurrence.position = recurrentPosition :=
  rfl

@[simp] theorem recurrentBacklogOccurrence_state :
    recurrentBacklogOccurrence.state = false :=
  rfl

@[simp] theorem recurrentBacklogOccurrence_sourceSeed :
    recurrentBacklogOccurrence.sourceSeed phaseCompiler = focalSeed := by
  apply Subtype.ext
  rfl

theorem recurrentBacklogOccurrence_lineage_is_focal :
    recurrentBacklogOccurrence.lineage phaseCompiler =
      lineageOf game.source installedRenewal.payload.sourceSeed :=
  anomiePhase.backlog_lineage_eq_focal recurrentUnit
    recurrentUnit_mem_anomieBacklog

/-! ## Same-source phase generation and negative controls -/

theorem installedCapacity_pos :
    0 < operationalCapacity (game := game) installedRenewal :=
  by decide

theorem installedCapacity_lt_queueLength :
    operationalCapacity (game := game) installedRenewal <
      phaseCompiler.queue.length :=
  by decide

theorem sameInstalledSource_generates_threePhases :
    (emptyPrefixPhase installedRenewal phaseCompiler).phaseTag = .stable ∧
      (capacityPrefixPhase
        (installed := installedRenewal) (compiler := phaseCompiler)
        installedCapacity_lt_queueLength.le).phaseTag = .critical ∧
      (excessPrefixPhase
        (installed := installedRenewal) (compiler := phaseCompiler)
        installedCapacity_lt_queueLength).phaseTag = .anomie :=
  sameSource_generates_threePhases
    (installed := installedRenewal) (compiler := phaseCompiler)
    installedCapacity_pos installedCapacity_lt_queueLength

/-- Reordering phaseCompiler units cannot be wrapped as an exact prefix seal. -/
theorem reordered_pair_is_not_exact_prefix
    (candidate : SourceGeneratedExactQueuePrefixAt
      (installed := installedRenewal) phaseCompiler) :
    candidate.units ≠ [middleUnit, firstUnit] := by
  intro reordered
  have cut_eq : candidate.cut = 2 := by
    rw [← candidate.units_length, reordered]
    rfl
  rw [candidate.units_eq_take, cut_eq] at reordered
  change [firstUnit, middleUnit] = [middleUnit, firstUnit] at reordered
  have exact_order : [firstUnit, middleUnit] = [middleUnit, firstUnit] :=
    reordered
  have first_eq_middle : firstUnit = middleUnit := by
    exact List.cons.inj exact_order |>.1
  exact first_middle_positions_are_distinct
    (congrArg Sigma.fst first_eq_middle)

/-- The recurrent visit remains distinct even though it stores the same state
and seed as the first occurrence. -/
theorem recurrent_trace_positions_remain_distinct :
    firstUnit ≠ recurrentUnit :=
  recurrent_units_are_distinct

/-- No constant phase oracle can reproduce the three exact generated tags. -/
theorem no_constant_phase_oracle
    (tag : OccurrenceCapacityPhaseTag) :
    ¬(stablePhase.phaseTag = tag ∧
      criticalPhase.phaseTag = tag ∧
      anomiePhase.phaseTag = tag) := by
  intro constant
  have stable_eq_critical :
      stablePhase.phaseTag = criticalPhase.phaseTag :=
    constant.1.trans constant.2.1.symm
  rw [stable_phase_exact, critical_phase_exact] at stable_eq_critical
  cases stable_eq_critical

/-! ## Independent root consumers -/

def stableRootConsumer : OccurrenceCapacityPhaseConsumerAt stablePhase :=
  stablePhase.independentRootConsumer

def criticalRootConsumer : OccurrenceCapacityPhaseConsumerAt criticalPhase :=
  criticalPhase.independentRootConsumer

def anomieRootConsumer : OccurrenceCapacityPhaseConsumerAt anomiePhase :=
  anomiePhase.independentRootConsumer

@[simp] theorem stableRootConsumer_renewal_exact :
    stableRootConsumer.rootConsumer = responsibilityConsumer :=
  rfl

@[simp] theorem criticalRootConsumer_renewal_exact :
    criticalRootConsumer.rootConsumer = responsibilityConsumer :=
  rfl

@[simp] theorem anomieRootConsumer_renewal_exact :
    anomieRootConsumer.rootConsumer = responsibilityConsumer :=
  rfl

@[simp] theorem stableRootConsumer_wholeLedger_exact :
    stableRootConsumer.wholeLedgerWriteBack =
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack :=
  rfl

@[simp] theorem criticalRootConsumer_wholeLedger_exact :
    criticalRootConsumer.wholeLedgerWriteBack =
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack :=
  rfl

@[simp] theorem anomieRootConsumer_wholeLedger_exact :
    anomieRootConsumer.wholeLedgerWriteBack =
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack :=
  rfl

@[simp] theorem stableRootConsumer_next_exact :
    stableRootConsumer.generatedNext = root.generatedNextCurrentAt visit :=
  rfl

@[simp] theorem criticalRootConsumer_next_exact :
    criticalRootConsumer.generatedNext = root.generatedNextCurrentAt visit :=
  rfl

@[simp] theorem anomieRootConsumer_next_exact :
    anomieRootConsumer.generatedNext = root.generatedNextCurrentAt visit :=
  rfl

/-! ## Independent certificate -/

structure OccurrenceCapacityPhaseCertificate : Type 6 where
  stable : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutOne
  critical : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutTwo
  anomie : SourceGeneratedOccurrenceCapacityPhaseAt
    installedRenewal phaseCompiler cutThree
  stableConsumer : OccurrenceCapacityPhaseConsumerAt stable
  criticalConsumer : OccurrenceCapacityPhaseConsumerAt critical
  anomieConsumer : OccurrenceCapacityPhaseConsumerAt anomie
  stableRate : stable.rate = 1
  criticalRate : critical.rate = 2
  anomieRate : anomie.rate = 3
  stableCapacity : stable.capacity = 2
  criticalCapacity : critical.capacity = 2
  anomieCapacity : anomie.capacity = 2
  stableTag : stable.phaseTag = .stable
  criticalTag : critical.phaseTag = .critical
  anomieTag : anomie.phaseTag = .anomie
  stableSpare : stable.spare = 1
  criticalSpare : critical.spare = 0
  stableBacklog : stable.backlog = []
  criticalBacklog : critical.backlog = []
  anomieBacklog : anomie.backlog = [recurrentUnit]
  recurrentBacklogMembership : recurrentUnit ∈ anomie.backlog
  recurrentPositionExact :
    (anomie.exactBacklogUnit recurrentUnit recurrentBacklogMembership).position =
      recurrentPosition
  recurrentSourceSeedExact :
    SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.sourceSeed phaseCompiler
      (anomie.exactBacklogUnit recurrentUnit recurrentBacklogMembership) =
        focalSeed
  recurrentLineageExact :
    SourceOwnedOccurrenceRateCompiler.ExactQueueUnit.lineage phaseCompiler
      (anomie.exactBacklogUnit recurrentUnit recurrentBacklogMembership) =
        lineageOf game.source installedRenewal.payload.sourceSeed
  rootFactorization : installedRenewal.RootAnswerAndNextFactorizes

def occurrenceCapacityPhaseDirectConsumer :
    OccurrenceCapacityPhaseCertificate where
  stable := stablePhase
  critical := criticalPhase
  anomie := anomiePhase
  stableConsumer := stableRootConsumer
  criticalConsumer := criticalRootConsumer
  anomieConsumer := anomieRootConsumer
  stableRate := stable_rate_eq_one
  criticalRate := critical_rate_eq_two
  anomieRate := anomie_rate_eq_three
  stableCapacity := stable_capacity_eq_two
  criticalCapacity := critical_capacity_eq_two
  anomieCapacity := anomie_capacity_eq_two
  stableTag := stable_phase_exact
  criticalTag := critical_phase_exact
  anomieTag := anomie_phase_exact
  stableSpare := stable_spare_eq_one
  criticalSpare := critical_spare_eq_zero
  stableBacklog := stable_backlog_eq_nil
  criticalBacklog := critical_backlog_eq_nil
  anomieBacklog := anomie_backlog_eq_recurrent
  recurrentBacklogMembership := recurrentUnit_mem_anomieBacklog
  recurrentPositionExact := rfl
  recurrentSourceSeedExact := recurrentBacklogOccurrence_sourceSeed
  recurrentLineageExact := recurrentBacklogOccurrence_lineage_is_focal
  rootFactorization := installedRenewal_factorizes_root_answer_and_next

end
end M10OccurrenceCapacityPhaseRegression
end Society
end ProcessGame
end SaturationMonoid
