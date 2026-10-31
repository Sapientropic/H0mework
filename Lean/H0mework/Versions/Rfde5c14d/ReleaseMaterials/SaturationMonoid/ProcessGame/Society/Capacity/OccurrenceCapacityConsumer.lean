import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityPhase
import H0mework.Foundation.Responsibility.ResponsibilityCapacityKernel

/-!
# Consumers of the generated occurrence-capacity phase

The phase authority remains a readout of one exact queue prefix and one
installed renewal row.  This module supplies two independent consumers:

* a root consumer retaining the renewal responsibility, whole-ledger
  write-back, and generated next current;
* an actual-debit consumer which aligns the exact queue with an existing
  `NativeDebitedRun` and turns critical/anomie into budget consequences.

No run, budget, phase, or target state is used to construct phase authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Capacity

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Renewal

universe u uLineage uUnit

variable {LocalSource LocalState Seed : Type u}
variable {occurrenceOf : LocalSource → RootedAccountedUnfolding LocalState}
variable {game : SaturationMonoid.ProcessGame occurrenceOf}
variable {SeedAt : LocalSource → LocalState → Seed → Prop}
variable {Lineage : LocalSource → Type uLineage}
variable {lineageOf : ∀ source,
  SourceSeed occurrenceOf Seed SeedAt source → Lineage source}

variable {N : WorldRelationNetwork.{u}}
variable {RootV : ConstructiveRoot.Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N RootV}
variable {ConsumerAt DispositionAt :
  SourceSeed occurrenceOf Seed SeedAt game.source → Type u}
variable {recognition : SourceNativeRenewalRecognitionAt root game Seed SeedAt
  ConsumerAt DispositionAt}
variable {visit : SourceNativeTemporalVisitAt
  root.toAuthoritativeRoot.toLedgerRoot}
variable {installed : SourceInstalledRenewalAt recognition visit}

variable {compiler : SourceOwnedOccurrenceRateCompiler.{u, u, u,
  uLineage, uUnit} game Seed SeedAt Lineage lineageOf
    installed.payload.sourceSeed}
variable {exactPrefix : SourceGeneratedExactQueuePrefixAt compiler}
variable {phase : SourceGeneratedOccurrenceCapacityPhaseAt
  installed compiler exactPrefix}

/-! ## Root/whole-ledger consumer -/

/-- Independent root consumer of one generated phase.  Every field is a
readout of the phase indices or the existing M8 installed renewal. -/
structure OccurrenceCapacityPhaseConsumerAt
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix) :
    Type (max (u + 4) (max (uLineage + 1) (uUnit + 2))) where
  private mk ::
  focalSeed : SourceSeed occurrenceOf Seed SeedAt game.source
  focalSeed_eq : focalSeed = installed.payload.sourceSeed
  exactQueuePrefix : SourceGeneratedExactQueuePrefixAt compiler
  exactQueuePrefix_eq : exactQueuePrefix = exactPrefix
  phaseTag : OccurrenceCapacityPhaseTag
  phaseTag_eq : phaseTag = phase.phaseTag
  rootConsumer : RenewalResponsibilityConsumerAt installed.operationalAuthority
  wholeLedgerWriteBack :
    SourceNativeLedgerEvolutionAt
      root.toAuthoritativeRoot.toLedgerRoot.source.source
      (root.toAuthoritativeRoot.toLedgerRoot
        |>.generatedAtTemporalVisit visit).occurrence
  generatedNext : SourceNativeAuthoritativeRootCurrentAt N
  generatedNext_eq : generatedNext = root.generatedNextCurrentAt visit
  rootFactorization : installed.RootAnswerAndNextFactorizes

/-- Generate the independent root consumer from the exact phase authority. -/
def SourceGeneratedOccurrenceCapacityPhaseAt.independentRootConsumer
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix) :
    OccurrenceCapacityPhaseConsumerAt phase where
  focalSeed := phase.focalSeed
  focalSeed_eq := phase.focalSeed_eq_installedSeed
  exactQueuePrefix := exactPrefix
  exactQueuePrefix_eq := rfl
  phaseTag := phase.phaseTag
  phaseTag_eq := rfl
  rootConsumer := installed.rootResponsibilityConsumer
  wholeLedgerWriteBack :=
    (root.toAuthoritativeRoot.toLedgerRoot
      |>.generatedAtTemporalVisit visit).wholeLedgerWriteBack
  generatedNext := root.generatedNextCurrentAt visit
  generatedNext_eq := rfl
  rootFactorization := installed.rootAnswerAndNext_factorizes

/-! ## Backlog provenance -/

/-- Every unit of an exact phase prefix remains a member of the sole
compiler-owned queue. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.queuePrefix_mem_queue
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (unit : compiler.QueueUnit)
    (unit_mem_prefix : unit ∈ phase.queuePrefix) : unit ∈ compiler.queue := by
  have unit_mem_exact : unit ∈ exactPrefix.units := by
    simpa only [phase.queuePrefix_eq_prefixUnits] using unit_mem_prefix
  rw [← exactPrefix.units_append_suffix]
  exact List.mem_append_left _ unit_mem_exact

/-- Every backlog unit remains a member of the sole compiler-owned queue. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.backlog_mem_queue
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (unit : compiler.QueueUnit)
    (unit_mem : unit ∈ phase.backlog) : unit ∈ compiler.queue := by
  apply phase.queuePrefix_mem_queue
  rw [← phase.served_append_backlog]
  exact List.mem_append_right _ unit_mem

/-- Upgrade a backlog member to its exact trace-position occurrence. -/
def SourceGeneratedOccurrenceCapacityPhaseAt.exactBacklogUnit
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (unit : compiler.QueueUnit)
    (unit_mem : unit ∈ phase.backlog) : compiler.ExactQueueUnit :=
  ⟨unit, phase.backlog_mem_queue unit unit_mem⟩

/-- Backlog never erases source provenance or focal lineage. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.backlog_lineage_eq_focal
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (unit : compiler.QueueUnit)
    (unit_mem : unit ∈ phase.backlog) :
    (phase.exactBacklogUnit unit unit_mem).lineage compiler =
      lineageOf game.source installed.payload.sourceSeed :=
  (phase.exactBacklogUnit unit unit_mem).lineage_eq_focal compiler

/-! ## Actual debit alignment and phase consequences -/

variable {RunV : ResponsibilityLifecycle.Vocabulary.{u}}
variable {P : NativeResponsibilityProcess RunV}
variable {B : NativeCarryDebitProcess P}
variable {runLineage : RunV.Lineage}
variable {sourceState targetState : ResponsibilityState RunV}
variable {run : P.Run sourceState targetState}

/-- Existing actual lifecycle run aligned with this exact queue prefix and
installed row capacity.  The run and both equalities are downstream
provenance; none participates in phase generation. -/
structure ExactOccurrenceCapacityDebitedRunAt
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (debited : NativeDebitedRun P B runLineage run) : Prop where
  sourceBudget_eq_capacity :
    B.budgetAt sourceState runLineage = phase.capacity
  eventsLength_eq_rate : run.events.length = phase.rate

/-- Exact event count equals exact queue-prefix length. -/
theorem ExactOccurrenceCapacityDebitedRunAt.eventsLength_eq_prefixLength
    {debited : NativeDebitedRun P B runLineage run}
    (aligned : ExactOccurrenceCapacityDebitedRunAt phase debited) :
    run.events.length = phase.queuePrefix.length :=
  aligned.eventsLength_eq_rate.trans rfl

/-! ### Ordered eventwise service provenance -/

/-- Existing source law relating one generated arrival unit to one actual
lifecycle service event.  It supplies only a receipt family; phase authority,
queue order and run order are fixed independently. -/
structure SourceOwnedOccurrenceServiceCompiler
    (compiler : SourceOwnedOccurrenceRateCompiler.{u, u, u,
      uLineage, uUnit} game Seed SeedAt Lineage lineageOf
        installed.payload.sourceSeed)
    (P : NativeResponsibilityProcess RunV) :
    Type (max (u + 2) (uUnit + 1)) where
  ServesAt : compiler.QueueUnit → LifecycleEvent RunV → Type u

/-- Provenance-strengthened alignment.  The numeric alignment is retained,
and the `i`th exact queue unit is tied to the `i`th actual lifecycle event by
one source-owned service receipt. -/
structure ExactProvenanceOccurrenceCapacityDebitedRunAt
    (phase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler exactPrefix)
    (debited : NativeDebitedRun P B runLineage run)
    (service : SourceOwnedOccurrenceServiceCompiler compiler P) :
    Type (max (u + 4) (max (uLineage + 1) (uUnit + 2))) where
  numeric : ExactOccurrenceCapacityDebitedRunAt phase debited
  serviceAt : (index : Fin phase.queuePrefix.length) →
    service.ServesAt
      (phase.queuePrefix.get index)
      (run.events.get
        (Fin.cast numeric.eventsLength_eq_prefixLength.symm index))

namespace ExactProvenanceOccurrenceCapacityDebitedRunAt

variable {debited : NativeDebitedRun P B runLineage run}
variable {service : SourceOwnedOccurrenceServiceCompiler compiler P}
variable (provenance :
  ExactProvenanceOccurrenceCapacityDebitedRunAt phase debited service)

/-- Queue occurrence at one serviced position, with exact source provenance. -/
def exactQueueUnitAt
    (_provenance :
      ExactProvenanceOccurrenceCapacityDebitedRunAt phase debited service)
    (index : Fin phase.queuePrefix.length) : compiler.ExactQueueUnit :=
  ⟨phase.queuePrefix.get index,
    phase.queuePrefix_mem_queue _ (List.get_mem _ index)⟩

/-- The serviced queue occurrence still carries the focal source lineage. -/
theorem serviced_lineage_eq_focal
    (index : Fin phase.queuePrefix.length) :
    (provenance.exactQueueUnitAt index).lineage compiler =
      lineageOf game.source installed.payload.sourceSeed :=
  (provenance.exactQueueUnitAt index).lineage_eq_focal compiler

/-- Exact ordered service receipt at one queue/run position. -/
def serviceReceiptAt
    (index : Fin phase.queuePrefix.length) :
    service.ServesAt
      (phase.queuePrefix.get index)
      (run.events.get
        (Fin.cast provenance.numeric.eventsLength_eq_prefixLength.symm index)) :=
  provenance.serviceAt index

/-- Critical eventwise service inherits the numeric exhaustion theorem. -/
theorem critical_targetBudget_eq_zero
    (provenance :
      ExactProvenanceOccurrenceCapacityDebitedRunAt phase debited service)
    (critical : phase.phaseTag = .critical) :
    B.budgetAt targetState runLineage = 0 := by
  apply NativeDebitedRun.targetBudget_eq_zero_of_events_length_eq_sourceBudget
    debited
  calc
    run.events.length = phase.rate :=
      provenance.numeric.eventsLength_eq_rate
    _ = phase.capacity := phase.phaseTag_eq_critical_iff.mp critical
    _ = B.budgetAt sourceState runLineage :=
      provenance.numeric.sourceBudget_eq_capacity.symm

end ExactProvenanceOccurrenceCapacityDebitedRunAt

namespace ExactOccurrenceCapacityDebitedRunAt

variable {debited : NativeDebitedRun P B runLineage run}

/-- A critical exact full run spends the installed capacity and therefore
reaches target budget zero. -/
theorem critical_targetBudget_eq_zero
    (aligned : ExactOccurrenceCapacityDebitedRunAt phase debited)
    (critical : phase.phaseTag = .critical) :
    B.budgetAt targetState runLineage = 0 := by
  apply NativeDebitedRun.targetBudget_eq_zero_of_events_length_eq_sourceBudget
    debited
  calc
    run.events.length = phase.rate := aligned.eventsLength_eq_rate
    _ = phase.capacity := phase.phaseTag_eq_critical_iff.mp critical
    _ = B.budgetAt sourceState runLineage :=
      aligned.sourceBudget_eq_capacity.symm

/-- An anomie prefix cannot already be a completely debited actual run: its
arrival count strictly exceeds the aligned source-owned capacity. -/
theorem anomie_false
    (aligned : ExactOccurrenceCapacityDebitedRunAt phase debited)
    (anomie : phase.phaseTag = .anomie) : False := by
  apply NativeDebitedRun.no_more_events_than_sourceBudget debited
  calc
    B.budgetAt sourceState runLineage = phase.capacity :=
      aligned.sourceBudget_eq_capacity
    _ < phase.rate := phase.phaseTag_eq_anomie_iff.mp anomie
    _ = run.events.length := aligned.eventsLength_eq_rate.symm

end ExactOccurrenceCapacityDebitedRunAt

/-- Structural no-go: no actual debited run can cover an anomie prefix under
the exact installed-capacity alignment. -/
theorem anomie_forbids_full_debited_consumption
    (anomie : phase.phaseTag = .anomie)
    (debited : NativeDebitedRun P B runLineage run) :
    IsEmpty (ExactOccurrenceCapacityDebitedRunAt phase debited) :=
  ⟨fun aligned => ExactOccurrenceCapacityDebitedRunAt.anomie_false
    aligned anomie⟩

/-- Strong run-level form: once an actual run claims both the exact installed
source capacity and the complete anomie arrival count, no source-owned debit
certification of that run can exist. -/
theorem anomie_forbids_full_debited_run
    (anomie : phase.phaseTag = .anomie)
    (sourceBudget_eq_capacity :
      B.budgetAt sourceState runLineage = phase.capacity)
    (eventsLength_eq_rate : run.events.length = phase.rate) :
    IsEmpty (NativeDebitedRun P B runLineage run) :=
  ⟨fun debited =>
    (anomie_forbids_full_debited_consumption anomie debited).false
      ⟨sourceBudget_eq_capacity, eventsLength_eq_rate⟩⟩

end Capacity
end Society
end ProcessGame
end SaturationMonoid
