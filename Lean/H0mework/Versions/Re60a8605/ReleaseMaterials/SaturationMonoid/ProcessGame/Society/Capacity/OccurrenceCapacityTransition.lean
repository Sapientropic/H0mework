import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityPhase

/-!
# Generated occurrence-capacity phase transitions

Exact source-bounded prefix cuts carry a canonical order.  Because rate is
definitionally the prefix cut and capacity is the one installed renewal-row
budget, the generated social phase evolves monotonically: stable is
downward-closed, anomie is upward-closed, and critical is the unique boundary.

This module adds no clock, scheduler, horizon, scalar oracle, or phase state.
It compares only two exact prefix seals of the same installed renewal and the
same source-owned queue compiler.
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
variable {leftPrefix rightPrefix : SourceGeneratedExactQueuePrefixAt compiler}
variable {leftPhase : SourceGeneratedOccurrenceCapacityPhaseAt
  installed compiler leftPrefix}
variable {rightPhase : SourceGeneratedOccurrenceCapacityPhaseAt
  installed compiler rightPrefix}

/-- Phase capacity depends only on the common installed row. -/
@[simp] theorem phase_capacity_eq
    (leftPhase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler leftPrefix)
    (rightPhase : SourceGeneratedOccurrenceCapacityPhaseAt
      installed compiler rightPrefix) :
    leftPhase.capacity = rightPhase.capacity :=
  rfl

/-- Cut-level spelling of the stable phase. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.phaseTag_eq_stable_iff_cut :
    leftPhase.phaseTag = .stable ↔ leftPrefix.cut < leftPhase.capacity := by
  rw [leftPhase.phaseTag_eq_stable_iff, leftPhase.rate_eq_prefixCut]

/-- Cut-level spelling of the critical boundary. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.phaseTag_eq_critical_iff_cut :
    leftPhase.phaseTag = .critical ↔ leftPrefix.cut = leftPhase.capacity := by
  rw [leftPhase.phaseTag_eq_critical_iff, leftPhase.rate_eq_prefixCut]

/-- Cut-level spelling of the anomie phase. -/
theorem SourceGeneratedOccurrenceCapacityPhaseAt.phaseTag_eq_anomie_iff_cut :
    leftPhase.phaseTag = .anomie ↔ leftPhase.capacity < leftPrefix.cut := by
  rw [leftPhase.phaseTag_eq_anomie_iff, leftPhase.rate_eq_prefixCut]

/-- Later exact cuts have weakly larger generated arrival rate. -/
theorem phase_rate_mono
    (cut_mono : leftPrefix.cut ≤ rightPrefix.cut) :
    leftPhase.rate ≤ rightPhase.rate := by
  rw [leftPhase.rate_eq_prefixCut, rightPhase.rate_eq_prefixCut]
  exact cut_mono

/-- Anomie is upward-closed along the exact source queue. -/
theorem anomie_persistent
    (cut_mono : leftPrefix.cut ≤ rightPrefix.cut)
    (leftAnomie : leftPhase.phaseTag = .anomie) :
    rightPhase.phaseTag = .anomie := by
  apply rightPhase.phaseTag_eq_anomie_iff.mpr
  exact lt_of_lt_of_le
    (leftPhase.phaseTag_eq_anomie_iff.mp leftAnomie)
    (phase_rate_mono (leftPhase := leftPhase) (rightPhase := rightPhase)
      cut_mono)

/-- Stable is downward-closed along the exact source queue. -/
theorem stable_hereditary
    (cut_mono : leftPrefix.cut ≤ rightPrefix.cut)
    (rightStable : rightPhase.phaseTag = .stable) :
    leftPhase.phaseTag = .stable := by
  apply leftPhase.phaseTag_eq_stable_iff.mpr
  exact lt_of_le_of_lt
    (phase_rate_mono (leftPhase := leftPhase) (rightPhase := rightPhase)
      cut_mono)
    (rightPhase.phaseTag_eq_stable_iff.mp rightStable)

/-- The critical boundary has one unique exact source cut. -/
theorem critical_cut_unique
    (leftCritical : leftPhase.phaseTag = .critical)
    (rightCritical : rightPhase.phaseTag = .critical) :
    leftPrefix.cut = rightPrefix.cut := by
  rw [← leftPhase.rate_eq_prefixCut, ← rightPhase.rate_eq_prefixCut]
  exact (leftPhase.phaseTag_eq_critical_iff.mp leftCritical).trans
    (rightPhase.phaseTag_eq_critical_iff.mp rightCritical).symm

/-- A one-unit source advance cannot jump directly from stable to anomie;
critical is a genuine intervening boundary. -/
theorem no_stable_to_anomie_at_successor
    (successorCut : rightPrefix.cut = leftPrefix.cut + 1)
    (leftStable : leftPhase.phaseTag = .stable)
    (rightAnomie : rightPhase.phaseTag = .anomie) : False := by
  have left_lt_capacity :=
    leftPhase.phaseTag_eq_stable_iff_cut.mp leftStable
  have capacity_lt_right :=
    rightPhase.phaseTag_eq_anomie_iff_cut.mp rightAnomie
  have sameCapacity : leftPhase.capacity = rightPhase.capacity := rfl
  omega

/-- The exact successor of a critical cut is necessarily anomie. -/
theorem critical_successor_is_anomie
    (successorCut : rightPrefix.cut = leftPrefix.cut + 1)
    (leftCritical : leftPhase.phaseTag = .critical) :
    rightPhase.phaseTag = .anomie := by
  apply rightPhase.phaseTag_eq_anomie_iff_cut.mpr
  have boundary := leftPhase.phaseTag_eq_critical_iff_cut.mp leftCritical
  have sameCapacity : leftPhase.capacity = rightPhase.capacity := rfl
  omega

/-- The exact predecessor of a positive critical cut is stable. -/
theorem critical_predecessor_is_stable
    (successorCut : rightPrefix.cut = leftPrefix.cut + 1)
    (rightCritical : rightPhase.phaseTag = .critical) :
    leftPhase.phaseTag = .stable := by
  apply leftPhase.phaseTag_eq_stable_iff_cut.mpr
  have boundary := rightPhase.phaseTag_eq_critical_iff_cut.mp rightCritical
  have sameCapacity : leftPhase.capacity = rightPhase.capacity := rfl
  omega

/-- Backlog length is monotone under exact prefix extension. -/
theorem backlog_length_mono
    (cut_mono : leftPrefix.cut ≤ rightPrefix.cut) :
    leftPhase.backlog.length ≤ rightPhase.backlog.length := by
  rw [leftPhase.backlog_length, rightPhase.backlog_length]
  have rate_mono := phase_rate_mono
    (leftPhase := leftPhase) (rightPhase := rightPhase) cut_mono
  have sameCapacity : leftPhase.capacity = rightPhase.capacity := rfl
  omega

/-- Once already in anomie, every strict source-prefix extension strictly
increases the unresolved backlog. -/
theorem anomie_backlog_strictly_grows
    (cut_strict : leftPrefix.cut < rightPrefix.cut)
    (leftAnomie : leftPhase.phaseTag = .anomie) :
    leftPhase.backlog.length < rightPhase.backlog.length := by
  rw [leftPhase.backlog_length, rightPhase.backlog_length]
  have left_over := leftPhase.phaseTag_eq_anomie_iff.mp leftAnomie
  have rate_strict : leftPhase.rate < rightPhase.rate := by
    rw [leftPhase.rate_eq_prefixCut, rightPhase.rate_eq_prefixCut]
    exact cut_strict
  have sameCapacity : leftPhase.capacity = rightPhase.capacity := rfl
  omega

end Capacity
end Society
end ProcessGame
end SaturationMonoid
