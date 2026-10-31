import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.OccurrenceCapacityTransition
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M10.OccurrenceCapacityPhaseRegression

/-!
# M10 generated phase-transition regression

The exact source queue advances from cut one to cut two to cut three.  With
the same installed capacity two this is the generated path

```text
stable → critical → anomie.
```

The transition consumes no clock, external rate, or mutable phase state.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M10OccurrenceCapacityTransitionRegression

noncomputable section

open Capacity
open M10OccurrenceCapacityPhaseRegression

@[simp] theorem cutOne_to_cutTwo_is_successor :
    cutTwo.cut = cutOne.cut + 1 :=
  rfl

@[simp] theorem cutTwo_to_cutThree_is_successor :
    cutThree.cut = cutTwo.cut + 1 :=
  rfl

/-- Critical is reached from the exact stable predecessor. -/
theorem stable_precedes_critical : stablePhase.phaseTag = .stable :=
  critical_predecessor_is_stable
    (leftPhase := stablePhase) (rightPhase := criticalPhase)
    cutOne_to_cutTwo_is_successor critical_phase_exact

/-- The exact unit after critical generates anomie. -/
theorem anomie_follows_critical : anomiePhase.phaseTag = .anomie :=
  critical_successor_is_anomie
    (leftPhase := criticalPhase) (rightPhase := anomiePhase)
    cutTwo_to_cutThree_is_successor critical_phase_exact

/-- The source cannot classify two different exact cuts as critical. -/
theorem critical_boundary_is_unique
    {candidatePrefix : SourceGeneratedExactQueuePrefixAt phaseCompiler}
    {candidatePhase : SourceGeneratedOccurrenceCapacityPhaseAt
      M10OccurrenceCapacityRenewalRootFixture.installedRenewal phaseCompiler
        candidatePrefix}
    (candidateCritical : candidatePhase.phaseTag = .critical) :
    candidatePrefix.cut = cutTwo.cut :=
  critical_cut_unique
    (leftPhase := candidatePhase) (rightPhase := criticalPhase)
    candidateCritical critical_phase_exact

theorem stable_to_critical_backlog_mono :
    stablePhase.backlog.length ≤ criticalPhase.backlog.length :=
  backlog_length_mono
    (leftPhase := stablePhase) (rightPhase := criticalPhase) (by decide)

theorem critical_to_anomie_backlog_mono :
    criticalPhase.backlog.length ≤ anomiePhase.backlog.length :=
  backlog_length_mono
    (leftPhase := criticalPhase) (rightPhase := anomiePhase) (by decide)

structure OccurrenceCapacityTransitionCertificate where
  stable : stablePhase.phaseTag = .stable
  critical : criticalPhase.phaseTag = .critical
  anomie : anomiePhase.phaseTag = .anomie
  firstSuccessor : cutTwo.cut = cutOne.cut + 1
  secondSuccessor : cutThree.cut = cutTwo.cut + 1
  stableCriticalBacklog :
    stablePhase.backlog.length ≤ criticalPhase.backlog.length
  criticalAnomieBacklog :
    criticalPhase.backlog.length ≤ anomiePhase.backlog.length

theorem occurrenceCapacityTransitionDirectConsumer :
    OccurrenceCapacityTransitionCertificate where
  stable := stable_precedes_critical
  critical := critical_phase_exact
  anomie := anomie_follows_critical
  firstSuccessor := cutOne_to_cutTwo_is_successor
  secondSuccessor := cutTwo_to_cutThree_is_successor
  stableCriticalBacklog := stable_to_critical_backlog_mono
  criticalAnomieBacklog := critical_to_anomie_backlog_mono

end
end M10OccurrenceCapacityTransitionRegression
end Society
end ProcessGame
end SaturationMonoid
