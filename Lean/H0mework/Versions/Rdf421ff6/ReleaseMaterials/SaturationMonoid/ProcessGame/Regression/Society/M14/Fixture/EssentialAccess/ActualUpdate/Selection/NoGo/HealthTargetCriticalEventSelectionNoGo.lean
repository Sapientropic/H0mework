import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Continuation.Root.SourceGeneratedHealthCessationTargetHistory

/-!
# Old health-target occurrence cannot select the next critical event

Finite temporal visits of the health target are distinct, but its old root
vocabulary has `Current = Unit`.  The emitted raw occurrence is therefore the
same at every finite visit.  Any event readout which factors only through that
old occurrence is constant and cannot cover two distinct essential-access
events.  A later selector needs a genuinely source-generated dependent face;
causal depth, a caller event or a static schedule is not old-root authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14HealthTargetCriticalEventSelectionNoGo

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Power
open M14EssentialAccessRelationFixture
open M14SourceGeneratedHealthCessationTargetRoot
open M14SourceGeneratedHealthCessationTargetHistory

abbrev HealthTargetRawOccurrence :=
  healthCessationTargetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt ()

def healthTargetRawOccurrenceAt (depth : Nat) :
    HealthTargetRawOccurrence :=
  (healthCessationTargetExactEventAt depth).occurrence

@[simp] theorem healthTargetRawOccurrenceAt_eq (depth : Nat) :
    healthTargetRawOccurrenceAt depth =
      healthCessationTargetRoot.emitted () :=
  rfl

theorem healthTargetRawOccurrenceAt_constant (left right : Nat) :
    healthTargetRawOccurrenceAt left = healthTargetRawOccurrenceAt right := by
  rw [healthTargetRawOccurrenceAt_eq, healthTargetRawOccurrenceAt_eq]

theorem every_oldRawCriticalEventReadout_is_constant
    (readout : HealthTargetRawOccurrence → EssentialAccessEvent)
    (left right : Nat) :
    readout (healthTargetRawOccurrenceAt left) =
      readout (healthTargetRawOccurrenceAt right) :=
  congrArg readout (healthTargetRawOccurrenceAt_constant left right)

/-- A selector which asks the old raw occurrence to cover every existing
critical event.  It deliberately does not expose temporal visit identity. -/
structure OldHealthTargetCriticalEventCoverageAt : Type where
  readout : HealthTargetRawOccurrence → EssentialAccessEvent
  covers : ∀ event : EssentialAccessEvent,
    ∃ depth : Nat, readout (healthTargetRawOccurrenceAt depth) = event

theorem oldHealthTargetCriticalEventCoverage_isEmpty :
    IsEmpty OldHealthTargetCriticalEventCoverageAt := by
  constructor
  rintro ⟨readout, covers⟩
  rcases covers .health with ⟨healthDepth, healthExact⟩
  rcases covers .platform with ⟨platformDepth, platformExact⟩
  have constant := every_oldRawCriticalEventReadout_is_constant readout
    healthDepth platformDepth
  rw [healthExact, platformExact] at constant
  cases constant

/-- A temporal selector which claims authority only by factoring through the
old raw occurrence.  The temporal visit may be inspected for typing, but it
cannot affect the selected event. -/
structure OldHealthTargetCurrentFactoredSelectorAt : Type 2 where
  select : (visit : SourceNativeTemporalVisitAt
    healthCessationTargetRoot.toAuthoritativeRoot.toLedgerRoot) →
      EssentialAccessEvent
  readout : HealthTargetRawOccurrence → EssentialAccessEvent
  factorizes : ∀ depth : Nat,
    select (healthCessationTargetTemporalVisitAt depth) =
      readout (healthTargetRawOccurrenceAt depth)

structure OldHealthTargetCurrentFactoredFamilyCoverageAt : Type 3 where
  selector : OldHealthTargetCurrentFactoredSelectorAt
  covers : ∀ event : EssentialAccessEvent,
    ∃ depth : Nat,
      selector.select (healthCessationTargetTemporalVisitAt depth) = event

theorem oldHealthTargetCurrentFactoredFamilyCoverage_isEmpty :
    IsEmpty OldHealthTargetCurrentFactoredFamilyCoverageAt := by
  constructor
  rintro ⟨selector, covers⟩
  apply oldHealthTargetCriticalEventCoverage_isEmpty.false
  exact
    { readout := selector.readout
      covers := fun event => by
        rcases covers event with ⟨depth, selected⟩
        exact ⟨depth, (selector.factorizes depth).symm.trans selected⟩ }

/-- The fulfilled health terminal has no reopen event from which a next
critical-event seed could be read. -/
abbrev HealthTerminalCriticalContinuationAt :=
  Sigma fun archive : TerminalArchive Lifecycle.LifecycleVocabulary =>
    (criticalRelationTerminalProcess
      M14SourceGeneratedEssentialAccessCriticalTerminal.essentialAccessCriticalBearerOf
      ).ReopenEvent archive

theorem healthTerminalCriticalContinuation_isEmpty :
    IsEmpty HealthTerminalCriticalContinuationAt :=
  ⟨fun continuation =>
    M14SourceGeneratedEssentialAccessCriticalTerminal.healthCriticalTerminal_no_reopen
      continuation.1 |>.false continuation.2⟩

/-- The obstruction is not a lack of finite occurrences: visit identity is
present and injective, but is absent from the old raw occurrence readout. -/
structure HealthTargetCriticalEventSelectionObstructionAt : Prop where
  finiteVisitsInjective :
    Function.Injective healthCessationTargetTemporalVisitAt
  rawOccurrencesConstant : ∀ left right,
    healthTargetRawOccurrenceAt left = healthTargetRawOccurrenceAt right
  oldCoverageEmpty : IsEmpty OldHealthTargetCriticalEventCoverageAt
  factoredCoverageEmpty :
    IsEmpty OldHealthTargetCurrentFactoredFamilyCoverageAt
  terminalContinuationEmpty : IsEmpty HealthTerminalCriticalContinuationAt

theorem healthTargetCriticalEventSelectionObstruction :
    HealthTargetCriticalEventSelectionObstructionAt :=
  { finiteVisitsInjective := healthCessationTargetTemporalVisitAt_injective
    rawOccurrencesConstant := healthTargetRawOccurrenceAt_constant
    oldCoverageEmpty := oldHealthTargetCriticalEventCoverage_isEmpty
    factoredCoverageEmpty :=
      oldHealthTargetCurrentFactoredFamilyCoverage_isEmpty
    terminalContinuationEmpty := healthTerminalCriticalContinuation_isEmpty }

end
end M14HealthTargetCriticalEventSelectionNoGo
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14HealthTargetCriticalEventSelectionNoGo.oldHealthTargetCriticalEventCoverage_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14HealthTargetCriticalEventSelectionNoGo.oldHealthTargetCurrentFactoredFamilyCoverage_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14HealthTargetCriticalEventSelectionNoGo.healthTerminalCriticalContinuation_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14HealthTargetCriticalEventSelectionNoGo.healthTargetCriticalEventSelectionObstruction
