import H0mework.Versions.X.NavierStokes.ClockAccount.FullKineticResolution

/-!
# Original medium row supplies the kinetic clock

The operational ledger row already transfers the source-normalized medium
effect. Its receipt exposes the same physical contact time used by the
existing kinetic reserve inequality. This is a Real source payment readout;
the old structural Nat budget is unchanged.
-/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeRowKineticCoupling

open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open KineticClockResolution
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

private abbrev fixedSource := KineticClockResolution.source

/-- The row compiler's actual transfer preserves its source effect's clock. -/
theorem operationalRowContactTime_eq (stage : Nat) :
    nativeFluidMediumGeneratedOperationalContactTime? fixedSource
        (fixedSource.stateAfter stage) =
      some (fixedSource.clockAt (fixedSource.stateAfter stage)) := by
  rw [nativeFluidMediumGeneratedOperationalContactTime?_eq]
  rfl

/-- A physical-row transfer cannot stand in for the operational clock. -/
theorem physicalAdvance_has_no_operational_clock (stage : Nat)
    (occurrence : NativeFluidMediumOccurrence fixedSource (fixedSource.stateAfter stage)) :
    nativeFluidMediumTransferContactTime? fixedSource (fixedSource.stateAfter stage)
      (.physicalAdvance occurrence) = none :=
  rfl

/-- The time is extracted from the old row, with no arbitrary fallback value. -/
def operationalRowContactTime (stage : Nat) : Real :=
  (nativeFluidMediumGeneratedOperationalContactTime? fixedSource
    (fixedSource.stateAfter stage)).get (by
    rw [operationalRowContactTime_eq]
    rfl)

theorem operationalRowContactTime_source (stage : Nat) :
    operationalRowContactTime stage =
      fixedSource.clockAt (fixedSource.stateAfter stage) := by
  simp [operationalRowContactTime, operationalRowContactTime_eq]

/-- The independent kinetic consumer uses the literal old operational row's
contact time and the actual next mass; it does not mint Nat strict payment. -/
theorem originalRow_high_kinetic_payment (stage : Nat)
    (high : WindowMassCoefficient.halfCriticalMass < wholeVorticityEuclideanMass
      (run concreteCounterexampleInitial (stage + 1)).contact.physicalState) :
    operationalRowContactTime stage +
      (clockState (fixedSource.successor (fixedSource.stateAfter stage))).potential ≤
        (clockState (fixedSource.stateAfter stage)).potential := by
  rw [operationalRowContactTime_source]
  exact KineticClockResolution.dominationOfHigh stage high

/-- The same source successor is the original root visit's next current. -/
theorem originalRow_kinetic_next (stage : Nat) :
    (nativeFluidMediumRootVisit fixedSource (stage + 1)).current =
      fixedSource.successor (nativeFluidMediumRootVisit fixedSource stage).current := by
  rfl

end
end SaturationMonoid.NavierStokes.NativeRowKineticCoupling
