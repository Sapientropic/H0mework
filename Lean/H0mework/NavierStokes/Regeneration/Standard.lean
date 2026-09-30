import H0mework.NavierStokes.Regeneration.LowContact
import H0mework.NavierStokes.Regeneration.EvenContact
import H0mework.NavierStokes.WholeReceipt.Global

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceFieldRenewal

open Set
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCompleteSerrinLanding
open ThreeDimensionalVorticityCoefficientStandingPaidMediumState
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock

noncomputable section

variable {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
  (reachable : ButterflyCreditClockFaceReachableAt stage face)
  (shortfall : ButterflyCreditClockFaceResidualAt stage face
    (sourceGeneratedStandingActionRunClockDisposition stackedInitialActionMaterialInstruction stage))

include reachable shortfall in
theorem residual_source_time_unbounded :
    ¬ BddAbove (range (elapsedTime concreteCounterexampleInitial)) := by
  obtain ⟨index, _within, low⟩ := residual_source_lowContact reachable shortfall
  exact source_time_unbounded_of_lowContact (index + 1) low

/-- An actual reachable payment failure selects the original standard NS
global solution through its own time window and preserved spatial symmetry. -/
def standardGlobalOfReachableResidual :
    StandardGlobalWholeMildSerrinSolutionAt concreteCounterexampleViscosity
      concreteCounterexampleInitial.initialState :=
  WholeGlobalReceipt.ofTrajectory
    (generatedWholeGlobalPhysicalTrajectory_of_unbounded concreteCounterexampleInitial
      (residual_source_time_unbounded reachable shortfall))

end
end SaturationMonoid.NavierStokes.SourceFieldRenewal
