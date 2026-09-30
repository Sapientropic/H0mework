import H0mework.NavierStokes.Regeneration.Window
import H0mework.NavierStokes.Regeneration.Tail

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.SourceDensityRegeneration

open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ThreeDimensionalVorticityCoefficientStandingPaidActionMaterialInstruction
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock
open ThreeDimensionalVorticityCoefficientButterflyStandingActionKineticClock.DensityAccount
open RationalVorticityEvaluator
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent

noncomputable section

theorem reachable_reserve_covers_current_min
    {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face) :
    min (min (wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) 2)
      (standingActionBarrierTail butterflyGainViscosity (source.stateAfter stage).1.standing.anchorLevel) ≤
        physicalDensityReserve stage := by
  cases reachable with
  | initial =>
      simp only [physicalDensityReserve, Finset.range_zero, Finset.sum_empty, add_zero]
      exact (min_le_left _ _).trans (min_le_right _ _)
  | @next prior previous rawNext previousReachable previousSettlement =>
      exact densityReserve_covers_of_transition previousReachable
        (butterflyRetainFaceSettlement prior previousSettlement).1
        (butterflyRetainFaceSettlement prior previousSettlement).2.1

/-- A real failing edge has a low-density actual terminal contact. -/
theorem residual_generates_terminal_low_density_contact
    {stage : Nat} {face : ButterflyCreditClockFaceAt (source.stateAfter stage)}
    (reachable : ButterflyCreditClockFaceReachableAt stage face)
    (shortfall : ButterflyCreditClockFaceResidualAt stage face
      (sourceGeneratedStandingActionRunClockDisposition stackedInitialActionMaterialInstruction stage)) :
    wholeVorticityEuclideanMass
      (source.stateAfter (stage + 1)).1.physical.contact.physicalState < 1 + WindowMassCoefficient.epsilon := by
  by_contra absent
  have nextHigh : 1 + WindowMassCoefficient.epsilon ≤ wholeVorticityEuclideanMass
      (run stackedShortCurrent (stage + 1)).contact.physicalState := by
    rw [← physicalCurrent_eq_run]
    exact le_of_not_gt absent
  have currentHigh : 1 ≤ wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState := by
    rw [physicalCurrent_eq_run]
    linarith [next_mass_le_current_add_epsilon stage]
  have covered := reachable_reserve_covers_current_min reachable
  have tailOne := source_tail_le_one stage
  have minEquals : min (min (wholeVorticityEuclideanMass
      (source.stateAfter stage).1.physical.contact.physicalState) 2)
      (standingActionBarrierTail butterflyGainViscosity (source.stateAfter stage).1.standing.anchorLevel) =
        standingActionBarrierTail butterflyGainViscosity (source.stateAfter stage).1.standing.anchorLevel :=
    min_eq_right (le_min (tailOne.trans currentHigh) (tailOne.trans (by norm_num)))
  rw [minEquals] at covered
  have density := window_density_nonneg_of_high stage nextHigh
  have step := physicalDensityReserve_step stage
  have nextCovered : standingActionBarrierTail butterflyGainViscosity
      (source.stateAfter (stage + 1)).1.standing.anchorLevel ≤ physicalDensityReserve (stage + 1) := by
    have decreasing := source_tail_next_le stage
    linarith
  have failure := (residual_densityReserve_shortfall reachable shortfall).trans_le (min_le_right _ _)
  exact not_lt_of_ge nextCovered failure

end
end SaturationMonoid.NavierStokes.SourceDensityRegeneration
