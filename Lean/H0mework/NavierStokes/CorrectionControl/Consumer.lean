import H0mework.NavierStokes.CorrectionControl.WholeActual

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeTurbulenceControl

open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

/-- Control is read on both outcomes of the original native equation.
The revised outcome retains all original micro receipts and the literal recovery write. -/
def BoundaryControlled (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial) : Prop :=
  answer.fold
    (fun _ trajectory => ∀ (horizon : ℝ) (positive : 0 < horizon)
      (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) horizon),
      ‖puncturedEuclideanize
        (receiptWholeCorrection ((WholeGlobalReceipt.ofTrajectory trajectory).receiptAt horizon positive) modes time)‖ ^ 2 ≤
        3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖)
    (fun _ _ law =>
      (∀ (index : Nat) (modes : Finset IntegerWavevector)
        (time : Icc (0 : ℝ) (run initial index).nextContact.time.1),
        ‖puncturedEuclideanize (receiptWholeCorrection (run initial index).nextContact.prefixReceipt modes time)‖ ^ 2 ≤
          3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖) ∧
      (∀ (modes : Finset IntegerWavevector) (time : Icc (0 : ℝ) law.recovery.next.duration),
        ‖puncturedEuclideanize (receiptWholeCorrection law.recovery.next.receipt modes time)‖ ^ 2 ≤
          3 * wholeBudget ‖puncturedWholeVelocityEuclideanState initial.initialState‖))

theorem boundary_control (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial) :
    BoundaryControlled answer := by
  unfold BoundaryControlled SourceGeneratedNativeBoundaryReachabilityAnswerAt.fold
  split
  · intro horizon positive modes time
    exact receipt_wholeCorrection_norm_sq_le _ modes time
  · exact ⟨original_wholeCorrection_norm_sq_le initial, recovery_wholeCorrection_norm_sq_le _⟩

/-- Source-only full-frequency control of the original native turbulence
answer. No old/revised choice or classical global regularity is an input. -/
theorem source_generated_boundary_control (initial : GeneratedWholeRestartCurrent nu) :
    BoundaryControlled (sourceGeneratedNativeBoundaryReachabilityAnswer initial) :=
  boundary_control _

end
end SaturationMonoid.NavierStokes.NativeTurbulenceControl
