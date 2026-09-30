import H0mework.NavierStokes.KineticRestart.KineticDefectZeroVelocityCompletion
import H0mework.NavierStokes.VelocityEndpoint.AbsoluteWholeMildNativeContinuation

/-!
# Zero-defect strong trace on the absolute endpoint clock

The bounded native restart run already generates both sides of the endpoint
splice: its actual absolute prefix endpoints and the whole mild path beginning
at the accumulation time.  When the source-generated kinetic endpoint defect
vanishes, the exact kinetic/velocity contact isometry upgrades the old weak
trace to strong convergence in the complete physical velocity carrier.

This file identifies that strong limit with the literal time-`T` state of the
generated absolute endpoint path.  No endpoint, subsequence, target path,
continuation witness, or faithfulness certificate is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroAbsoluteStrongTrace

open Set Filter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation

noncomputable section

/-- The generated absolute endpoint path at its accumulation-time boundary,
restricted to the complete nonzero-wave Euclidean velocity carrier, is
literally the weak endpoint selected from the old actual run. -/
theorem sourceGeneratedWholeRestartVelocityEndpoint_absoluteInitialVelocity
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    let accumulationTime := wholeRestartVelocityAccumulationTime initial
    let absoluteStart : Icc accumulationTime (accumulationTime + 1) :=
      ⟨accumulationTime, by constructor <;> linarith⟩
    puncturedEuclideanize
        (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
          initial elapsedBounded absoluteStart) =
      weak.velocityEndpoint := by
  dsimp only
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  apply lp.ext
  funext wave
  ext coordinate
  change
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
        initial elapsedBounded
        ⟨wholeRestartVelocityAccumulationTime initial, _⟩
        wave.1 coordinate = _
  rw [continuation.absolutePath_initial_row wave.1,
    wholeRestartVelocityEndpointCoefficient_of_ne
      _ wave.1 wave.2]

/-- If the internally generated kinetic endpoint defect is zero, the actual
prefix endpoint velocities converge strongly on the original absolute clock
to the literal time-`T` boundary state of the generated endpoint path.  The
time and state limits are paired before any coordinate quotient is taken. -/
theorem
    sourceGeneratedWholeRestartVelocityEndpoint_absoluteStrongTrace_of_kineticDefect_eq_zero
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    let accumulationTime := wholeRestartVelocityAccumulationTime initial
    let absoluteStart : Icc accumulationTime (accumulationTime + 1) :=
      ⟨accumulationTime, by constructor <;> linarith⟩
    Tendsto
      (fun index =>
        (elapsedTime initial (weak.subsequence index + 1),
          puncturedWholeVelocityEuclideanState
            (wholeRestartPrefixPhysicalTrajectory initial
              (weak.subsequence index + 1)
              (elapsedTime initial (weak.subsequence index + 1)))))
      atTop
      (nhds
        (accumulationTime,
          puncturedEuclideanize
            (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
              initial elapsedBounded absoluteStart))) := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  have prefixTimeTendsto :
      Tendsto
        (fun index => elapsedTime initial (weak.subsequence index + 1))
        atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) := by
    simpa only [ledger, weak] using
      continuation.prefixEndpointTime_tendsto
  have contactVelocityStrong :
      Tendsto
        (fun index =>
          wholeRestartContactVelocityState
            initial (weak.subsequence index))
        atTop
        (nhds weak.velocityEndpoint) := by
    exact velocity_strong_tendsto_of_kineticDefect_eq_zero
      weak defectZero
  have prefixVelocityEq :
      (fun index =>
        puncturedWholeVelocityEuclideanState
          (wholeRestartPrefixPhysicalTrajectory initial
            (weak.subsequence index + 1)
            (elapsedTime initial (weak.subsequence index + 1)))) =
        (fun index =>
          wholeRestartContactVelocityState
            initial (weak.subsequence index)) := by
    funext index
    rw [wholeRestartPrefixPhysicalTrajectory_endpoint,
      run_succ_initialState]
    rfl
  have prefixVelocityStrong :
      Tendsto
        (fun index =>
          puncturedWholeVelocityEuclideanState
            (wholeRestartPrefixPhysicalTrajectory initial
              (weak.subsequence index + 1)
              (elapsedTime initial (weak.subsequence index + 1))))
        atTop
        (nhds weak.velocityEndpoint) := by
    rw [prefixVelocityEq]
    exact contactVelocityStrong
  have absoluteInitialVelocity :
      puncturedEuclideanize
          (sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholePath
            initial elapsedBounded
            ⟨wholeRestartVelocityAccumulationTime initial, by
              constructor <;> linarith⟩) =
        weak.velocityEndpoint := by
    simpa only [ledger, weak] using
      sourceGeneratedWholeRestartVelocityEndpoint_absoluteInitialVelocity
        initial elapsedBounded
  rw [absoluteInitialVelocity]
  exact prefixTimeTendsto.prodMk_nhds prefixVelocityStrong

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroAbsoluteStrongTrace
end NavierStokes
end SaturationMonoid
