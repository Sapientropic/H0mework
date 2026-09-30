import H0mework.NavierStokes.Restart.FinitePrefixDualSquareLedger
import H0mework.NavierStokes.VelocityEndpoint.WholeMildReadWrite

/-!
# Absolute weak-trace glue at the generated whole-restart endpoint

The bounded actual restart run already selects one cofinal sequence of
physical contacts, its weak velocity endpoint, and a pointwise whole mild
write beginning at that endpoint.  This module welds those three facts on
the original absolute physical clock.

The prefix endpoint paired with contact `n` has length `n + 1`: it is the
actual physical state written by that contact, not an independently chosen
approximation.  Along the source-selected subsequence these absolute prefix
times converge to the same accumulation time, their Biot--Savart velocities
converge weakly to the selected endpoint, and the local time-zero row of the
new whole mild write is exactly that endpoint.

This is the missing trace glue between the old absolute write-chain and the
new local endpoint write.  It does not yet identify a positive local time
with an absolute time beyond the accumulation supremum.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWeakTraceGlue

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite

noncomputable section

/-- The source-selected prefix endpoints approach the accumulation endpoint
on the original absolute clock, converge weakly to its physical velocity,
and are written literally as the local time-zero row of the generated whole
mild path.  No subsequence, endpoint, path, target state, or continuation
witness is supplied by the caller. -/
theorem
    sourceGeneratedWholeRestartVelocityEndpoint_absoluteWeakTraceGlue
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    let selected := weak.subsequence
    let endpoint :=
      generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
        ledger.toCore
    Tendsto
        (fun index => elapsedTime initial (selected index + 1))
        atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
      (∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (puncturedWholeVelocityEuclideanState
                (wholeRestartPrefixPhysicalTrajectory initial
                  (selected index + 1)
                  (elapsedTime initial (selected index + 1))))
              test)
          atTop
          (nhds (inner ℂ weak.velocityEndpoint test))) ∧
      (∀ output : IntegerWavevector,
        endpoint.wholePath ⟨0, by norm_num⟩ output =
          wholeRestartVelocityEndpointCoefficient
            weak.velocityEndpoint output) := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let selected := weak.subsequence
  let endpoint :=
    generatedWholeRestartVelocityEndpointWholeMildReadWriteReceipt
      ledger.toCore
  change
    Tendsto
        (fun index => elapsedTime initial (selected index + 1))
        atTop
        (nhds (wholeRestartVelocityAccumulationTime initial)) ∧
      (∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index =>
            inner ℂ
              (puncturedWholeVelocityEuclideanState
                (wholeRestartPrefixPhysicalTrajectory initial
                  (selected index + 1)
                  (elapsedTime initial (selected index + 1))))
              test)
          atTop
          (nhds (inner ℂ weak.velocityEndpoint test))) ∧
      (∀ output : IntegerWavevector,
        endpoint.wholePath ⟨0, by norm_num⟩ output =
          wholeRestartVelocityEndpointCoefficient
            weak.velocityEndpoint output)
  have selectedEndpointStrictMono :
      StrictMono (fun index => selected index + 1) :=
    fun _ _ indexLt => Nat.add_lt_add_right (weak.subsequence_strictMono indexLt) 1
  refine ⟨?_, ?_, ?_⟩
  · exact
      (tendsto_atTop_ciSup
        (elapsedTime_strictMono initial).monotone elapsedBounded).comp
          selectedEndpointStrictMono.tendsto_atTop
  · intro test
    have prefixVelocityEq :
        (fun index =>
          inner ℂ
            (puncturedWholeVelocityEuclideanState
              (wholeRestartPrefixPhysicalTrajectory initial
                (selected index + 1)
                (elapsedTime initial (selected index + 1))))
            test) =
          (fun index =>
            inner ℂ
              (wholeRestartContactVelocityState initial (selected index))
              test) := by
      funext index
      rw [wholeRestartPrefixPhysicalTrajectory_endpoint,
        run_succ_initialState]
      rfl
    rw [prefixVelocityEq]
    exact weak.velocity_weak_tendsto_shared test
  · intro output
    exact endpoint.initial_row output

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWeakTraceGlue
end NavierStokes
end SaturationMonoid
