import H0mework.NavierStokes.EndpointWork.QuadraticBoundaryCocycle

/-!
# Pre-quotient pair-work compiler for the quadratic kinetic boundary

The quadratic boundary of one actual native velocity edge already sees the
complete Duhamel row.  This module transports the existing summable
pair-innovation table through the actual Biot--Savart velocity row and the
incoming-velocity pairing before any pair or output quotient.

For each output, the kinetic pairing is exactly

```text
incoming velocity paired with frozen tangent
+ tsum of incoming velocity paired with each pair innovation.
```

The outputwise equality then compiles the whole one-edge pairing and every
finite-path quadratic telescope.  The pair `tsum` remains inside its actual
output occurrence; no independent global pair summability, output cutoff,
enumeration, cancellation certificate, or target state is supplied.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler

open scoped BigOperators

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryCocycle

noncomputable section

/-! ## Exact continuous-linear pair readout -/

/-- Biot--Savart inversion followed by Euclideanization of one physical
velocity row, as the continuous-linear map consumed by pair `tsum`. -/
def wholeRestartVelocityEuclideanRowCLM
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →L[ℂ] ComplexCoordinateEuclidean :=
  (PiLp.continuousLinearEquiv
      2 ℂ (fun _ : Coordinate => ℂ)).symm.toContinuousLinearMap.comp
    (biotSavartVelocityLinearMap wave).toContinuousLinearMap

@[simp] theorem wholeRestartVelocityEuclideanRowCLM_apply
    (wave : IntegerWavevector)
    (state : ComplexCoordinateVector) :
    wholeRestartVelocityEuclideanRowCLM wave state =
      euclideanCoordinateRow
        (biotSavartVelocityCoefficient wave state) := rfl

/-- The incoming-velocity pairing commutes with the complete source-generated
pair-innovation series at one actual output. -/
theorem wholeRestartPairInnovationVelocityInner_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (test : ComplexCoordinateEuclidean) :
    inner ℂ test
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first))) =
      ∑' first : IntegerWavevector,
        inner ℂ test
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first))) := by
  let workCLM : ComplexCoordinateVector →L[ℂ] ℂ :=
    (innerSL ℂ test).comp
      (wholeRestartVelocityEuclideanRowCLM wave.1)
  have mapped := workCLM.map_tsum
    (summable_wholeRestartPairDuhamelInnovationOccurrence
      current index wave.1)
  simpa [workCLM] using mapped

/-- Taking the real kinetic readout also commutes with the same complete
pair-innovation series. -/
theorem wholeRestartPairInnovationVelocityRealInner_tsum
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (test : ComplexCoordinateEuclidean) :
    RCLike.re (inner ℂ test
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (∑' first : IntegerWavevector,
              wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)))) =
      ∑' first : IntegerWavevector,
        RCLike.re (inner ℂ test
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)))) := by
  let workCLM : ComplexCoordinateVector →L[ℂ] ℂ :=
    (innerSL ℂ test).comp
      (wholeRestartVelocityEuclideanRowCLM wave.1)
  have workSummable : Summable fun first : IntegerWavevector =>
      inner ℂ test
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartPairDuhamelInnovationOccurrence
              current index wave.1 first))) := by
    have mapped :=
      (summable_wholeRestartPairDuhamelInnovationOccurrence
        current index wave.1).map workCLM workCLM.continuous
    exact mapped.congr fun first => by rfl
  rw [wholeRestartPairInnovationVelocityInner_tsum]
  change Complex.reCLM (∑' first : IntegerWavevector,
      inner ℂ test
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartPairDuhamelInnovationOccurrence
              current index wave.1 first)))) = _
  exact Complex.reCLM.map_tsum workSummable

/-! ## One-output and whole-edge component compilers -/

/-- At one actual nonzero output, the real kinetic pairing splits exactly
into its frozen tangent work and the complete pre-quotient pair-work `tsum`.
-/
theorem wholeRestartCausalDuhamelVelocityRealInner_eq_tangent_add_pairWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1 +
              ∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first)))) =
      RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index wave)
        (euclideanCoordinateRow
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartCausalTangentGain current index wave.1 •
              wholeRestartCrossingUnforcedTangentRow
                current index wave.1)))) +
      ∑' first : IntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelInnovationOccurrence
                current index wave.1 first)))) := by
  have complexSplit :
      inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartCausalTangentGain current index wave.1 •
                  wholeRestartCrossingUnforcedTangentRow
                    current index wave.1 +
                ∑' first : IntegerWavevector,
                  wholeRestartPairDuhamelInnovationOccurrence
                    current index wave.1 first))) =
        inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1))) +
        inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first))) := by
    change inner ℂ _
      (wholeRestartVelocityEuclideanRowCLM wave.1 (_ + _)) = _
    rw [map_add, inner_add_right]
    simp only [wholeRestartVelocityEuclideanRowCLM_apply]
  calc
    _ = RCLike.re
        (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1))) +
        inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first)))) :=
      congrArg (fun value : ℂ => RCLike.re value) complexSplit
    _ = RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartCausalTangentGain current index wave.1 •
                wholeRestartCrossingUnforcedTangentRow
                  current index wave.1)))) +
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState current index wave)
          (euclideanCoordinateRow
            (biotSavartVelocityCoefficient wave.1
              (∑' first : IntegerWavevector,
                wholeRestartPairDuhamelInnovationOccurrence
                  current index wave.1 first)))) := by
      exact map_add Complex.reCLM _ _
    _ = _ := by
      rw [wholeRestartPairInnovationVelocityRealInner_tsum]

/-- The whole one-edge kinetic pairing is the outputwise `tsum` of the
same-output tangent work plus the complete pair-work `tsum`.  The inner pair
series is not pulled across the outer output quotient. -/
theorem
    wholeRestartNativeCausalVelocityWrite_realInner_eq_tsum_tangent_add_pairWork
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    RCLike.re (inner ℂ
        (wholeRestartContactVelocityState current index)
        (wholeRestartNativeCausalVelocityWrite current index)) =
      ∑' wave : NonzeroIntegerWavevector,
        (RCLike.re (inner ℂ
            (wholeRestartContactVelocityState current index wave)
            (euclideanCoordinateRow
              (biotSavartVelocityCoefficient wave.1
                (wholeRestartCausalTangentGain current index wave.1 •
                  wholeRestartCrossingUnforcedTangentRow
                    current index wave.1)))) +
          ∑' first : IntegerWavevector,
            RCLike.re (inner ℂ
              (wholeRestartContactVelocityState current index wave)
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartPairDuhamelInnovationOccurrence
                    current index wave.1 first))))) := by
  rw [wholeRestartNativeCausalVelocityWrite_realInner_eq_tsum]
  apply tsum_congr
  intro wave
  rw [
    wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation,
    wholeRestartCausalDuhamelVelocityRealInner_eq_tangent_add_pairWork]

/-! ## Finite-path componentwise quadratic boundary -/

/-- The finite actual-path quadratic boundary now exposes its tangent and
complete output×pair work before aggregation, while retaining the exact
endpoint kinetic telescope. -/
theorem wholeRestartFiniteCausalComponentKineticBoundary_telescope
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 *
          (∑' wave : NonzeroIntegerWavevector,
            (RCLike.re (inner ℂ
                (wholeRestartContactVelocityState
                  current (start + offset) wave)
                (euclideanCoordinateRow
                  (biotSavartVelocityCoefficient wave.1
                    (wholeRestartCausalTangentGain
                          current (start + offset) wave.1 •
                        wholeRestartCrossingUnforcedTangentRow
                          current (start + offset) wave.1)))) +
              ∑' first : IntegerWavevector,
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState
                    current (start + offset) wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)))))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) =
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 -
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
  rw [← wholeRestartFiniteCausalKineticBoundary_telescope]
  apply Finset.sum_congr rfl
  intro offset _offsetMem
  congr 2
  exact
    (wholeRestartNativeCausalVelocityWrite_realInner_eq_tsum_tangent_add_pairWork
      current (start + offset)).symm

/-- The componentwise finite quadratic boundary remains nonpositive by the
same actual kinetic descent. -/
theorem wholeRestartFiniteCausalComponentKineticBoundary_nonpos
    {ν : Viscosity}
    (current : GeneratedWholeRestartCurrent ν)
    (start steps : ℕ) :
    (∑ offset ∈ Finset.range steps,
      (2 *
          (∑' wave : NonzeroIntegerWavevector,
            (RCLike.re (inner ℂ
                (wholeRestartContactVelocityState
                  current (start + offset) wave)
                (euclideanCoordinateRow
                  (biotSavartVelocityCoefficient wave.1
                    (wholeRestartCausalTangentGain
                          current (start + offset) wave.1 •
                        wholeRestartCrossingUnforcedTangentRow
                          current (start + offset) wave.1)))) +
              ∑' first : IntegerWavevector,
                RCLike.re (inner ℂ
                  (wholeRestartContactVelocityState
                    current (start + offset) wave)
                  (euclideanCoordinateRow
                    (biotSavartVelocityCoefficient wave.1
                      (wholeRestartPairDuhamelInnovationOccurrence
                        current (start + offset) wave.1 first)))))) +
        ‖wholeRestartNativeCausalVelocityWrite
          current (start + offset)‖ ^ 2)) ≤ 0 := by
  rw [wholeRestartFiniteCausalComponentKineticBoundary_telescope]
  have massLe :=
    run_contact_kineticMass_antitone current
      (Nat.le_add_right start steps)
  have velocityNormLe :
      ‖wholeRestartContactVelocityState current (start + steps)‖ ^ 2 ≤
        ‖wholeRestartContactVelocityState current start‖ ^ 2 := by
    rw [wholeRestartContactVelocityState_norm_sq,
      wholeRestartContactVelocityState_norm_sq]
    exact massLe
  linarith

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler
end NavierStokes
end SaturationMonoid
