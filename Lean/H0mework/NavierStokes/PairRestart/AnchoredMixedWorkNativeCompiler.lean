import H0mework.NavierStokes.EndpointWork.AnchoredMixedWork
import H0mework.NavierStokes.PairRestart.AnchoredReflectedPairNativeProcess
import H0mework.NavierStokes.PairRestart.AnchoredHeatCommutatorNativeVelocityPairRedirect

/-!
# Exact native compiler for anchored mixed work

One actual native velocity write is the Biot--Savart readout of its frozen
contact tangent plus the complete output-by-input-pair Duhamel innovation.
This module pairs that equality with the actual source contact selected by an
anchored frame and then compiles the pair part before its input-pair quotient.

An individual ordered vorticity pair does not invert to one ordered velocity
occurrence: physical curl identifies the generated pair together with its
swap.  The compiler therefore states the exact symmetric identity.  Its
right-hand side is the two actual anchored direct Duhamel works minus the
literal frozen-contact subtraction.  Both ordered direct works are then
consumed by the native reflected-pair exhaustion.

The public whole-edge theorem takes only an authoritative restart current and
an actual `start/offset` frame.  Output and pair occurrences are universally
quantified in its conclusion.  No equality, sign, nonzero, cutoff, coverage,
path, or continuation witness enters its mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredMixedWorkNativeCompiler

open scoped BigOperators Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelTangentInnovation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomCollectiveCausalGapWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomQuadraticBoundaryPairWorkCompiler
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEndpointKineticAtomAnchoredMixedWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredReflectedPairNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHeatCommutatorNativeVelocityPairRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredHeatCommutatorNativeVelocityPairRedirect
open AffineRelaxation

noncomputable section

/-! ## Exact whole-edge tangent / pair split at the actual anchor -/

/-- Frozen-tangent contribution to the source-anchor work at one actual
nonzero output. -/
def wholeRestartAnchoredCausalTangentVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  RCLike.re (inner ℂ
    (wholeRestartContactVelocityState initial frame.start wave)
    (euclideanCoordinateRow
      (biotSavartVelocityCoefficient wave.1
        (wholeRestartCausalTangentGain
              initial frame.currentIndex wave.1 •
          wholeRestartCrossingUnforcedTangentRow
            initial frame.currentIndex wave.1))))

/-- One complete pre-quotient pair-innovation contribution to the same
source-anchor work. -/
def wholeRestartAnchoredPairInnovationVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) : ℝ :=
  RCLike.re (inner ℂ
    (wholeRestartContactVelocityState initial frame.start wave)
    (euclideanCoordinateRow
      (biotSavartVelocityCoefficient wave.1
        (wholeRestartPairDuhamelInnovationOccurrence
          initial frame.currentIndex wave.1 first))))

/-- The actual source-anchor pairing with the literal native velocity write.
-/
def wholeRestartAnchoredNativeCausalVelocityWriteWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) : ℝ :=
  RCLike.re (inner ℂ
    (wholeRestartContactVelocityState initial frame.start)
    (wholeRestartNativeCausalVelocityWrite initial frame.currentIndex))

/-- The actual source-anchor work splits exactly into the frozen tangent and
the complete output-by-pair innovation.  Neither series is replaced by a
norm or aggregate pair observer. -/
theorem
    wholeRestartAnchoredNativeCausalVelocityWriteWork_eq_tsum_tangent_add_pairInnovation
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    wholeRestartAnchoredNativeCausalVelocityWriteWork initial frame =
      ∑' wave : NonzeroIntegerWavevector,
        (wholeRestartAnchoredCausalTangentVelocityWork
            initial frame wave +
          ∑' first : IntegerWavevector,
            wholeRestartAnchoredPairInnovationVelocityWork
              initial frame wave first) := by
  unfold wholeRestartAnchoredNativeCausalVelocityWriteWork
  rw [lp.inner_eq_tsum]
  calc
    RCLike.re
        (∑' wave : NonzeroIntegerWavevector,
          inner ℂ
            (wholeRestartContactVelocityState initial frame.start wave)
            (wholeRestartNativeCausalVelocityWrite
              initial frame.currentIndex wave)) =
      ∑' wave : NonzeroIntegerWavevector,
        RCLike.re (inner ℂ
          (wholeRestartContactVelocityState initial frame.start wave)
          (wholeRestartNativeCausalVelocityWrite
            initial frame.currentIndex wave)) :=
      Complex.reCLM.map_tsum
        (lp.summable_inner
          (wholeRestartContactVelocityState initial frame.start)
          (wholeRestartNativeCausalVelocityWrite
            initial frame.currentIndex))
    _ = _ := by
      apply tsum_congr
      intro wave
      rw [
        wholeRestartNativeCausalVelocityWrite_apply_eq_causalTangent_add_pairInnovation]
      change
        RCLike.re (inner ℂ _
          (wholeRestartVelocityEuclideanRowCLM wave.1 (_ + _))) = _
      rw [map_add, inner_add_right]
      simp only [map_add]
      unfold wholeRestartAnchoredCausalTangentVelocityWork
        wholeRestartAnchoredPairInnovationVelocityWork
      rw [wholeRestartVelocityEuclideanRowCLM_apply,
        wholeRestartVelocityEuclideanRowCLM_apply]
      exact congrArg
        (fun value : ℝ =>
          RCLike.re (inner ℂ
              (wholeRestartContactVelocityState initial frame.start wave)
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartCausalTangentGain
                        initial frame.currentIndex wave.1 •
                    wholeRestartCrossingUnforcedTangentRow
                      initial frame.currentIndex wave.1)))) +
            value)
        (wholeRestartAnchorPairInnovationVelocityRealInner_tsum
          initial frame.start frame.currentIndex wave)

/-! ## Symmetric pair compiler before the curl quotient -/

/-- Source anchor velocity row at one actual nonzero output. -/
def wholeRestartAnchoredOutputVelocity
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateVector :=
  finiteStateVelocityCoefficient
    (wholeRestartAnchoredReflectedPairAnchor initial frame)
    wave.1

/-- The two actual velocity-pair Duhamel occurrences tested against the
source anchor before physical curl. -/
def wholeRestartAnchoredSymmetricVelocityPairDuhamelWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) : ℝ :=
  complexCoordinateRealInner
    (finiteStateVelocityCoefficient
      (wholeRestartAnchoredReflectedPairAnchor initial frame)
      (first + second))
    (wholeRestartSymmetricVelocityPairDuhamelOccurrence
      initial frame.currentIndex first second)

/-- Testing the actual symmetric velocity-pair Duhamel vector by the source
anchor is exactly the sum of its two ordered anchored direct works. -/
theorem
    wholeRestartAnchoredSymmetricVelocityPairDuhamelWork_eq_direct_add_swap
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (first second : IntegerWavevector) :
    wholeRestartAnchoredSymmetricVelocityPairDuhamelWork
        initial frame first second =
      wholeRestartAnchoredDirectVelocityBilinearEnergyWork
          initial frame first second +
        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
          initial frame second first := by
  let endpoint :=
    wholeRestartAnchoredReflectedPairTerminalTime initial frame
  let μ :=
    (commonTimeMeasure
      (run initial frame.currentIndex).nextContact.time.1).restrict
        (Iic endpoint)
  let anchorVelocity :=
    finiteStateVelocityCoefficient
      (wholeRestartAnchoredReflectedPairAnchor initial frame)
      (first + second)
  let firstPair := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    actualWholeContinuousVelocityPairVector
      (run initial frame.currentIndex).nextContact.prefixReceipt
      first second earlier
  let secondPair := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    actualWholeContinuousVelocityPairVector
      (run initial frame.currentIndex).nextContact.prefixReceipt
      second first earlier
  let heat := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    finiteStateVorticityHeatMultiplier
      ν.coeff (endpoint.1 - earlier.1) (first + second)
  let row := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    heat earlier • (firstPair earlier + secondPair earlier)
  have heatContinuous : Continuous heat := by
    unfold heat finiteStateVorticityHeatMultiplier
    fun_prop
  have firstPairContinuous : Continuous firstPair :=
    actualWholeContinuousVelocityPairVector_continuous
      (run initial frame.currentIndex).nextContact.prefixReceipt
      first second
  have secondPairContinuous : Continuous secondPair :=
    actualWholeContinuousVelocityPairVector_continuous
      (run initial frame.currentIndex).nextContact.prefixReceipt
      second first
  have rowContinuous : Continuous row := by
    exact heatContinuous.smul
      (firstPairContinuous.add secondPairContinuous)
  have rowIntegrable : Integrable row μ :=
    (rowContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  let firstScalar := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    heat earlier *
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame first second earlier
  let secondScalar := fun earlier :
      Icc (0 : ℝ)
        (run initial frame.currentIndex).nextContact.time.1 =>
    heat earlier *
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
        initial frame second first earlier
  have firstScalarContinuous : Continuous firstScalar :=
    heatContinuous.mul
      (wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence_continuous
        initial frame first second)
  have secondScalarContinuous : Continuous secondScalar := by
    have swappedHeat :
        (fun earlier :
            Icc (0 : ℝ)
              (run initial frame.currentIndex).nextContact.time.1 =>
          finiteStateVorticityHeatMultiplier
            ν.coeff (endpoint.1 - earlier.1) (second + first)) =
          heat := by
      funext earlier
      unfold heat
      rw [add_comm second first]
    exact heatContinuous.mul
      (wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence_continuous
        initial frame second first)
  have firstScalarIntegrable : Integrable firstScalar μ :=
    (firstScalarContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  have secondScalarIntegrable : Integrable secondScalar μ :=
    (secondScalarContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).integrableOn
  unfold wholeRestartAnchoredSymmetricVelocityPairDuhamelWork
    wholeRestartSymmetricVelocityPairDuhamelOccurrence
    actualWholeSymmetricVelocityPairDuhamelOccurrence
    wholeRestartAnchoredDirectVelocityBilinearEnergyWork
    wholeRestartAnchoredReflectedPairTerminalTime
  have mapIntegral :
      complexCoordinateRealInner anchorVelocity
          (∫ earlier, row earlier ∂μ) =
        ∫ earlier,
          complexCoordinateRealInner anchorVelocity (row earlier) ∂μ := by
    symm
    exact
      (complexCoordinateRealInnerRightCLM anchorVelocity).integral_comp_comm
        rowIntegrable
  have scalarSplit :
      (∫ earlier,
          complexCoordinateRealInner anchorVelocity (row earlier) ∂μ) =
        (∫ earlier, firstScalar earlier ∂μ) +
          ∫ earlier, secondScalar earlier ∂μ := by
    rw [← integral_add firstScalarIntegrable secondScalarIntegrable]
    apply integral_congr_ae
    filter_upwards with earlier
    unfold row firstScalar secondScalar
    rw [complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_add_right]
    simp only [heat, firstPair, secondPair,
      actualWholeContinuousVelocityPairVector,
      wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence,
      finiteStateVelocityBilinearEnergyOccurrence, anchorVelocity]
    ring_nf
  have compiled := mapIntegral.trans scalarSplit
  simpa [endpoint, μ, anchorVelocity, row, heat, firstPair, secondPair,
    firstScalar, secondScalar,
    wholeRestartAnchoredReflectedPairTerminalTime,
    add_comm second first] using compiled

/-- Source-anchor velocity work of one actual pair innovation together with
its generated swap.  This is the smallest carrier on which physical curl can
be inverted without losing an ordered occurrence. -/
def wholeRestartAnchoredSymmetricPairInnovationVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) : ℝ :=
  complexCoordinateRealInner
    (wholeRestartAnchoredOutputVelocity initial frame wave)
    (biotSavartVelocityCoefficient wave.1
      (wholeRestartPairDuhamelInnovationOccurrence
          initial frame.currentIndex wave.1 first +
        wholeRestartPairDuhamelInnovationOccurrence
          initial frame.currentIndex wave.1 (wave.1 - first)))

/-- Literal frozen-contact subtraction carried by the same symmetric input
pair.  It remains visible in the compiler instead of being folded into the
dynamic Duhamel work. -/
def wholeRestartAnchoredSymmetricFrozenContactPairVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) : ℝ :=
  complexCoordinateRealInner
    (wholeRestartAnchoredOutputVelocity initial frame wave)
    (biotSavartVelocityCoefficient wave.1
      (wholeRestartCausalTangentGain
          initial frame.currentIndex wave.1 •
        (wholeRestartContactPairOccurrenceTable
            initial frame.currentIndex wave.1 first +
          wholeRestartContactPairOccurrenceTable
            initial frame.currentIndex wave.1 (wave.1 - first))))

/-- Exact pre-quotient pair compiler.

The symmetrized pair innovation equals the two actual anchored direct
Duhamel works, minus the frozen source-contact pair transported by the same
causal gain.  The symmetry is forced by the existing curl compiler; no
individual ordered occurrence is silently identified with its curl image. -/
theorem
    wholeRestartAnchoredSymmetricPairInnovationVelocityWork_eq_direct_add_swap_sub_frozen
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartAnchoredSymmetricPairInnovationVelocityWork
        initial frame wave first =
      wholeRestartAnchoredDirectVelocityBilinearEnergyWork
          initial frame first (wave.1 - first) +
        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
          initial frame (wave.1 - first) first -
        wholeRestartAnchoredSymmetricFrozenContactPairVelocityWork
          initial frame wave first := by
  let second : IntegerWavevector := wave.1 - first
  have innovationSum :
      wholeRestartPairDuhamelInnovationOccurrence
            initial frame.currentIndex wave.1 first +
          wholeRestartPairDuhamelInnovationOccurrence
            initial frame.currentIndex wave.1 second =
        (wholeRestartPairDuhamelOccurrence
              initial frame.currentIndex wave.1 first +
            wholeRestartPairDuhamelOccurrence
              initial frame.currentIndex wave.1 second) -
          wholeRestartCausalTangentGain
              initial frame.currentIndex wave.1 •
            (wholeRestartContactPairOccurrenceTable
                  initial frame.currentIndex wave.1 first +
              wholeRestartContactPairOccurrenceTable
                  initial frame.currentIndex wave.1 second) := by
    unfold wholeRestartPairDuhamelInnovationOccurrence
    module
  have anchorTransverse :
      complexWavevector wave.1 ⬝ᵥ
          wholeRestartAnchoredOutputVelocity initial frame wave = 0 := by
    unfold wholeRestartAnchoredOutputVelocity
      finiteStateVelocityCoefficient
    exact complexWavevector_dot_biotSavartVelocityCoefficient _ _
  unfold wholeRestartAnchoredSymmetricPairInnovationVelocityWork
    wholeRestartAnchoredSymmetricFrozenContactPairVelocityWork
  change
    complexCoordinateRealInner
        (wholeRestartAnchoredOutputVelocity initial frame wave)
        (biotSavartVelocityCoefficient wave.1
          (wholeRestartPairDuhamelInnovationOccurrence
                initial frame.currentIndex wave.1 first +
            wholeRestartPairDuhamelInnovationOccurrence
                initial frame.currentIndex wave.1 second)) =
      _
  rw [innovationSum, biotSavartVelocityCoefficient_sub,
    complexCoordinateRealInner_sub_right]
  rw [
    wholeRestartPairDuhamelOccurrence_add_swap_eq_velocityPair_curl
      initial frame.currentIndex wave.1 first]
  rw [
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      wave.1
      (wholeRestartSymmetricVelocityPairDuhamelOccurrence
        initial frame.currentIndex first second)
      wave.2]
  rw [
    complexCoordinateRealInner_transverseProjection
      wave.1
      (wholeRestartAnchoredOutputVelocity initial frame wave)
      (wholeRestartSymmetricVelocityPairDuhamelOccurrence
        initial frame.currentIndex first second)
      wave.2 anchorTransverse]
  have symmetricWork :=
    wholeRestartAnchoredSymmetricVelocityPairDuhamelWork_eq_direct_add_swap
      initial frame first second
  have symmetricTerm :
      complexCoordinateRealInner
          (wholeRestartAnchoredOutputVelocity initial frame wave)
          (wholeRestartSymmetricVelocityPairDuhamelOccurrence
            initial frame.currentIndex first second) =
        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
            initial frame first second +
          wholeRestartAnchoredDirectVelocityBilinearEnergyWork
            initial frame second first := by
    simpa [wholeRestartAnchoredSymmetricVelocityPairDuhamelWork,
      wholeRestartAnchoredOutputVelocity, second] using symmetricWork
  rw [symmetricTerm]

/-! ## Source-facing whole-edge compiler -/

/-- One actual anchored velocity edge is compiled all the way to its native
componentwise disposition.

The first conjunct is the exact whole-edge tangent/pair decomposition.  The
second universally quantifies every nonzero output and input-pair occurrence:
its symmetric innovation is the two ordered anchored Duhamel works minus the
frozen-contact subtraction, and each ordered work is either faithfully zero,
leaves the generated heat commutator, or is written into the actual
next/trace pair process. -/
theorem
    wholeRestartAnchoredNativeCausalVelocityWriteWork_componentwise_nativeCompiler
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame) :
    wholeRestartAnchoredNativeCausalVelocityWriteWork initial frame =
        ∑' wave : NonzeroIntegerWavevector,
          (wholeRestartAnchoredCausalTangentVelocityWork
              initial frame wave +
            ∑' first : IntegerWavevector,
              wholeRestartAnchoredPairInnovationVelocityWork
                initial frame wave first) ∧
      let settles := fun first second : IntegerWavevector =>
        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
              initial frame first second = 0 ∨
          wholeRestartAnchoredVelocityTriadHeatCommutatorTrace
              initial frame first second ≠ 0 ∨
          ∃ time :
              Icc (0 : ℝ)
                (run initial frame.currentIndex).nextContact.time.1,
            wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
                initial frame first second time ≠ 0 ∧
              actualWholeRestartAnchoredReflectedVelocityPairVector
                  initial frame first
                    (outputNegSecondEquiv first second) time ≠ 0 ∧
              (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                    initial frame first
                      (outputNegSecondEquiv first second) ≠ 0 ∨
                wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                    initial frame first
                      (outputNegSecondEquiv first second) time ≠ 0) ∧
              run initial frame.next.currentIndex =
                (run initial frame.currentIndex).next
      ∀ wave : NonzeroIntegerWavevector,
        ∀ first : IntegerWavevector,
          wholeRestartAnchoredSymmetricPairInnovationVelocityWork
                initial frame wave first =
              wholeRestartAnchoredDirectVelocityBilinearEnergyWork
                  initial frame first (wave.1 - first) +
                wholeRestartAnchoredDirectVelocityBilinearEnergyWork
                  initial frame (wave.1 - first) first -
                wholeRestartAnchoredSymmetricFrozenContactPairVelocityWork
                  initial frame wave first ∧
            settles first (wave.1 - first) ∧
              settles (wave.1 - first) first := by
  refine
    ⟨wholeRestartAnchoredNativeCausalVelocityWriteWork_eq_tsum_tangent_add_pairInnovation
      initial frame, ?_⟩
  dsimp only
  intro wave first
  refine
    ⟨wholeRestartAnchoredSymmetricPairInnovationVelocityWork_eq_direct_add_swap_sub_frozen
      initial frame wave first, ?_, ?_⟩
  · exact
      wholeRestartAnchoredVelocityBilinearEnergyWork_nativeExhaustion
        initial frame first (wave.1 - first)
  · exact
      wholeRestartAnchoredVelocityBilinearEnergyWork_nativeExhaustion
        initial frame (wave.1 - first) first

/-! ## Whole-output cancellation of the frozen nonlinear contact -/

/-- Linear viscous/heat displacement left after the frozen contact nonlinear
row in the pair innovation cancels the identical nonlinear row in the frozen
tangent. -/
def wholeRestartAnchoredViscousHeatDisplacementVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  RCLike.re (inner ℂ
    (wholeRestartContactVelocityState initial frame.start wave)
    (euclideanCoordinateRow
      (biotSavartVelocityCoefficient wave.1
        (-wholeRestartCausalTangentGain
              initial frame.currentIndex wave.1 •
          ((ν.coeff * integerWaveViscousMultiplier wave.1) •
            (run initial frame.currentIndex).contact.physicalState
              wave.1)))))

/-- Actual complete nonlinear regeneration at one output, tested by the
source anchor after Biot--Savart. -/
def wholeRestartAnchoredNonlinearRegenerationVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  RCLike.re (inner ℂ
    (wholeRestartContactVelocityState initial frame.start wave)
    (euclideanCoordinateRow
      (biotSavartVelocityCoefficient wave.1
        (wholeRestartNonlinearRegenerationState
          initial frame.currentIndex wave.1))))

/-- Outputwise exact cancellation of the frozen contact nonlinear row.

The tangent contributes `gain • (N(contact) - νA(contact))`; the complete
pair innovation contributes `regeneration - gain • N(contact)`.  Their
identical source-owned nonlinear rows cancel before any norm or sign readout,
leaving the actual regeneration plus the linear viscous/heat displacement. -/
theorem
    wholeRestartAnchoredOutputTangent_add_pairInnovation_eq_viscousHeat_add_regeneration
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartAnchoredCausalTangentVelocityWork initial frame wave +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairInnovationVelocityWork
            initial frame wave first =
      wholeRestartAnchoredViscousHeatDisplacementVelocityWork
          initial frame wave +
        wholeRestartAnchoredNonlinearRegenerationVelocityWork
          initial frame wave := by
  have innovationTsum :=
    tsum_wholeRestartPairDuhamelInnovationOccurrence_eq
      initial frame.currentIndex wave.1 wave.2
  have rowIdentity :
      wholeRestartCausalTangentGain
            initial frame.currentIndex wave.1 •
          wholeRestartCrossingUnforcedTangentRow
            initial frame.currentIndex wave.1 +
        (∑' first : IntegerWavevector,
          wholeRestartPairDuhamelInnovationOccurrence
            initial frame.currentIndex wave.1 first) =
      (-wholeRestartCausalTangentGain
            initial frame.currentIndex wave.1) •
          ((ν.coeff * integerWaveViscousMultiplier wave.1) •
            (run initial frame.currentIndex).contact.physicalState
              wave.1) +
        wholeRestartNonlinearRegenerationState
          initial frame.currentIndex wave.1 := by
    rw [innovationTsum]
    unfold wholeRestartCrossingUnforcedTangentRow
    module
  have pairTsum :=
    wholeRestartAnchorPairInnovationVelocityRealInner_tsum
      initial frame.start frame.currentIndex wave
  unfold wholeRestartAnchoredCausalTangentVelocityWork
    wholeRestartAnchoredPairInnovationVelocityWork
    wholeRestartAnchoredViscousHeatDisplacementVelocityWork
    wholeRestartAnchoredNonlinearRegenerationVelocityWork
  rw [← pairTsum]
  let workCLM : ComplexCoordinateVector →L[ℂ] ℂ :=
    (innerSL ℂ
      (wholeRestartContactVelocityState initial frame.start wave)).comp
        (wholeRestartVelocityEuclideanRowCLM wave.1)
  change
    RCLike.re (workCLM
          (wholeRestartCausalTangentGain
              initial frame.currentIndex wave.1 •
            wholeRestartCrossingUnforcedTangentRow
              initial frame.currentIndex wave.1)) +
        RCLike.re (workCLM
          (∑' first : IntegerWavevector,
            wholeRestartPairDuhamelInnovationOccurrence
              initial frame.currentIndex wave.1 first)) =
      RCLike.re (workCLM
          ((-wholeRestartCausalTangentGain
              initial frame.currentIndex wave.1) •
            ((ν.coeff * integerWaveViscousMultiplier wave.1) •
              (run initial frame.currentIndex).contact.physicalState
                wave.1))) +
        RCLike.re (workCLM
          (wholeRestartNonlinearRegenerationState
            initial frame.currentIndex wave.1))
  have mapped :=
    congrArg (fun row : ComplexCoordinateVector =>
      RCLike.re (workCLM row)) rowIdentity
  simpa only [map_add] using mapped

/-! ## Regeneration as the symmetric direct-work sum -/

/-- One actual causal vorticity pair transported through Biot--Savart and
tested by the source anchor. -/
def wholeRestartAnchoredPairDuhamelVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) : ℝ :=
  complexCoordinateRealInner
    (wholeRestartAnchoredOutputVelocity initial frame wave)
    (biotSavartVelocityCoefficient wave.1
      (wholeRestartPairDuhamelOccurrence
        initial frame.currentIndex wave.1 first))

/-- The exact pair-plus-swap direct work at one fixed nonzero output. -/
def wholeRestartAnchoredSymmetricDirectDuhamelWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) : ℝ :=
  wholeRestartAnchoredDirectVelocityBilinearEnergyWork
      initial frame first (wave.1 - first) +
    wholeRestartAnchoredDirectVelocityBilinearEnergyWork
      initial frame (wave.1 - first) first

/-- The fixed-output pair-Duhamel anchor works form a summable real series. -/
theorem summable_wholeRestartAnchoredPairDuhamelVelocityWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    Summable fun first : IntegerWavevector =>
      wholeRestartAnchoredPairDuhamelVelocityWork
        initial frame wave first := by
  let complexWorkCLM : ComplexCoordinateVector →L[ℂ] ℂ :=
    (innerSL ℂ
      (euclideanCoordinateRow
        (wholeRestartAnchoredOutputVelocity initial frame wave))).comp
      (wholeRestartVelocityEuclideanRowCLM wave.1)
  have vectorSummable :=
    summable_wholeRestartPairDuhamelOccurrence
      initial frame.currentIndex wave.1
  have complexSummable :
      Summable fun first : IntegerWavevector =>
        complexWorkCLM
          (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 first) :=
    vectorSummable.map complexWorkCLM complexWorkCLM.continuous
  have realSummable :
      Summable fun first : IntegerWavevector =>
        RCLike.re (complexWorkCLM
          (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 first)) :=
    complexSummable.map Complex.reCLM Complex.reCLM.continuous
  exact realSummable.congr fun first => by
    change
      RCLike.re
          (inner ℂ
            (euclideanCoordinateRow
              (wholeRestartAnchoredOutputVelocity initial frame wave))
            (euclideanCoordinateRow
              (biotSavartVelocityCoefficient wave.1
                (wholeRestartPairDuhamelOccurrence
                  initial frame.currentIndex wave.1 first)))) =
        complexCoordinateRealInner
          (wholeRestartAnchoredOutputVelocity initial frame wave)
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartPairDuhamelOccurrence
              initial frame.currentIndex wave.1 first))
    exact euclideanCoordinateRow_re_inner _ _

/-- Complete nonlinear regeneration is the `tsum` of its actual causal
pair-Duhamel anchor works. -/
theorem
    wholeRestartAnchoredNonlinearRegenerationVelocityWork_eq_tsum_pairDuhamel
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartAnchoredNonlinearRegenerationVelocityWork
        initial frame wave =
      ∑' first : IntegerWavevector,
        wholeRestartAnchoredPairDuhamelVelocityWork
          initial frame wave first := by
  let complexWorkCLM : ComplexCoordinateVector →L[ℂ] ℂ :=
    (innerSL ℂ
      (wholeRestartContactVelocityState initial frame.start wave)).comp
        (wholeRestartVelocityEuclideanRowCLM wave.1)
  have vectorSummable :=
    summable_wholeRestartPairDuhamelOccurrence
      initial frame.currentIndex wave.1
  have complexSummable :
      Summable fun first : IntegerWavevector =>
        complexWorkCLM
          (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 first) :=
    vectorSummable.map complexWorkCLM complexWorkCLM.continuous
  have mappedComplex :=
    complexWorkCLM.map_tsum vectorSummable
  have mappedReal :=
    Complex.reCLM.map_tsum complexSummable
  have regenerationTsum :=
    tsum_wholeRestartPairDuhamelOccurrence_eq_regeneration
      initial frame.currentIndex wave.1 wave.2
  unfold wholeRestartAnchoredNonlinearRegenerationVelocityWork
    wholeRestartAnchoredPairDuhamelVelocityWork
  change
    RCLike.re (complexWorkCLM
      (wholeRestartNonlinearRegenerationState
        initial frame.currentIndex wave.1)) =
      ∑' first : IntegerWavevector,
        complexCoordinateRealInner
          (wholeRestartAnchoredOutputVelocity initial frame wave)
          (biotSavartVelocityCoefficient wave.1
            (wholeRestartPairDuhamelOccurrence
              initial frame.currentIndex wave.1 first))
  rw [← regenerationTsum, mappedComplex]
  calc
    RCLike.re
        (∑' first : IntegerWavevector,
          complexWorkCLM
            (wholeRestartPairDuhamelOccurrence
              initial frame.currentIndex wave.1 first)) =
        ∑' first : IntegerWavevector,
          RCLike.re
            (complexWorkCLM
              (wholeRestartPairDuhamelOccurrence
                initial frame.currentIndex wave.1 first)) := by
      simpa using mappedReal
    _ =
        ∑' first : IntegerWavevector,
          complexCoordinateRealInner
            (wholeRestartAnchoredOutputVelocity initial frame wave)
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelOccurrence
                initial frame.currentIndex wave.1 first)) := by
      apply tsum_congr
      intro first
      change
        RCLike.re
            (inner ℂ
              (euclideanCoordinateRow
                (wholeRestartAnchoredOutputVelocity initial frame wave))
              (euclideanCoordinateRow
                (biotSavartVelocityCoefficient wave.1
                  (wholeRestartPairDuhamelOccurrence
                    initial frame.currentIndex wave.1 first)))) =
          complexCoordinateRealInner
            (wholeRestartAnchoredOutputVelocity initial frame wave)
            (biotSavartVelocityCoefficient wave.1
              (wholeRestartPairDuhamelOccurrence
                initial frame.currentIndex wave.1 first))
      exact euclideanCoordinateRow_re_inner _ _

/-- Pair-plus-swap through curl/Biot--Savart is exactly the two ordered
anchored direct Duhamel works. -/
theorem
    wholeRestartAnchoredPairDuhamelVelocityWork_add_swap_eq_symmetricDirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector)
    (first : IntegerWavevector) :
    wholeRestartAnchoredPairDuhamelVelocityWork
          initial frame wave first +
        wholeRestartAnchoredPairDuhamelVelocityWork
          initial frame wave (wave.1 - first) =
      wholeRestartAnchoredSymmetricDirectDuhamelWork
        initial frame wave first := by
  let second : IntegerWavevector := wave.1 - first
  have anchorTransverse :
      complexWavevector wave.1 ⬝ᵥ
          wholeRestartAnchoredOutputVelocity initial frame wave = 0 := by
    unfold wholeRestartAnchoredOutputVelocity
      finiteStateVelocityCoefficient
    exact complexWavevector_dot_biotSavartVelocityCoefficient _ _
  unfold wholeRestartAnchoredPairDuhamelVelocityWork
    wholeRestartAnchoredSymmetricDirectDuhamelWork
  rw [← complexCoordinateRealInner_add_right]
  have biotAdd :=
    (biotSavartVelocityLinearMap wave.1).map_add
      (wholeRestartPairDuhamelOccurrence
        initial frame.currentIndex wave.1 first)
      (wholeRestartPairDuhamelOccurrence
        initial frame.currentIndex wave.1 (wave.1 - first))
  change
    biotSavartVelocityCoefficient wave.1
        (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 first +
          wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 (wave.1 - first)) =
      biotSavartVelocityCoefficient wave.1
          (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 first) +
        biotSavartVelocityCoefficient wave.1
          (wholeRestartPairDuhamelOccurrence
            initial frame.currentIndex wave.1 (wave.1 - first)) at biotAdd
  rw [← biotAdd]
  rw [
    wholeRestartPairDuhamelOccurrence_add_swap_eq_velocityPair_curl
      initial frame.currentIndex wave.1 first]
  rw [
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      wave.1
      (wholeRestartSymmetricVelocityPairDuhamelOccurrence
        initial frame.currentIndex first second)
      wave.2]
  rw [
    complexCoordinateRealInner_transverseProjection
      wave.1
      (wholeRestartAnchoredOutputVelocity initial frame wave)
      (wholeRestartSymmetricVelocityPairDuhamelOccurrence
        initial frame.currentIndex first second)
      wave.2 anchorTransverse]
  have symmetricWork :=
    wholeRestartAnchoredSymmetricVelocityPairDuhamelWork_eq_direct_add_swap
      initial frame first second
  have outputEq : wave.1 = first + second := by
    simp [second]
  unfold wholeRestartAnchoredOutputVelocity
  rw [outputEq]
  rw [show first + second - first = second by abel]
  simpa only [wholeRestartAnchoredSymmetricVelocityPairDuhamelWork] using
    symmetricWork

set_option maxHeartbeats 800000 in
/-- Exact whole-output compiler without an illicit individual curl inverse:
twice the actual regeneration work is the `tsum` of the generated symmetric
direct works. -/
theorem
    two_mul_wholeRestartAnchoredNonlinearRegenerationVelocityWork_eq_tsum_symmetricDirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    2 * wholeRestartAnchoredNonlinearRegenerationVelocityWork
          initial frame wave =
      ∑' first : IntegerWavevector,
        wholeRestartAnchoredSymmetricDirectDuhamelWork
          initial frame wave first := by
  have directSummable :=
    summable_wholeRestartAnchoredPairDuhamelVelocityWork
      initial frame wave
  have reflectInvolutive :
      Function.Involutive
        (fun first : IntegerWavevector => wave.1 - first) := by
    intro first
    ext coordinate
    simp
  have reflectInjective :
      Function.Injective
        (fun first : IntegerWavevector => wave.1 - first) :=
    reflectInvolutive.injective
  have reflectSurjective :
      Function.Surjective
        (fun first : IntegerWavevector => wave.1 - first) :=
    reflectInvolutive.surjective
  have outsideRangeZero :
      ∀ index ∉ Set.range
          (fun first : IntegerWavevector => wave.1 - first),
        wholeRestartAnchoredPairDuhamelVelocityWork
          initial frame wave index = 0 := by
    intro index indexOutside
    exact False.elim (indexOutside (reflectSurjective index))
  have shiftedHasSum :
      HasSum
        ((wholeRestartAnchoredPairDuhamelVelocityWork initial frame wave) ∘
          fun first : IntegerWavevector => wave.1 - first)
        (∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first) :=
    (reflectInjective.hasSum_iff outsideRangeZero).2
      directSummable.hasSum
  have swappedSummable :
      Summable fun first : IntegerWavevector =>
        wholeRestartAnchoredPairDuhamelVelocityWork
          initial frame wave (wave.1 - first) :=
    by
      change
        Summable
          ((wholeRestartAnchoredPairDuhamelVelocityWork
              initial frame wave) ∘
            fun first : IntegerWavevector => wave.1 - first)
      exact shiftedHasSum.summable
  have shiftedTsum :
      (∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave (wave.1 - first)) =
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first := by
    change
      (∑' first : IntegerWavevector,
          ((wholeRestartAnchoredPairDuhamelVelocityWork
              initial frame wave) ∘
            fun first : IntegerWavevector => wave.1 - first) first) =
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first
    exact shiftedHasSum.tsum_eq
  calc
    2 * wholeRestartAnchoredNonlinearRegenerationVelocityWork
          initial frame wave =
        (∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first) +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first := by
      rw [
        wholeRestartAnchoredNonlinearRegenerationVelocityWork_eq_tsum_pairDuhamel]
      exact two_mul _
    _ =
        (∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave first) +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairDuhamelVelocityWork
            initial frame wave (wave.1 - first) := by
      exact
        congrArg
          (fun value : ℝ =>
            (∑' first : IntegerWavevector,
              wholeRestartAnchoredPairDuhamelVelocityWork
                initial frame wave first) + value)
          shiftedTsum.symm
    _ =
        ∑' first : IntegerWavevector,
          (wholeRestartAnchoredPairDuhamelVelocityWork
              initial frame wave first +
            wholeRestartAnchoredPairDuhamelVelocityWork
              initial frame wave (wave.1 - first)) := by
      rw [Summable.tsum_add directSummable swappedSummable]
    _ =
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredSymmetricDirectDuhamelWork
            initial frame wave first := by
      apply tsum_congr
      intro first
      exact
        wholeRestartAnchoredPairDuhamelVelocityWork_add_swap_eq_symmetricDirect
          initial frame wave first

/-- The frozen cancellation and symmetric curl compiler combine into one
outputwise equality directly consumable by the source-selected negative
anchor row. -/
theorem
    two_mul_wholeRestartAnchoredOutputContribution_eq_viscousHeat_add_tsum_symmetricDirect
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    2 * (wholeRestartAnchoredCausalTangentVelocityWork
          initial frame wave +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredPairInnovationVelocityWork
            initial frame wave first) =
      2 * wholeRestartAnchoredViscousHeatDisplacementVelocityWork
          initial frame wave +
        ∑' first : IntegerWavevector,
          wholeRestartAnchoredSymmetricDirectDuhamelWork
            initial frame wave first := by
  rw [
    wholeRestartAnchoredOutputTangent_add_pairInnovation_eq_viscousHeat_add_regeneration]
  calc
    2 *
        (wholeRestartAnchoredViscousHeatDisplacementVelocityWork
            initial frame wave +
          wholeRestartAnchoredNonlinearRegenerationVelocityWork
            initial frame wave) =
        2 * wholeRestartAnchoredViscousHeatDisplacementVelocityWork
            initial frame wave +
          2 * wholeRestartAnchoredNonlinearRegenerationVelocityWork
            initial frame wave := by ring_nf
    _ =
        2 * wholeRestartAnchoredViscousHeatDisplacementVelocityWork
            initial frame wave +
          ∑' first : IntegerWavevector,
            wholeRestartAnchoredSymmetricDirectDuhamelWork
              initial frame wave first := by
      rw [
        two_mul_wholeRestartAnchoredNonlinearRegenerationVelocityWork_eq_tsum_symmetricDirect]

/-! ## Sign-free output disposition -/

/-- The actual anchored output has no silent negative branch.  Either its
complete tangent-plus-pair contribution is nonnegative, the source-generated
viscous heat displacement is already negative, or one actual incidence pair
has negative direct work and is written into the ordinary/reflected native
pair process.  No sign, pair, time, branch, or target witness is supplied by
the caller. -/
theorem wholeRestartAnchoredOutputContribution_nativePairDisposition
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (frame : WholeRestartAnchoredReflectedPairFrame)
    (wave : NonzeroIntegerWavevector) :
    0 ≤
        wholeRestartAnchoredCausalTangentVelocityWork
            initial frame wave +
          ∑' first : IntegerWavevector,
            wholeRestartAnchoredPairInnovationVelocityWork
              initial frame wave first ∨
      wholeRestartAnchoredViscousHeatDisplacementVelocityWork
          initial frame wave < 0 ∨
      ∃ first second : IntegerWavevector,
        first + second = wave.1 ∧
          wholeRestartAnchoredDirectVelocityBilinearEnergyWork
              initial frame first second < 0 ∧
          ((∃ time :
                Icc (0 : ℝ)
                  (run initial frame.currentIndex).nextContact.time.1,
              wholeRestartAnchoredDirectVelocityBilinearEnergyOccurrence
                    initial frame first second time ≠ 0 ∧
                actualWholeContinuousVelocityPairVector
                    (run initial frame.currentIndex).nextContact.prefixReceipt
                    first second time ≠ 0 ∧
                (wholeRestartNextVelocityPairOccurrence
                      initial frame.currentIndex first second ≠ 0 ∨
                  (linearResidualTrace
                      wholeRestartSplicedVelocityPairOccurrenceTailKeep
                      (wholeRestartSplicedVelocityPairOccurrenceTail
                        initial frame.currentIndex time 0) 0)
                        first second ≠ 0) ∧
                run initial frame.next.currentIndex =
                  (run initial frame.currentIndex).next) ∨
            ∃ time :
                Icc (0 : ℝ)
                  (run initial frame.currentIndex).nextContact.time.1,
              wholeRestartAnchoredReflectedVelocityBilinearEnergyOccurrence
                    initial frame first second time ≠ 0 ∧
                actualWholeRestartAnchoredReflectedVelocityPairVector
                    initial frame first
                      (outputNegSecondEquiv first second) time ≠ 0 ∧
                (wholeRestartAnchoredReflectedNextVelocityPairOccurrence
                      initial frame first
                        (outputNegSecondEquiv first second) ≠ 0 ∨
                  wholeRestartAnchoredReflectedVelocityPairOccurrenceTrace
                      initial frame first
                        (outputNegSecondEquiv first second) time ≠ 0) ∧
                run initial frame.next.currentIndex =
                  (run initial frame.currentIndex).next) := by
  by_cases outputNonnegative :
      0 ≤
        wholeRestartAnchoredCausalTangentVelocityWork
            initial frame wave +
          ∑' first : IntegerWavevector,
            wholeRestartAnchoredPairInnovationVelocityWork
              initial frame wave first
  · exact Or.inl outputNonnegative
  · apply Or.inr
    by_cases viscousNegative :
        wholeRestartAnchoredViscousHeatDisplacementVelocityWork
          initial frame wave < 0
    · exact Or.inl viscousNegative
    · apply Or.inr
      have outputNegative :
          wholeRestartAnchoredCausalTangentVelocityWork
                initial frame wave +
              ∑' first : IntegerWavevector,
                wholeRestartAnchoredPairInnovationVelocityWork
                  initial frame wave first < 0 :=
        lt_of_not_ge outputNonnegative
      have viscousNonnegative :
          0 ≤
            wholeRestartAnchoredViscousHeatDisplacementVelocityWork
              initial frame wave :=
        le_of_not_gt viscousNegative
      have outputCompiler :=
        two_mul_wholeRestartAnchoredOutputContribution_eq_viscousHeat_add_tsum_symmetricDirect
          initial frame wave
      have symmetricTsumNegative :
          (∑' first : IntegerWavevector,
              wholeRestartAnchoredSymmetricDirectDuhamelWork
                initial frame wave first) < 0 := by
        linarith
      have negativeSymmetricPair :
          ∃ first : IntegerWavevector,
            wholeRestartAnchoredSymmetricDirectDuhamelWork
              initial frame wave first < 0 := by
        by_contra noNegativePair
        push Not at noNegativePair
        have symmetricTsumNonnegative :
            0 ≤
              ∑' first : IntegerWavevector,
                wholeRestartAnchoredSymmetricDirectDuhamelWork
                  initial frame wave first :=
          tsum_nonneg noNegativePair
        linarith
      obtain ⟨first, symmetricNegative⟩ := negativeSymmetricPair
      let second : IntegerWavevector := wave.1 - first
      change
        wholeRestartAnchoredDirectVelocityBilinearEnergyWork
              initial frame first second +
            wholeRestartAnchoredDirectVelocityBilinearEnergyWork
              initial frame second first < 0 at symmetricNegative
      by_cases firstNegative :
          wholeRestartAnchoredDirectVelocityBilinearEnergyWork
            initial frame first second < 0
      · refine ⟨first, second, ?_, firstNegative, ?_⟩
        · dsimp [second]
          abel
        · exact
            wholeRestartAnchoredDirectVelocityBilinearEnergyWork_ne_zero_generates_nativePairResponsibility
              initial frame first second (ne_of_lt firstNegative)
      · have firstNonnegative :
            0 ≤
              wholeRestartAnchoredDirectVelocityBilinearEnergyWork
                initial frame first second :=
          le_of_not_gt firstNegative
        have secondNegative :
            wholeRestartAnchoredDirectVelocityBilinearEnergyWork
              initial frame second first < 0 := by
          linarith
        refine ⟨second, first, ?_, secondNegative, ?_⟩
        · dsimp [second]
          abel
        · exact
            wholeRestartAnchoredDirectVelocityBilinearEnergyWork_ne_zero_generates_nativePairResponsibility
              initial frame second first (ne_of_lt secondNegative)

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartAnchoredMixedWorkNativeCompiler
end NavierStokes
end SaturationMonoid
