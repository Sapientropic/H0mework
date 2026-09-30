import H0mework.NavierStokes.Restart.BoundedPreAccumulationPhysicalTrajectory
import H0mework.NavierStokes.KineticRestart.KineticDefectZeroAbsoluteStrongTrace
import H0mework.NavierStokes.Restart.WholeMildAssembly

/-!
# Full left velocity trace of a bounded whole-restart run

Every canonical restart receipt after the initial segment inherits a fixed-wave
physical-velocity Lipschitz modulus from the actual Galerkin extraction that
generated it.  Native kinetic monotonicity bounds all of those moduli by the
first contact.  This module telescopes the local estimates across the literal
finite-prefix splice and then uses the source-generated cofinal contact trace
to control the complete pre-accumulation path.

No cutoff, target path, continuation witness, or externally chosen modulus
enters the theorem mouths.

The local modulus, cross-join telescope, every-time kinetic tail bound, and
finite-projection completion remain together because each is a private proof
stage of the single public full-left-trace contract.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCriticalClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartMildClosure
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeMildAssembly
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDefectZeroVelocityCompletion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation

noncomputable section

/-! ## One canonical segment -/

/-- Every segment after the possibly arbitrary initial receipt is generated
from the preceding contact's canonical replay.  Its physical velocity row
therefore carries the preceding contact's source-owned speed ceiling. -/
theorem wholeRestartCanonicalContactPrefix_fixedWave_velocity_increment_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (first second :
      Icc (0 : ℝ) (run initial (index + 1)).contact.time.1) :
    dist
        (biotSavartVelocityCoefficient wave.1
          ((run initial (index + 1)).contact.prefixReceipt.wholePath
            first wave.1))
        (biotSavartVelocityCoefficient wave.1
          ((run initial (index + 1)).contact.prefixReceipt.wholePath
            second wave.1)) ≤
      wholeRestartFixedWaveVelocitySpeedCeiling
          (run initial index).contact wave.1 *
        dist first second := by
  let timeLe := (run initial index).nextContact.time.2.2
  let firstFull :
      Icc (0 : ℝ) (wholeRestartDuration (run initial index).contact) :=
    commonTimeInclusion timeLe first
  let secondFull :
      Icc (0 : ℝ) (wholeRestartDuration (run initial index).contact) :=
    commonTimeInclusion timeLe second
  let closure :=
    generatedWholeRestartCriticalClosure
      (generatedWholeRestartCanonicalReplay (run initial index).contact)
  have actual :=
    wholeRestartWholeMildAssembly_fixedWave_velocity_increment_le
      closure
      wave.1 wave.2 firstFull secondFull
  have firstPathEq :
      ((run initial (index + 1)).contact.prefixReceipt.wholePath
          first wave.1) =
        (wholeRestartWholeMildAssembly closure).wholePath
          firstFull wave.1 := by
    change
      (((wholeRestartWholeMildAssembly closure).wholePath.compContinuous
          (commonTimeInclusion _)) first) wave.1 = _
    rw [BoundedContinuousFunction.compContinuous_apply]
    apply congrArg
      (fun time =>
        (wholeRestartWholeMildAssembly closure).wholePath time wave.1)
    exact Subtype.ext rfl
  have secondPathEq :
      ((run initial (index + 1)).contact.prefixReceipt.wholePath
          second wave.1) =
        (wholeRestartWholeMildAssembly closure).wholePath
          secondFull wave.1 := by
    change
      (((wholeRestartWholeMildAssembly closure).wholePath.compContinuous
          (commonTimeInclusion _)) second) wave.1 = _
    rw [BoundedContinuousFunction.compContinuous_apply]
    apply congrArg
      (fun time =>
        (wholeRestartWholeMildAssembly closure).wholePath time wave.1)
    exact Subtype.ext rfl
  have timeDistEq : dist firstFull secondFull = dist first second := rfl
  rw [firstPathEq, secondPathEq]
  rw [timeDistEq] at actual
  exact actual

/-- Kinetic monotonicity turns the source-owned segment ceiling into one
fixed ceiling for the entire canonical tail of the native run. -/
theorem wholeRestartFixedWaveVelocitySpeedCeiling_run_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : IntegerWavevector) :
    wholeRestartFixedWaveVelocitySpeedCeiling
        (run initial index).contact wave ≤
      wholeRestartFixedWaveVelocitySpeedCeiling
        (run initial 0).contact wave := by
  unfold wholeRestartFixedWaveVelocitySpeedCeiling
  have massLe :=
    run_contact_kineticMass_antitone initial (Nat.zero_le index)
  have physicalMassLe :
      puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState (run initial index).contact) ≤
        puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState (run initial 0).contact) := by
    simpa only [
      wholeRestartPhysicalState_generatedPositiveWholeRestartContact] using
      massLe
  have angularNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) Real.pi_pos.le)
      (Real.sqrt_nonneg _)
  have multiplierNonneg :
      0 ≤ ν.coeff * integerWaveViscousMultiplier wave := by
    exact mul_nonneg ν.coeff_pos.le
      (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left physicalMassLe angularNonneg)
      (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (by linarith) multiplierNonneg)

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_canonicalSegment_coordinate_increment_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate)
    (first second :
      Icc (0 : ℝ) (run initial (index + 1)).contact.time.1) :
    dist
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded (index + 1) first)
          wave coordinate)
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded (index + 1) second)
          wave coordinate) ≤
      wholeRestartFixedWaveVelocitySpeedCeiling
          (run initial 0).contact wave.1 *
        dist first second := by
  let left : ComplexCoordinateVector :=
    biotSavartVelocityCoefficient wave.1
      ((run initial (index + 1)).contact.prefixReceipt.wholePath
        first wave.1)
  let right : ComplexCoordinateVector :=
    biotSavartVelocityCoefficient wave.1
      ((run initial (index + 1)).contact.prefixReceipt.wholePath
        second wave.1)
  have pathFirst :
      wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded (index + 1) first)
          wave coordinate =
        left coordinate := by
    unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart]
    rfl
  have pathSecond :
      wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded
          (wholeRestartReceiptPreAccumulationTime
            initial elapsedBounded (index + 1) second)
          wave coordinate =
        right coordinate := by
    unfold wholeRestartBoundedPreAccumulationVelocityTrajectory
    rw [wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart]
    rfl
  rw [pathFirst, pathSecond]
  calc
    dist (left coordinate) (right coordinate) ≤ dist left right := by
      rw [dist_eq_norm, dist_eq_norm]
      simpa only [Pi.sub_apply] using
        (norm_le_pi_norm (left - right) coordinate)
    _ ≤
        wholeRestartFixedWaveVelocitySpeedCeiling
            (run initial index).contact wave.1 *
          dist first second := by
      exact
        wholeRestartCanonicalContactPrefix_fixedWave_velocity_increment_le
          initial index wave first second
    _ ≤
        wholeRestartFixedWaveVelocitySpeedCeiling
            (run initial 0).contact wave.1 *
          dist first second := by
      exact mul_le_mul_of_nonneg_right
        (wholeRestartFixedWaveVelocitySpeedCeiling_run_le_initial
          initial index wave.1)
        dist_nonneg

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_canonicalWindow_coordinate_increment_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate)
    (first second :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial))
    (firstMem :
      first.1 ∈ Icc
        (elapsedTime initial (index + 1))
        (elapsedTime initial (index + 1 + 1)))
    (secondMem :
      second.1 ∈ Icc
        (elapsedTime initial (index + 1))
        (elapsedTime initial (index + 1 + 1))) :
    dist
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded first wave coordinate)
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded second wave coordinate) ≤
      wholeRestartFixedWaveVelocitySpeedCeiling
          (run initial 0).contact wave.1 *
        dist first second := by
  have firstUpper := firstMem.2
  have secondUpper := secondMem.2
  rw [elapsedTime_succ] at firstUpper secondUpper
  let firstLocal :
      Icc (0 : ℝ) (run initial (index + 1)).contact.time.1 :=
    ⟨first.1 - elapsedTime initial (index + 1), by
      constructor <;> linarith [firstMem.1, firstUpper]⟩
  let secondLocal :
      Icc (0 : ℝ) (run initial (index + 1)).contact.time.1 :=
    ⟨second.1 - elapsedTime initial (index + 1), by
      constructor <;> linarith [secondMem.1, secondUpper]⟩
  have firstTimeEq :
      wholeRestartReceiptPreAccumulationTime
          initial elapsedBounded (index + 1) firstLocal =
        first := by
    apply Subtype.ext
    rw [wholeRestartReceiptPreAccumulationTime_value]
    dsimp only [firstLocal]
    ring
  have secondTimeEq :
      wholeRestartReceiptPreAccumulationTime
          initial elapsedBounded (index + 1) secondLocal =
        second := by
    apply Subtype.ext
    rw [wholeRestartReceiptPreAccumulationTime_value]
    dsimp only [secondLocal]
    ring
  have localDistEq : dist firstLocal secondLocal = dist first second := by
    change
      dist
          (first.1 - elapsedTime initial (index + 1))
          (second.1 - elapsedTime initial (index + 1)) =
        dist first.1 second.1
    simp only [Real.dist_eq]
    congr 1
    ring
  have localEstimate :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_canonicalSegment_coordinate_increment_le
      initial elapsedBounded index wave coordinate firstLocal secondLocal
  rw [firstTimeEq, secondTimeEq, localDistEq] at localEstimate
  exact localEstimate

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_finiteTail_coordinate_increment_le_ordered
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    ∀ (length : ℕ)
      (first second :
        Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)),
      elapsedTime initial 1 ≤ first.1 →
      first.1 ≤ second.1 →
      second.1 ≤ elapsedTime initial (length + 1) →
      dist
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded first wave coordinate)
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded second wave coordinate) ≤
        wholeRestartFixedWaveVelocitySpeedCeiling
            (run initial 0).contact wave.1 *
          dist first second := by
  intro length
  induction length with
  | zero =>
      intro first second firstTail firstLeSecond secondUpper
      have secondBoundary :
          second.1 ≤ elapsedTime initial 1 := by
        simpa only [Nat.zero_add] using secondUpper
      have firstEqSecond : first = second := by
        apply Subtype.ext
        exact le_antisymm firstLeSecond (by linarith)
      subst second
      simp
  | succ length inductionHypothesis =>
      intro first second firstTail firstLeSecond secondUpper
      let join :=
        wholeRestartContactEndpointPreAccumulationTime
          initial elapsedBounded length
      have joinValue :
          join.1 = elapsedTime initial (length + 1) := rfl
      by_cases secondLeJoin : second.1 ≤ join.1
      · exact inductionHypothesis first second firstTail firstLeSecond (by
          simpa only [joinValue] using secondLeJoin)
      · have joinLtSecond : join.1 < second.1 := lt_of_not_ge secondLeJoin
        by_cases joinLeFirst : join.1 ≤ first.1
        · apply
            wholeRestartBoundedPreAccumulationVelocityTrajectory_canonicalWindow_coordinate_increment_le
              initial elapsedBounded length wave coordinate first second
          · constructor
            · simpa only [joinValue] using joinLeFirst
            · exact firstLeSecond.trans secondUpper
          · constructor
            · simpa only [joinValue] using joinLtSecond.le
            · exact secondUpper
        · have firstLtJoin : first.1 < join.1 := lt_of_not_ge joinLeFirst
          have leftEstimate :=
            inductionHypothesis first join firstTail firstLtJoin.le (by
              rw [joinValue])
          have rightEstimate :=
            wholeRestartBoundedPreAccumulationVelocityTrajectory_canonicalWindow_coordinate_increment_le
              initial elapsedBounded length wave coordinate join second
              ⟨by rw [joinValue], joinLtSecond.le.trans secondUpper⟩
              ⟨joinLtSecond.le, secondUpper⟩
          have distanceSplit :
              dist first join + dist join second = dist first second := by
            change
              dist first.1 join.1 + dist join.1 second.1 =
                dist first.1 second.1
            rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
              abs_of_nonpos (sub_nonpos.mpr firstLtJoin.le),
              abs_of_nonpos (sub_nonpos.mpr joinLtSecond.le),
              abs_of_nonpos (sub_nonpos.mpr firstLeSecond)]
            ring
          calc
            dist
                (wholeRestartBoundedPreAccumulationVelocityTrajectory
                  initial elapsedBounded first wave coordinate)
                (wholeRestartBoundedPreAccumulationVelocityTrajectory
                  initial elapsedBounded second wave coordinate) ≤
                dist
                    (wholeRestartBoundedPreAccumulationVelocityTrajectory
                      initial elapsedBounded first wave coordinate)
                    (wholeRestartBoundedPreAccumulationVelocityTrajectory
                      initial elapsedBounded join wave coordinate) +
                  dist
                    (wholeRestartBoundedPreAccumulationVelocityTrajectory
                      initial elapsedBounded join wave coordinate)
                    (wholeRestartBoundedPreAccumulationVelocityTrajectory
                      initial elapsedBounded second wave coordinate) :=
              dist_triangle _ _ _
            _ ≤
                wholeRestartFixedWaveVelocitySpeedCeiling
                      (run initial 0).contact wave.1 *
                    dist first join +
                  wholeRestartFixedWaveVelocitySpeedCeiling
                      (run initial 0).contact wave.1 *
                    dist join second :=
              add_le_add leftEstimate rightEstimate
            _ =
                wholeRestartFixedWaveVelocitySpeedCeiling
                    (run initial 0).contact wave.1 *
                  (dist first join + dist join second) := by ring
            _ =
                wholeRestartFixedWaveVelocitySpeedCeiling
                    (run initial 0).contact wave.1 *
                  dist first second := by rw [distanceSplit]

/-! ## Complete pre-accumulation tail -/

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_norm_sq_le_contactMass_tail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ)
    (time : Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial))
    (indexTail : elapsedTime initial (index + 1) < time.1) :
    ‖wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded time‖ ^ 2 ≤
      wholeRestartContactKineticMass initial index := by
  let cover :=
    wholeRestartPreAccumulationCoverIndex initial elapsedBounded time
  have elapsedOnePos : 0 < elapsedTime initial 1 := by
    simpa only [elapsedTime_zero] using
      elapsedTime_strictMono initial (Nat.zero_lt_one)
  have timePos : 0 < time.1 := by
    have oneLeIndexSucc : 1 ≤ index + 1 :=
      Nat.succ_le_succ (Nat.zero_le index)
    exact
      (elapsedOnePos.trans_le
        ((elapsedTime_strictMono initial).monotone oneLeIndexSucc)).trans
          indexTail
  have timeLeCover : time.1 ≤ elapsedTime initial cover :=
    (wholeRestartPreAccumulationCoverIndex_spec
      initial elapsedBounded time).le
  obtain ⟨window, windowSpec, _windowUnique⟩ :=
    wholeRestartPhysicalWindow_existsUnique initial
      (length := cover) ⟨timePos, timeLeCover⟩
  have indexSuccLeWindow : index + 1 ≤ window := by
    by_contra indexSuccNotLe
    have windowLeIndex : window ≤ index := Nat.lt_succ_iff.mp <|
      Nat.lt_of_not_ge indexSuccNotLe
    have windowEndpointLeIndexEndpoint :
        elapsedTime initial (window + 1) ≤
          elapsedTime initial (index + 1) :=
      (elapsedTime_strictMono initial).monotone
        (Nat.succ_le_succ windowLeIndex)
    exact (not_lt_of_ge <|
      windowSpec.2.2.trans windowEndpointLeIndexEndpoint) indexTail
  obtain ⟨previous, windowEq⟩ : ∃ previous, window = previous + 1 := by
    exact ⟨window - 1, by omega⟩
  subst window
  have indexLePrevious : index ≤ previous := by omega
  have windowUpper := windowSpec.2.2
  rw [elapsedTime_succ] at windowUpper
  let localTime : Icc (0 : ℝ) (run initial (previous + 1)).contact.time.1 :=
    ⟨time.1 - elapsedTime initial (previous + 1), by
      constructor
      · linarith [windowSpec.2.1]
      · linarith [windowUpper]⟩
  have absoluteTimeEq :
      wholeRestartReceiptPreAccumulationTime
          initial elapsedBounded (previous + 1) localTime =
        time := by
    apply Subtype.ext
    rw [wholeRestartReceiptPreAccumulationTime_value]
    dsimp only [localTime]
    ring
  let closure :=
    generatedWholeRestartCriticalClosure
      (generatedWholeRestartCanonicalReplay (run initial previous).contact)
  let timeLe := (run initial previous).nextContact.time.2.2
  let fullTime :
      Icc (0 : ℝ) (wholeRestartDuration (run initial previous).contact) :=
    commonTimeInclusion timeLe localTime
  have pathEq :
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time =
        (wholeRestartWholeMildAssembly closure).wholePath fullTime := by
    calc
      wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time =
        (run initial (previous + 1)).contact.prefixReceipt.wholePath
          localTime := by
        rw [← absoluteTimeEq]
        exact
          wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_receipt_chart
            initial elapsedBounded (previous + 1) localTime
      _ = (wholeRestartWholeMildAssembly closure).wholePath fullTime := by
        change
          (((wholeRestartWholeMildAssembly closure).wholePath.compContinuous
              (commonTimeInclusion _)) localTime) = _
        rw [BoundedContinuousFunction.compContinuous_apply]
        apply congrArg
          (fun currentTime =>
            (wholeRestartWholeMildAssembly closure).wholePath currentTime)
        exact Subtype.ext rfl
  change
    ‖puncturedWholeVelocityEuclideanState
        (wholeRestartBoundedPreAccumulationPhysicalTrajectory
          initial elapsedBounded time)‖ ^ 2 ≤ _
  rw [pathEq]
  calc
    ‖puncturedWholeVelocityEuclideanState
        ((wholeRestartWholeMildAssembly closure).wholePath fullTime)‖ ^ 2 ≤
        puncturedWholeVorticityKineticMass
          ((wholeRestartWholeMildAssembly closure).wholePath fullTime) :=
      puncturedWholeVelocityEuclideanState_norm_sq_le_kineticMass _
    _ ≤ puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState (run initial previous).contact) :=
      wholeRestartWholePath_kineticMass_le closure fullTime
    _ ≤ puncturedWholeVorticityKineticMass
          (wholeRestartPhysicalState (run initial index).contact) := by
      exact run_contact_kineticMass_antitone initial indexLePrevious
    _ = wholeRestartContactKineticMass initial index := by
      unfold wholeRestartContactKineticMass
      unfold wholeRestartContactKineticState
      exact
        (puncturedWholeVorticityKineticEuclideanState_norm_sq _).symm

private def wholeRestartVelocityFiniteProjection
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    WholeRestartVelocityEndpointState :=
  ∑ wave ∈ modes, lp.single 2 wave (state wave)

private def wholeRestartVelocityFiniteTail
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    WholeRestartVelocityEndpointState :=
  state - wholeRestartVelocityFiniteProjection modes state

private theorem wholeRestartVelocityFiniteTail_norm_sq
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartVelocityEndpointState) :
    ‖wholeRestartVelocityFiniteTail modes state‖ ^ 2 =
      ‖state‖ ^ 2 -
        ‖wholeRestartVelocityFiniteProjection modes state‖ ^ 2 := by
  classical
  have complementEq :=
    lp.norm_compl_sum_single
      (p := (2 : ENNReal)) (by norm_num) state modes
  have projectionEq :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave => state wave) modes
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at complementEq projectionEq
  calc
    ‖wholeRestartVelocityFiniteTail modes state‖ ^ 2 =
        ‖state‖ ^ 2 - ∑ wave ∈ modes, ‖state wave‖ ^ 2 := by
      simpa only [wholeRestartVelocityFiniteTail,
        wholeRestartVelocityFiniteProjection] using complementEq
    _ = ‖state‖ ^ 2 -
        ‖wholeRestartVelocityFiniteProjection modes state‖ ^ 2 := by
      simpa only [wholeRestartVelocityFiniteProjection] using
        congrArg (fun value => ‖state‖ ^ 2 - value) projectionEq.symm

private theorem wholeRestartContactVelocityState_norm_sq_eq_contactMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    ‖wholeRestartContactVelocityState initial index‖ ^ 2 =
      wholeRestartContactKineticMass initial index := by
  calc
    ‖wholeRestartContactVelocityState initial index‖ ^ 2 =
        puncturedWholeVorticityKineticMass
          (run initial index).contact.physicalState :=
      wholeRestartContactVelocityState_norm_sq initial index
    _ = ‖wholeRestartContactKineticState initial index‖ ^ 2 := by
      unfold wholeRestartContactKineticState
      exact
        (puncturedWholeVorticityKineticEuclideanState_norm_sq _).symm
    _ = wholeRestartContactKineticMass initial index := rfl

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_norm_sq_eventually_lt_massLimit_add
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (epsilon : ℝ)
    (epsilonPos : 0 < epsilon) :
    ∀ᶠ time : Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)
      in atTop,
      ‖wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time‖ ^ 2 <
        wholeRestartKineticMassLimit initial + epsilon := by
  obtain ⟨index, massClose⟩ :=
    (Metric.tendsto_atTop.mp
      (wholeRestartContactKineticMass_tendsto_limit initial))
      epsilon epsilonPos
  have massAtIndexLt :
      wholeRestartContactKineticMass initial index <
        wholeRestartKineticMassLimit initial + epsilon := by
    have close := massClose index le_rfl
    rw [Real.dist_eq, abs_lt] at close
    linarith [close.2]
  let threshold :=
    wholeRestartContactEndpointPreAccumulationTime
      initial elapsedBounded (index + 1)
  filter_upwards [eventually_ge_atTop threshold] with time thresholdLeTime
  have indexTail : elapsedTime initial (index + 1) < time.1 := by
    have strictStep :
        elapsedTime initial (index + 1) <
          elapsedTime initial (index + 1 + 1) :=
      elapsedTime_strictMono initial (Nat.lt_succ_self (index + 1))
    exact strictStep.trans_le thresholdLeTime
  exact
    (wholeRestartBoundedPreAccumulationVelocityTrajectory_norm_sq_le_contactMass_tail
      initial elapsedBounded index time indexTail).trans_lt massAtIndexLt

private theorem
    generatedWholeRestartVelocityEndpoint_norm_sq_eq_massLimit_of_kineticDefect_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    ‖ledger.family.endpointReceipt.velocityEndpoint‖ ^ 2 =
      wholeRestartKineticMassLimit initial := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let selected := weak.subsequence
  have contactStrong :
      Tendsto
        (fun index =>
          wholeRestartContactVelocityState initial (selected index))
        atTop
        (nhds weak.velocityEndpoint) := by
    exact
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.velocity_strong_tendsto_of_kineticDefect_eq_zero
        weak defectZero
  have normSqToEndpoint :
      Tendsto
        (fun index =>
          ‖wholeRestartContactVelocityState initial (selected index)‖ ^ 2)
        atTop
        (nhds (‖weak.velocityEndpoint‖ ^ 2)) :=
    contactStrong.norm.pow 2
  have massToLimit :
      Tendsto
        (fun index =>
          wholeRestartContactKineticMass initial (selected index))
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [selected,
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
      Function.comp_def] using
      weak.kineticReceipt.mass_tendsto.comp
        weak.velocitySubsubsequence_strictMono.tendsto_atTop
  have normSqToLimit :
      Tendsto
        (fun index =>
          ‖wholeRestartContactVelocityState initial (selected index)‖ ^ 2)
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    convert massToLimit using 1
    funext index
    exact
      wholeRestartContactVelocityState_norm_sq_eq_contactMass
        initial (selected index)
  exact tendsto_nhds_unique normSqToEndpoint normSqToLimit

/-- After the first possibly arbitrary source receipt, every physical
velocity Fourier coordinate of the complete bounded pre-accumulation path is
globally Lipschitz with one source-generated constant.  The estimate has
already telescoped every actual restart join, so overlapping restart charts
cannot charge the same physical interval twice. -/
theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_increment_le_tail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate)
    (first second :
      Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial))
    (firstTail : elapsedTime initial 1 ≤ first.1)
    (secondTail : elapsedTime initial 1 ≤ second.1) :
    dist
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded first wave coordinate)
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded second wave coordinate) ≤
      wholeRestartFixedWaveVelocitySpeedCeiling
          (run initial 0).contact wave.1 *
        dist first second := by
  rcases le_total first.1 second.1 with firstLeSecond | secondLeFirst
  · let length :=
      wholeRestartPreAccumulationCoverIndex
        initial elapsedBounded second
    have secondUpper :
        second.1 ≤ elapsedTime initial (length + 1) :=
      (wholeRestartPreAccumulationCoverIndex_spec
          initial elapsedBounded second).le.trans
        ((elapsedTime_strictMono initial).monotone
          (Nat.le_succ length))
    exact
      wholeRestartBoundedPreAccumulationVelocityTrajectory_finiteTail_coordinate_increment_le_ordered
        initial elapsedBounded wave coordinate length first second
        firstTail firstLeSecond secondUpper
  · let length :=
      wholeRestartPreAccumulationCoverIndex
        initial elapsedBounded first
    have firstUpper :
        first.1 ≤ elapsedTime initial (length + 1) :=
      (wholeRestartPreAccumulationCoverIndex_spec
          initial elapsedBounded first).le.trans
        ((elapsedTime_strictMono initial).monotone
          (Nat.le_succ length))
    have swapped :=
      wholeRestartBoundedPreAccumulationVelocityTrajectory_finiteTail_coordinate_increment_le_ordered
        initial elapsedBounded wave coordinate length second first
        secondTail secondLeFirst firstUpper
    simpa only [dist_comm] using swapped

/-- The source-generated Hilbert-weak endpoint already determines the
complete left trace of every fixed physical velocity Fourier coordinate.
The source's own contact subsequence is used only inside the proof; no
kinetic-defect branch is needed for this coordinate-level interface. -/
theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    Tendsto
      (fun time =>
        wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time wave coordinate)
      atTop
      (nhds (weak.velocityEndpoint wave coordinate)) := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let selected := weak.subsequence
  let accumulationTime := wholeRestartVelocityAccumulationTime initial
  let speedCeiling :=
    wholeRestartFixedWaveVelocitySpeedCeiling
      (run initial 0).contact wave.1
  let initialEndpointTime :=
    wholeRestartContactEndpointPreAccumulationTime
      initial elapsedBounded 0
  change
    Tendsto
      (fun time =>
        wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time wave coordinate)
      atTop
      (nhds (weak.velocityEndpoint wave coordinate))
  letI : Nonempty (Ico (0 : ℝ) accumulationTime) :=
    ⟨initialEndpointTime⟩
  have contactCoordinateTendsto :
      Tendsto
        (fun index =>
          wholeRestartContactVelocityState initial (selected index)
            wave coordinate)
        atTop
        (nhds (weak.velocityEndpoint wave coordinate)) := by
    exact
      velocityWeakTendsto_coordinate
        (fun index =>
          wholeRestartContactVelocityState initial (selected index))
        weak.velocityEndpoint
        weak.velocity_weak_tendsto_shared
        wave coordinate
  let continuation :=
    sourceGeneratedWholeRestartVelocityEndpointAbsoluteWholeMildNativeContinuation
      initial elapsedBounded
  have endpointTimeTendsto :
      Tendsto
        (fun index => elapsedTime initial (selected index + 1))
        atTop
        (nhds accumulationTime) := by
    simpa only [ledger, weak, selected, accumulationTime] using
      continuation.prefixEndpointTime_tendsto
  have gapTendsto :
      Tendsto
        (fun index =>
          speedCeiling *
            dist (elapsedTime initial (selected index + 1)) accumulationTime)
        atTop
        (nhds 0) := by
    have distanceTendsto :=
      endpointTimeTendsto.dist
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => accumulationTime) atTop
            (nhds accumulationTime))
    have multiplied :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => speedCeiling) atTop
          (nhds speedCeiling)).mul distanceTendsto
    simpa only [dist_self, mul_zero] using multiplied
  rw [Metric.tendsto_atTop]
  intro epsilon epsilonPos
  have halfPos : 0 < epsilon / 2 := by linarith
  obtain ⟨coordinateThreshold, coordinateClose⟩ :=
    (Metric.tendsto_atTop.mp contactCoordinateTendsto)
      (epsilon / 2) halfPos
  obtain ⟨gapThreshold, gapClose⟩ :=
    (Metric.tendsto_atTop.mp gapTendsto) (epsilon / 2) halfPos
  let index := max coordinateThreshold gapThreshold
  let anchor :=
    wholeRestartContactEndpointPreAccumulationTime
      initial elapsedBounded (selected index)
  refine ⟨anchor, ?_⟩
  intro time anchorLeTime
  have anchorTail : elapsedTime initial 1 ≤ anchor.1 := by
    change
      elapsedTime initial 1 ≤
        elapsedTime initial (selected index + 1)
    exact
      (elapsedTime_strictMono initial).monotone (by omega)
  have timeTail : elapsedTime initial 1 ≤ time.1 :=
    anchorTail.trans anchorLeTime
  have pathIncrement :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_increment_le_tail
      initial elapsedBounded wave coordinate time anchor timeTail anchorTail
  have speedCeilingNonneg : 0 ≤ speedCeiling := by
    exact wholeRestartFixedWaveVelocitySpeedCeiling_nonneg
      (run initial 0).contact wave.1
  have timeDistanceLe :
      dist time anchor ≤
        dist (elapsedTime initial (selected index + 1)) accumulationTime := by
    have anchorLeTimeValue : anchor.1 ≤ time.1 := anchorLeTime
    have elapsedLeTime :
        elapsedTime initial (selected index + 1) ≤ time.1 := by
      exact anchorLeTimeValue
    have elapsedLeAccumulation :
        elapsedTime initial (selected index + 1) ≤ accumulationTime := by
      exact anchor.2.2.le
    change
      dist time.1 (elapsedTime initial (selected index + 1)) ≤
        dist (elapsedTime initial (selected index + 1)) accumulationTime
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr elapsedLeTime),
      abs_of_nonpos (sub_nonpos.mpr elapsedLeAccumulation)]
    linarith [time.2.2]
  have gapAtIndex :
      speedCeiling *
          dist (elapsedTime initial (selected index + 1)) accumulationTime <
        epsilon / 2 := by
    have closeAtIndex :=
      gapClose index (Nat.le_max_right _ _)
    have gapNonneg :
        0 ≤ speedCeiling *
          dist (elapsedTime initial (selected index + 1)) accumulationTime :=
      mul_nonneg speedCeilingNonneg dist_nonneg
    simpa only [dist_zero_right, Real.norm_of_nonneg gapNonneg] using
      closeAtIndex
  have pathIncrementLt :
      dist
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded time wave coordinate)
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded anchor wave coordinate) <
        epsilon / 2 :=
    pathIncrement.trans_lt <|
      (mul_le_mul_of_nonneg_left timeDistanceLe speedCeilingNonneg).trans_lt
        gapAtIndex
  have anchorValue :
      wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded anchor =
        wholeRestartContactVelocityState initial (selected index) := by
    exact
      wholeRestartBoundedPreAccumulationVelocityTrajectory_contactEndpoint
        initial elapsedBounded (selected index)
  have anchorClose :
      dist
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded anchor wave coordinate)
          (weak.velocityEndpoint wave coordinate) <
        epsilon / 2 := by
    rw [anchorValue]
    exact coordinateClose index (Nat.le_max_left _ _)
  calc
    dist
        (wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time wave coordinate)
        (weak.velocityEndpoint wave coordinate) ≤
        dist
            (wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded time wave coordinate)
            (wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded anchor wave coordinate) +
          dist
            (wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded anchor wave coordinate)
            (weak.velocityEndpoint wave coordinate) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 :=
      add_lt_add pathIncrementLt anchorClose
    _ = epsilon := by ring

/-- Compatibility form of the coordinate trace theorem.  Vanishing kinetic
defect is needed only for the later whole-`L²` upgrade, not for a fixed
Fourier-coordinate trace. -/
theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint_of_kineticDefect_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (_defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0)
    (wave : NonzeroIntegerWavevector)
    (coordinate : Coordinate) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    Tendsto
      (fun time =>
        wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time wave coordinate)
      atTop
      (nhds (weak.velocityEndpoint wave coordinate)) :=
  wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint
    initial elapsedBounded wave coordinate

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_fixedWave_tendsto_endpoint_of_kineticDefect_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0)
    (wave : NonzeroIntegerWavevector) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    Tendsto
      (fun time =>
        wholeRestartBoundedPreAccumulationVelocityTrajectory
          initial elapsedBounded time wave)
      atTop
      (nhds (weak.velocityEndpoint wave)) := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  have coordinateTendsto :
      ∀ coordinate : Coordinate,
        Tendsto
          (fun time =>
            wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded time wave coordinate)
          atTop
          (nhds (weak.velocityEndpoint wave coordinate)) := by
    intro coordinate
    exact
      wholeRestartBoundedPreAccumulationVelocityTrajectory_coordinate_tendsto_endpoint_of_kineticDefect_eq_zero
        initial elapsedBounded defectZero wave coordinate
  have functionTendsto :
      Tendsto
        (fun time =>
          WithLp.ofLp
            (wholeRestartBoundedPreAccumulationVelocityTrajectory
              initial elapsedBounded time wave))
        atTop
        (nhds (WithLp.ofLp (weak.velocityEndpoint wave))) :=
    tendsto_pi_nhds.mpr coordinateTendsto
  have lifted :
      Tendsto
        (fun time =>
          WithLp.toLp 2 <|
            WithLp.ofLp
              (wholeRestartBoundedPreAccumulationVelocityTrajectory
                initial elapsedBounded time wave))
        atTop
        (nhds (WithLp.toLp 2 <| WithLp.ofLp (weak.velocityEndpoint wave))) :=
    (PiLp.continuous_toLp
      (p := (2 : ENNReal))
      (β := fun _ : Coordinate => ℂ)).tendsto
        (WithLp.ofLp (weak.velocityEndpoint wave))
      |>.comp functionTendsto
  simpa only [WithLp.toLp_ofLp] using lifted

private theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_finiteProjection_tendsto_endpoint_of_kineticDefect_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (defectZero :
      wholeRestartKineticWeakEndpointDefect initial
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          initial elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint =
        0)
    (modes : Finset NonzeroIntegerWavevector) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        initial elapsedBounded
    let weak := ledger.family.endpointReceipt
    Tendsto
      (fun time =>
        wholeRestartVelocityFiniteProjection modes
          (wholeRestartBoundedPreAccumulationVelocityTrajectory
            initial elapsedBounded time))
      atTop
      (nhds
        (wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint)) := by
  classical
  dsimp only
  unfold wholeRestartVelocityFiniteProjection
  apply tendsto_finsetSum modes
  intro wave _waveMem
  exact
    (lp.singleContinuousLinearMap
      ℂ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean)
      2 wave).continuous.tendsto _ |>.comp
        (wholeRestartBoundedPreAccumulationVelocityTrajectory_fixedWave_tendsto_endpoint_of_kineticDefect_eq_zero
          initial elapsedBounded defectZero wave)

/-- Vanishing of the source-generated kinetic defect upgrades the complete
bounded pre-accumulation velocity path, not merely its selected contact
subsequence or finite Fourier readouts, to a strong left trace at the
generated endpoint.  The proof consumes the every-time kinetic ledger before
the finite-observation quotient and therefore introduces no cutoff or tail
smallness premise. -/
theorem
    wholeRestartBoundedPreAccumulationVelocityTrajectory_tendsto_endpoint_of_kineticDefect_eq_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
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
    Tendsto
      (wholeRestartBoundedPreAccumulationVelocityTrajectory
        initial elapsedBounded)
      atTop
      (nhds weak.velocityEndpoint) := by
  classical
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      initial elapsedBounded
  let weak := ledger.family.endpointReceipt
  let trajectory :=
    wholeRestartBoundedPreAccumulationVelocityTrajectory
      initial elapsedBounded
  letI : Nonempty
      (Ico (0 : ℝ) (wholeRestartVelocityAccumulationTime initial)) :=
    ⟨wholeRestartContactEndpointPreAccumulationTime
      initial elapsedBounded 0⟩
  have finiteProjectionTendsto
      (modes : Finset NonzeroIntegerWavevector) :
      Tendsto
        (fun time =>
          wholeRestartVelocityFiniteProjection modes (trajectory time))
        atTop
        (nhds
          (wholeRestartVelocityFiniteProjection modes
            weak.velocityEndpoint)) := by
    exact
      wholeRestartBoundedPreAccumulationVelocityTrajectory_finiteProjection_tendsto_endpoint_of_kineticDefect_eq_zero
        initial elapsedBounded defectZero modes
  have endpointNormSqEq :
      ‖weak.velocityEndpoint‖ ^ 2 =
        wholeRestartKineticMassLimit initial := by
    exact
      generatedWholeRestartVelocityEndpoint_norm_sq_eq_massLimit_of_kineticDefect_eq_zero
        initial elapsedBounded defectZero
  have normSqUpper
      (delta : ℝ)
      (deltaPos : 0 < delta) :
      ∀ᶠ time in atTop,
        ‖trajectory time‖ ^ 2 < ‖weak.velocityEndpoint‖ ^ 2 + delta := by
    have upper :=
      wholeRestartBoundedPreAccumulationVelocityTrajectory_norm_sq_eventually_lt_massLimit_add
        initial elapsedBounded delta deltaPos
    rw [← endpointNormSqEq] at upper
    exact upper
  have endpointProjectionTendsto :
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint)
        atTop
        (nhds weak.velocityEndpoint) := by
    change
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          ∑ wave ∈ modes, lp.single 2 wave (weak.velocityEndpoint wave))
        atTop
        (nhds weak.velocityEndpoint)
    exact
      lp.hasSum_single
        (p := (2 : ENNReal)) (by norm_num) weak.velocityEndpoint
  have endpointTailTendsto :
      Tendsto
        (fun modes : Finset NonzeroIntegerWavevector =>
          wholeRestartVelocityFiniteTail modes weak.velocityEndpoint)
        atTop
        (nhds 0) := by
    have constantTendsto :
        Tendsto
          (fun _ : Finset NonzeroIntegerWavevector => weak.velocityEndpoint)
          atTop
          (nhds weak.velocityEndpoint) :=
      tendsto_const_nhds
    have difference :=
      constantTendsto.sub endpointProjectionTendsto
    simpa only [wholeRestartVelocityFiniteTail, sub_self] using difference
  change Tendsto trajectory atTop (nhds weak.velocityEndpoint)
  rw [Metric.tendsto_nhds]
  intro epsilon epsilonPos
  let quarter := epsilon / 4
  let half := epsilon / 2
  let delta := epsilon ^ 2 / 32
  have quarterPos : 0 < quarter := by
    dsimp only [quarter]
    positivity
  have halfPos : 0 < half := by
    dsimp only [half]
    positivity
  have deltaPos : 0 < delta := by
    dsimp only [delta]
    positivity
  have endpointTailEventually :
      ∀ᶠ modes : Finset NonzeroIntegerWavevector in atTop,
        ‖wholeRestartVelocityFiniteTail modes weak.velocityEndpoint‖ <
          quarter := by
    have close :=
      (Metric.tendsto_nhds.mp endpointTailTendsto) quarter quarterPos
    filter_upwards [close] with modes modesClose
    simpa only [dist_zero_right] using modesClose
  obtain ⟨modes, endpointTailSmall⟩ := endpointTailEventually.exists
  have headEventually :
      ∀ᶠ time in atTop,
        dist
            (wholeRestartVelocityFiniteProjection modes (trajectory time))
            (wholeRestartVelocityFiniteProjection modes
              weak.velocityEndpoint) <
          quarter :=
    (Metric.tendsto_nhds.mp (finiteProjectionTendsto modes))
      quarter quarterPos
  have projectionSquareTendsto :
      Tendsto
        (fun time =>
          ‖wholeRestartVelocityFiniteProjection modes (trajectory time)‖ ^ 2)
        atTop
        (nhds
          (‖wholeRestartVelocityFiniteProjection modes
              weak.velocityEndpoint‖ ^ 2)) :=
    (finiteProjectionTendsto modes).norm.pow 2
  have projectionSquareEventually :
      ∀ᶠ time in atTop,
        dist
            (‖wholeRestartVelocityFiniteProjection modes
                (trajectory time)‖ ^ 2)
            (‖wholeRestartVelocityFiniteProjection modes
                weak.velocityEndpoint‖ ^ 2) <
          delta :=
    (Metric.tendsto_nhds.mp projectionSquareTendsto) delta deltaPos
  filter_upwards [headEventually, projectionSquareEventually,
    normSqUpper delta deltaPos] with
      time headSmall projectionSquareClose totalSquareUpper
  have projectionSquareLower :
      ‖wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint‖ ^ 2 -
          delta <
        ‖wholeRestartVelocityFiniteProjection modes (trajectory time)‖ ^ 2 := by
    rw [Real.dist_eq, abs_lt] at projectionSquareClose
    linarith [projectionSquareClose.1]
  have endpointTailSquareSmall :
      ‖wholeRestartVelocityFiniteTail modes weak.velocityEndpoint‖ ^ 2 <
        quarter ^ 2 := by
    nlinarith [norm_nonneg
      (wholeRestartVelocityFiniteTail modes weak.velocityEndpoint)]
  have trajectoryTailSquareSmall :
      ‖wholeRestartVelocityFiniteTail modes (trajectory time)‖ ^ 2 <
        half ^ 2 := by
    have trajectoryTailIdentity :=
      wholeRestartVelocityFiniteTail_norm_sq modes (trajectory time)
    have endpointTailIdentity :=
      wholeRestartVelocityFiniteTail_norm_sq modes weak.velocityEndpoint
    dsimp only [delta, quarter, half] at totalSquareUpper
    dsimp only [delta, quarter, half] at projectionSquareLower
    dsimp only [delta, quarter, half] at endpointTailSquareSmall
    dsimp only [delta, quarter, half]
    nlinarith
  have trajectoryTailSmall :
      ‖wholeRestartVelocityFiniteTail modes (trajectory time)‖ < half := by
    nlinarith [norm_nonneg
      (wholeRestartVelocityFiniteTail modes (trajectory time))]
  have decomposition :
      trajectory time - weak.velocityEndpoint =
        (wholeRestartVelocityFiniteProjection modes (trajectory time) -
            wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint) +
          (wholeRestartVelocityFiniteTail modes (trajectory time) -
            wholeRestartVelocityFiniteTail modes weak.velocityEndpoint) := by
    unfold wholeRestartVelocityFiniteTail
    abel
  rw [dist_eq_norm, decomposition]
  calc
    ‖(wholeRestartVelocityFiniteProjection modes (trajectory time) -
          wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint) +
        (wholeRestartVelocityFiniteTail modes (trajectory time) -
          wholeRestartVelocityFiniteTail modes weak.velocityEndpoint)‖ ≤
        ‖wholeRestartVelocityFiniteProjection modes (trajectory time) -
          wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint‖ +
        ‖wholeRestartVelocityFiniteTail modes (trajectory time) -
          wholeRestartVelocityFiniteTail modes weak.velocityEndpoint‖ :=
      norm_add_le _ _
    _ ≤
        ‖wholeRestartVelocityFiniteProjection modes (trajectory time) -
          wholeRestartVelocityFiniteProjection modes weak.velocityEndpoint‖ +
          (‖wholeRestartVelocityFiniteTail modes (trajectory time)‖ +
            ‖wholeRestartVelocityFiniteTail modes weak.velocityEndpoint‖) :=
      add_le_add le_rfl (norm_sub_le _ _)
    _ < quarter + (half + quarter) := by
      rw [dist_eq_norm] at headSmall
      exact add_lt_add headSmall
        (add_lt_add trajectoryTailSmall endpointTailSmall)
    _ = epsilon := by
      dsimp only [quarter, half]
      ring

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
end NavierStokes
end SaturationMonoid
