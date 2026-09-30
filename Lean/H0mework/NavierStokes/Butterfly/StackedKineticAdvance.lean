import H0mework.NavierStokes.Butterfly.StackedSourceCurrent
import H0mework.NavierStokes.Accumulation.WholeReceiptKineticTimeModulus
import H0mework.NavierStokes.Accumulation.NativeFluidMediumRoot
import H0mework.NavierStokes.Accumulation.StandingValuedKineticPayment

/-!
# Kinetic-ledger advance of the stacked butterfly current

The complete kinetic time modulus removes the coarse whole-vorticity tail
from the first stacked current.  Its canonical seventh-order horizon is then
small enough that the actual full-receipt tangent cannot lose one unit of
the two source-generated sideband work margins.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace ButterflyStackedKineticAdvance

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open ButterflyStackedExpansionMaterial
open ButterflyStackedSourceCurrent
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot

noncomputable section

theorem butterflyGainKernelRadiusSlope_eq :
    sourceOwnedLocalKernelRadiusSlope butterflyGainViscosity = 2080000 := by
  unfold sourceOwnedLocalKernelRadiusSlope biotSavartSerrinConstant
    butterflyGainViscosity
  field_simp [Real.pi_ne_zero]
  norm_num

theorem butterflyGainSeventhCoefficient_eq :
    sourceOwnedWholeStateBarrierSeventhCoefficient butterflyGainViscosity =
      100 * (2080000 : Real) ^ 5 / 81 := by
  unfold sourceOwnedWholeStateBarrierSeventhCoefficient
    sourceOwnedLocalQuadraticFifthCoefficient
  rw [butterflyGainKernelRadiusSlope_eq]
  unfold biotSavartSerrinConstant butterflyGainViscosity
  field_simp [Real.pi_ne_zero]

theorem stackedShortCurrent_duration_lt_inverse_ten_pow_forty :
    wholeRestartDuration stackedShortCurrent.contact <
      1 / (10 : Real) ^ 40 := by
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier
    stackedShortCurrent
  rw [stackedShortCurrent_ceiling_eq_eighty_eight,
    butterflyGainSeventhCoefficient_eq] at durationLe
  exact durationLe.trans_lt (by norm_num)

theorem butterflyGain_cubicTangentConstant_lt_two_billion :
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (butterflyGainViscosity.coeff ^ 2 *
          (2 * Real.pi) ^ 2)) <
      (2000000000 : Real) := by
  unfold biotSavartSerrinConstant butterflyGainViscosity
  have denominatorPos :
      0 < 2 * ((((1 / 100 : Real) / (2 * Real.pi) ^ 2) ^ 2) *
        (2 * Real.pi) ^ 2) := by positivity
  apply (div_lt_iff₀ denominatorPos).2
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

theorem butterflyGain_viscosity_mul_eighty_eight_lt_one :
    butterflyGainViscosity.coeff * 88 < (1 : Real) := by
  unfold butterflyGainViscosity
  have piSq : (9 : Real) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have denominatorPos : 0 < (2 * Real.pi) ^ 2 := by positivity
  rw [show ((1 / 100 : Real) / (2 * Real.pi) ^ 2) * 88 =
      (88 / 100 : Real) / (2 * Real.pi) ^ 2 by ring]
  apply (div_lt_iff₀ denominatorPos).2
  nlinarith

theorem stackedShortCurrent_wholeTangentSourceUpper_lt_two :
    fullReplayWholeTangentSquareSourceUpper stackedShortCurrent < 2 := by
  have cubicLt := butterflyGain_cubicTangentConstant_lt_two_billion
  have durationLt :=
    stackedShortCurrent_duration_lt_inverse_ten_pow_forty
  have viscosityLt := butterflyGain_viscosity_mul_eighty_eight_lt_one
  unfold fullReplayWholeTangentSquareSourceUpper
  rw [stackedShortCurrent_ceiling_eq_eighty_eight]
  have cubicCoefficientNonneg :
      0 ≤ (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (butterflyGainViscosity.coeff ^ 2 *
          (2 * Real.pi) ^ 2)) := by positivity
  have durationNonneg :=
    (wholeRestartDuration_pos stackedShortCurrent.contact).le
  nlinarith

theorem stackedShortCurrent_sourceKineticDrift_lt_inverse_ten_pow_nineteen :
    Real.sqrt
        (3 * wholeRestartDuration stackedShortCurrent.contact *
          fullReplayWholeTangentSquareSourceUpper stackedShortCurrent) <
      1 / (10 : Real) ^ 19 := by
  apply (Real.sqrt_lt' (by positivity)).2
  have durationLt :=
    stackedShortCurrent_duration_lt_inverse_ten_pow_forty
  have tangentLt := stackedShortCurrent_wholeTangentSourceUpper_lt_two
  have tangentNonneg :
      0 ≤ fullReplayWholeTangentSquareSourceUpper stackedShortCurrent :=
    (fullReplayWholeTangentSquare_le_sourceUpper stackedShortCurrent).trans'
      (sq_nonneg _)
  have durationNonneg :=
    (wholeRestartDuration_pos stackedShortCurrent.contact).le
  nlinarith

theorem stackedSideband_sqrtNormSq_lt_five
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    Real.sqrt (integerWaveNormSq wave) < 5 := by
  rw [stackedSideband_integerWaveNormSq_eq wave waveMem]
  apply (Real.sqrt_lt' (by norm_num)).2
  norm_num

theorem stackedSideband_sqrtNormSq_lt_twenty_five_sixths
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    Real.sqrt (integerWaveNormSq wave) < 25 / 6 := by
  rw [stackedSideband_integerWaveNormSq_eq wave waveMem]
  apply (Real.sqrt_lt' (by norm_num : (0 : Real) < 25 / 6)).2
  norm_num

theorem stackedShortCurrent_kineticVelocityRadius_lt_seventeen :
    fullReplayKineticVelocityRadius stackedShortCurrent < 17 := by
  unfold fullReplayKineticVelocityRadius
  rw [stackedShortCurrent_ceiling_eq_eighty_eight]
  apply (Real.sqrt_lt' (by norm_num)).2
  norm_num

theorem stackedSideband_damping_lt_one
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    butterflyGainViscosity.coeff * integerWaveViscousMultiplier wave < 1 := by
  have waveNormSq := stackedSideband_integerWaveNormSq_eq wave waveMem
  unfold integerWaveViscousMultiplier
  rw [waveNormSq]
  calc
    butterflyGainViscosity.coeff * ((2 * Real.pi) ^ 2 * 17) =
        (butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2) * 17 := by ring
    _ = (1 / 100 : Real) * 17 := by
      rw [butterflyGainViscosity_scaled]
      norm_num
    _ < 1 := by norm_num

/-- The source-only kinetic remainder is far below one on each paying
sideband of the first actual stacked occurrence. -/
theorem stackedSideband_kineticTangentSourceUpper_lt_one_hundredth
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    fullReplayKineticTangentSourceUpper stackedShortCurrent wave < 1 / 100 := by
  have piLt : Real.pi < 4 := Real.pi_lt_four
  have sqrtLt := stackedSideband_sqrtNormSq_lt_five wave waveMem
  have radiusLt := stackedShortCurrent_kineticVelocityRadius_lt_seventeen
  have dampingLt := stackedSideband_damping_lt_one wave waveMem
  have driftLt :=
    stackedShortCurrent_sourceKineticDrift_lt_inverse_ten_pow_nineteen
  have outerNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
    positivity
  have radiusNonneg :=
    fullReplayKineticVelocityRadius_nonneg stackedShortCurrent
  have dampingNonneg :
      0 ≤ butterflyGainViscosity.coeff *
        integerWaveViscousMultiplier wave := by
    exact mul_nonneg butterflyGainViscosity.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have driftNonneg :
      0 ≤ Real.sqrt
        (3 * wholeRestartDuration stackedShortCurrent.contact *
          fullReplayWholeTangentSquareSourceUpper stackedShortCurrent) :=
    Real.sqrt_nonneg _
  unfold fullReplayKineticTangentSourceUpper
  let outer := (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)
  let radius := fullReplayKineticVelocityRadius stackedShortCurrent
  let damping := butterflyGainViscosity.coeff *
    integerWaveViscousMultiplier wave
  let drift := Real.sqrt
    (3 * wholeRestartDuration stackedShortCurrent.contact *
      fullReplayWholeTangentSquareSourceUpper stackedShortCurrent)
  have outerLt : outer < 120 := by
    dsimp only [outer]
    calc
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) <
          (6 * Real.pi) * 5 :=
        mul_lt_mul_of_pos_left sqrtLt
          (mul_pos (by norm_num) Real.pi_pos)
      _ < 6 * 4 * 5 := by nlinarith [Real.pi_pos]
      _ = 120 := by norm_num
  have twoRadiusLt : 2 * radius < 34 := by
    dsimp only [radius]
    nlinarith
  have radiusPos : 0 < radius := by
    dsimp only [radius, fullReplayKineticVelocityRadius]
    apply Real.sqrt_pos.2
    exact mul_pos (by norm_num)
      (wholeRestartCoefficientCeiling_pos stackedShortCurrent.contact)
  have outerRadiusLt : outer * (2 * radius) < 120 * 34 := by
    calc
      outer * (2 * radius) < 120 * (2 * radius) :=
        mul_lt_mul_of_pos_right outerLt (mul_pos (by norm_num) radiusPos)
      _ < 120 * 34 := mul_lt_mul_of_pos_left twoRadiusLt (by norm_num)
  have coefficientLt : outer * (2 * radius) + damping < 4081 := by
    have dampingLt' : damping < 1 := by
      simpa only [damping] using dampingLt
    nlinarith [outerRadiusLt]
  have coefficientNonneg : 0 ≤ outer * (2 * radius) + damping := by
    dsimp only [outer, radius, damping]
    exact add_nonneg
      (mul_nonneg outerNonneg
        (mul_nonneg (by norm_num) radiusNonneg)) dampingNonneg
  have outerCoefficientLt :
      outer * (outer * (2 * radius) + damping) < 120 * 4081 := by
    calc
      outer * (outer * (2 * radius) + damping) ≤
          120 * (outer * (2 * radius) + damping) :=
        mul_le_mul_of_nonneg_right outerLt.le coefficientNonneg
      _ < 120 * 4081 :=
        mul_lt_mul_of_pos_left coefficientLt (by norm_num)
  have finalLt :
      outer * ((outer * (2 * radius) + damping) * drift) <
        (120 * 4081 : Real) * (1 / 10 ^ 19) := by
    calc
      outer * ((outer * (2 * radius) + damping) * drift) =
          (outer * (outer * (2 * radius) + damping)) * drift := by ring
      _ ≤
          (120 * 4081 : Real) * drift :=
        mul_le_mul_of_nonneg_right outerCoefficientLt.le driftNonneg
      _ < (120 * 4081 : Real) * (1 / 10 ^ 19) :=
        mul_lt_mul_of_pos_left (by simpa only [drift] using driftLt)
          (by norm_num)
  exact finalLt.trans (by norm_num)

theorem stackedSideband_currentRow_norm_lt_ten
    (wave : IntegerWavevector) :
    ‖stackedShortCurrent.contact.physicalState wave‖ < 10 := by
  have rowLe := lp.norm_apply_le_norm (by norm_num)
    stackedShortCurrent.contact.physicalState wave
  have stateLe :=
    current_physicalState_norm_le_sqrt_coefficientCeiling
      stackedShortCurrent
  rw [stackedShortCurrent_ceiling_eq_eighty_eight] at stateLe
  have sqrtLt : Real.sqrt (88 : Real) < 10 := by
    apply (Real.sqrt_lt' (by norm_num)).2
    norm_num
  exact rowLe.trans_lt (stateLe.trans_lt sqrtLt)

/-- A source-only norm bound for the complete physical tangent on either
paying sideband.  It is deliberately crude: the seventh-order clock makes
the product with the actual row displacement microscopic. -/
theorem stackedSideband_sourceTangent_norm_lt_five_million
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        stackedShortCurrent.contact.physicalState wave‖ < 5000000 := by
  let state := stackedShortCurrent.contact.physicalState
  let velocity := wholeBiotSavartVelocityState state
  let outer := (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)
  let damping := butterflyGainViscosity.coeff *
    integerWaveViscousMultiplier wave
  have outerNonneg : 0 ≤ outer := by
    dsimp only [outer]
    positivity
  have outerLt : outer < 120 := by
    dsimp only [outer]
    have sqrtLt := stackedSideband_sqrtNormSq_lt_five wave waveMem
    calc
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) <
          (6 * Real.pi) * 5 :=
        mul_lt_mul_of_pos_left sqrtLt
          (mul_pos (by norm_num) Real.pi_pos)
      _ < 6 * 4 * 5 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
      _ = 120 := by norm_num
  have dampingNonneg : 0 ≤ damping := by
    dsimp only [damping]
    exact mul_nonneg butterflyGainViscosity.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have dampingLt : damping < 1 := by
    simpa only [damping] using stackedSideband_damping_lt_one wave waveMem
  have velocityNormLt : ‖velocity‖ < 17 := by
    exact (fullReplay_initialWholeBiotSavartVelocity_norm_le_radius
      stackedShortCurrent).trans_lt
        stackedShortCurrent_kineticVelocityRadius_lt_seventeen
  have velocityNonlinearLe :
      ‖wholeStateVelocityNonlinearCoefficientAt velocity wave‖ ≤
        outer * ‖velocity‖ * ‖velocity‖ := by
    simpa only [velocity, outer,
      wholeStateVelocityNonlinearCoefficientAt] using
      wholeStateVelocityBilinearCoefficientAt_norm_le
        (wholeBiotSavartVelocityState state)
        (wholeBiotSavartVelocityState state)
        (wholeBiotSavartVelocityState_transverse state) wave
  have vorticityNonlinearLe :
      ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ ≤
        outer * (outer * ‖velocity‖ * ‖velocity‖) := by
    rw [wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity
      state stackedShortCurrent.contact.physicalState_zero
      stackedShortCurrent.contact.transverse wave]
    exact (fourierCurlCoefficient_norm_le_six_pi_sqrt wave
      (wholeStateVelocityNonlinearCoefficientAt velocity wave)).trans
        (mul_le_mul_of_nonneg_left velocityNonlinearLe outerNonneg)
  have nonlinearLeConst :
      outer * (outer * ‖velocity‖ * ‖velocity‖) ≤
        120 * (120 * 17 * 17) := by
    have velocityNormNonneg : 0 ≤ ‖velocity‖ := norm_nonneg _
    have firstLe : outer * ‖velocity‖ ≤ 120 * 17 :=
      mul_le_mul outerLt.le velocityNormLt.le velocityNormNonneg (by norm_num)
    have secondLe : outer * ‖velocity‖ * ‖velocity‖ ≤
        120 * 17 * 17 :=
      mul_le_mul firstLe velocityNormLt.le velocityNormNonneg (by norm_num)
    have secondNonneg :
        0 ≤ outer * ‖velocity‖ * ‖velocity‖ := by positivity
    exact mul_le_mul outerLt.le secondLe secondNonneg (by norm_num)
  calc
    ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        stackedShortCurrent.contact.physicalState wave‖ =
        ‖wholeStateVorticityNonlinearCoefficientAt state wave -
          damping • state wave‖ := rfl
    _ ≤
        ‖wholeStateVorticityNonlinearCoefficientAt state wave‖ +
          ‖damping • state wave‖ := norm_sub_le _ _
    _ ≤ outer * (outer * ‖velocity‖ * ‖velocity‖) +
          damping * ‖state wave‖ := by
      apply add_le_add vorticityNonlinearLe
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg dampingNonneg]
    _ ≤ 120 * (120 * 17 * 17) + 1 * 10 := by
      apply add_le_add nonlinearLeConst
      have rowLt : ‖state wave‖ < 10 := by
        simpa only [state] using stackedSideband_currentRow_norm_lt_ten wave
      calc
        damping * ‖state wave‖ ≤ 1 * ‖state wave‖ :=
          mul_le_mul_of_nonneg_right dampingLt.le (norm_nonneg _)
        _ ≤ 1 * 10 := mul_le_mul_of_nonneg_left rowLt.le (by norm_num)
    _ < 5000000 := by norm_num

/-- The actual compiler-selected endpoint remains microscopically close to
the source row on either paying sideband.  This is the curl projection of
the same receipt's cutoff-free kinetic velocity displacement. -/
theorem stackedSideband_nextContactRow_sub_current_norm_lt_inverse_ten_pow_seventeen
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖stackedShortCurrent.nextContact.physicalState wave -
        stackedShortCurrent.contact.physicalState wave‖ <
      1 / (10 : Real) ^ 17 := by
  have waveNe : wave ≠ 0 := fun waveZero => by
    subst wave
    exact stackedSidebandCone.zeroNotMem waveMem
  let zeroTime : Icc (0 : Real)
      (wholeRestartDuration stackedShortCurrent.contact) :=
    ⟨0, ⟨le_rfl,
      (wholeRestartDuration_pos stackedShortCurrent.contact).le⟩⟩
  let source := stackedShortCurrent.contact.physicalState
  let target := stackedShortCurrent.nextContact.physicalState
  let sourceVelocity := wholeBiotSavartVelocityState source
  let targetVelocity := wholeBiotSavartVelocityState target
  have velocityDriftLe :
      ‖targetVelocity - sourceVelocity‖ ≤
        Real.sqrt
          (3 * wholeRestartDuration stackedShortCurrent.contact *
            fullReplayWholeTangentSquareSourceUpper stackedShortCurrent) := by
    have generated :=
      receipt_wholeBiotSavartVelocity_sub_norm_le_driftUpper
        stackedShortCurrent.nextReceipt zeroTime
        stackedShortCurrent.nextContact.time
        stackedShortCurrent.nextContact.time.2.1
    have fullLe := receiptKineticVelocityDriftUpper_le_fullReplay
      stackedShortCurrent stackedShortCurrent.nextContact.time
    have sourceLe :=
      fullReplayKineticVelocityDriftUpper_le_source stackedShortCurrent
    have zeroEq : stackedShortCurrent.nextReceipt.wholePath zeroTime =
        stackedShortCurrent.contact.physicalState :=
      stackedShortCurrent.nextReceipt.wholePath_initial
    have targetEq : stackedShortCurrent.nextReceipt.wholePath
        stackedShortCurrent.nextContact.time =
          stackedShortCurrent.nextContact.physicalState := rfl
    have generated' : ‖targetVelocity - sourceVelocity‖ ≤
        receiptKineticVelocityDriftUpper stackedShortCurrent.nextReceipt
          zeroTime stackedShortCurrent.nextContact.time := by
      dsimp only [targetVelocity, sourceVelocity, target, source]
      simpa only [zeroEq, targetEq] using generated
    exact generated'.trans (fullLe.trans sourceLe)
  have sourceRow : source wave =
      fourierCurlCoefficient wave (sourceVelocity wave) := by
    dsimp only [source, sourceVelocity]
    change stackedShortCurrent.contact.physicalState wave =
      fourierCurlCoefficient wave
        (biotSavartVelocityCoefficient wave
          (stackedShortCurrent.contact.physicalState wave))
    exact
      (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
        wave (stackedShortCurrent.contact.physicalState wave) waveNe
        (stackedShortCurrent.contact.transverse wave)).symm
  have targetRow : target wave =
      fourierCurlCoefficient wave (targetVelocity wave) := by
    dsimp only [target, targetVelocity]
    change stackedShortCurrent.nextContact.physicalState wave =
      fourierCurlCoefficient wave
        (biotSavartVelocityCoefficient wave
          (stackedShortCurrent.nextContact.physicalState wave))
    exact
      (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
        wave (stackedShortCurrent.nextContact.physicalState wave) waveNe
        (stackedShortCurrent.nextContact.transverse wave)).symm
  have velocityRowLe :
      ‖targetVelocity wave - sourceVelocity wave‖ ≤
        ‖targetVelocity - sourceVelocity‖ := by
    exact lp.norm_apply_le_norm (by norm_num)
      (targetVelocity - sourceVelocity) wave
  have outerLt :
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) < 100 := by
    have sqrtLt :=
      stackedSideband_sqrtNormSq_lt_twenty_five_sixths wave waveMem
    calc
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) <
          (6 * Real.pi) * (25 / 6) :=
        mul_lt_mul_of_pos_left sqrtLt
          (mul_pos (by norm_num) Real.pi_pos)
      _ < 6 * 4 * (25 / 6) := by
        nlinarith [Real.pi_pos, Real.pi_lt_four]
      _ = 100 := by norm_num
  rw [show stackedShortCurrent.nextContact.physicalState wave =
      target wave by rfl,
    show stackedShortCurrent.contact.physicalState wave =
      source wave by rfl,
    targetRow, sourceRow]
  change
    ‖fourierCurlCoefficientContinuousLinearMap wave (targetVelocity wave) -
      fourierCurlCoefficientContinuousLinearMap wave (sourceVelocity wave)‖ < _
  rw [← map_sub]
  calc
    ‖fourierCurlCoefficientContinuousLinearMap wave
        (targetVelocity wave - sourceVelocity wave)‖ ≤
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)) *
          ‖targetVelocity wave - sourceVelocity wave‖ := by
      simpa only [fourierCurlCoefficientContinuousLinearMap_apply] using
        fourierCurlCoefficient_norm_le_six_pi_sqrt wave
          (targetVelocity wave - sourceVelocity wave)
    _ ≤ ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)) *
          ‖targetVelocity - sourceVelocity‖ :=
      mul_le_mul_of_nonneg_left velocityRowLe (by positivity)
    _ ≤ ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)) *
          Real.sqrt
            (3 * wholeRestartDuration stackedShortCurrent.contact *
              fullReplayWholeTangentSquareSourceUpper
                stackedShortCurrent) :=
      mul_le_mul_of_nonneg_left velocityDriftLe (by positivity)
    _ < 100 * (1 / (10 : Real) ^ 19) := by
      have driftLt :=
        stackedShortCurrent_sourceKineticDrift_lt_inverse_ten_pow_nineteen
      calc
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)) *
              Real.sqrt
                (3 * wholeRestartDuration stackedShortCurrent.contact *
                  fullReplayWholeTangentSquareSourceUpper
                    stackedShortCurrent) ≤
            100 * Real.sqrt
              (3 * wholeRestartDuration stackedShortCurrent.contact *
                fullReplayWholeTangentSquareSourceUpper
                  stackedShortCurrent) :=
          mul_le_mul_of_nonneg_right outerLt.le (Real.sqrt_nonneg _)
        _ < 100 * (1 / (10 : Real) ^ 19) :=
          mul_lt_mul_of_pos_left driftLt (by norm_num)
    _ = 1 / (10 : Real) ^ 17 := by norm_num

/-- The same selected endpoint also preserves the complete NS tangent row
to within one hundredth.  No presentation-time endpoint is introduced: the
proof reads the fixed `nextContact` from the receipt compiler. -/
theorem stackedSideband_nextContactTangent_sub_current_norm_lt_one_hundredth
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.nextContact.physicalState wave -
        wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave‖ <
      1 / 100 := by
  have waveNe : wave ≠ 0 := fun waveZero => by
    subst wave
    exact stackedSidebandCone.zeroNotMem waveMem
  let receipt := stackedShortCurrent.nextReceipt
  let actual := stackedShortCurrent.nextContact.time.1
  let pathState : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  have pathStateEq :
      pathState = stackedShortCurrent.nextContact.physicalState := by
    change stackedShortCurrent.nextReceipt.wholePath
        (Set.projIcc 0 (wholeRestartDuration stackedShortCurrent.contact)
          (wholeRestartDuration_pos stackedShortCurrent.contact).le actual) =
      stackedShortCurrent.nextContact.physicalState
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos stackedShortCurrent.contact).le
      stackedShortCurrent.nextContact.time.2]
    rfl
  have heatPathEq :
      actualWholeContinuousHeatDuhamelPath receipt wave actual =
        stackedShortCurrent.nextContact.physicalState wave := by
    have generated :=
      wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
        receipt wave waveNe stackedShortCurrent.nextContact.time
    exact generated.symm
  have actualLe :=
    fullReplayEulerErrorDerivative_norm_le_kinetic
      stackedShortCurrent wave waveNe actual
        stackedShortCurrent.nextContact.time.2
  have sourceLe :=
    fullReplayKineticTangentDriftUpper_le_sourceUpper
      stackedShortCurrent wave
  unfold fullReplayEulerErrorDerivative at actualLe
  rw [heatPathEq, ← pathStateEq] at actualLe
  change
    ‖wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff pathState wave -
        wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave‖ ≤
      fullReplayKineticTangentDriftUpper stackedShortCurrent wave
    at actualLe
  rw [pathStateEq] at actualLe
  exact (actualLe.trans sourceLe).trans_lt
    (stackedSideband_kineticTangentSourceUpper_lt_one_hundredth
      wave waveMem)

theorem stackedSideband_nextContactTangent_norm_lt_five_million_one
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        stackedShortCurrent.nextContact.physicalState wave‖ < 5000001 := by
  let targetTangent := wholeLatticeVorticityFourierTangentAt
    butterflyGainViscosity.coeff
    stackedShortCurrent.nextContact.physicalState wave
  let sourceTangent := wholeLatticeVorticityFourierTangentAt
    butterflyGainViscosity.coeff
    stackedShortCurrent.contact.physicalState wave
  have differenceLt : ‖targetTangent - sourceTangent‖ < 1 / 100 := by
    simpa only [targetTangent, sourceTangent] using
      stackedSideband_nextContactTangent_sub_current_norm_lt_one_hundredth
        wave waveMem
  have sourceLt : ‖sourceTangent‖ < 5000000 := by
    simpa only [sourceTangent] using
      stackedSideband_sourceTangent_norm_lt_five_million wave waveMem
  calc
    ‖targetTangent‖ = ‖(targetTangent - sourceTangent) + sourceTangent‖ := by
      congr 1
      module
    _ ≤ ‖targetTangent - sourceTangent‖ + ‖sourceTangent‖ :=
      norm_add_le _ _
    _ < 1 / 100 + 5000000 := add_lt_add differenceLt sourceLt
    _ < 5000001 := by norm_num

/-- The root compiler's actual successor retains a strictly positive
self-work margin on both paying sidebands.  This is the first recursive
same-effect regeneration step: state and tangent are transported together
through the selected receipt endpoint. -/
theorem stackedSideband_nextContact_selfTangentWork_gt_eleven
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    11 < selfTangentWorkAt
      stackedShortCurrent.nextContact.physicalState wave := by
  let targetState := stackedShortCurrent.nextContact.physicalState wave
  let sourceState := stackedShortCurrent.contact.physicalState wave
  let targetTangent := wholeLatticeVorticityFourierTangentAt
    butterflyGainViscosity.coeff
    stackedShortCurrent.nextContact.physicalState wave
  let sourceTangent := wholeLatticeVorticityFourierTangentAt
    butterflyGainViscosity.coeff
    stackedShortCurrent.contact.physicalState wave
  have stateDifferenceLt : ‖targetState - sourceState‖ <
      1 / (10 : Real) ^ 17 := by
    simpa only [targetState, sourceState] using
      stackedSideband_nextContactRow_sub_current_norm_lt_inverse_ten_pow_seventeen
        wave waveMem
  have tangentDifferenceLt : ‖targetTangent - sourceTangent‖ <
      1 / 100 := by
    simpa only [targetTangent, sourceTangent] using
      stackedSideband_nextContactTangent_sub_current_norm_lt_one_hundredth
        wave waveMem
  have targetTangentLt : ‖targetTangent‖ < 5000001 := by
    simpa only [targetTangent] using
      stackedSideband_nextContactTangent_norm_lt_five_million_one
        wave waveMem
  have sourceStateLt : ‖sourceState‖ < 10 := by
    simpa only [sourceState] using
      stackedSideband_currentRow_norm_lt_ten wave
  have firstTermLe :
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ ≤
        3 * (1 / (10 : Real) ^ 17) * 5000001 := by
    have scaledStateLe :
        3 * ‖targetState - sourceState‖ ≤
          3 * (1 / (10 : Real) ^ 17) :=
      mul_le_mul_of_nonneg_left stateDifferenceLt.le (by norm_num)
    exact mul_le_mul scaledStateLe targetTangentLt.le
      (norm_nonneg _) (by positivity)
  have secondTermLe :
      3 * ‖sourceState‖ * ‖targetTangent - sourceTangent‖ ≤
        3 * 10 * (1 / 100 : Real) := by
    have scaledSourceLe : 3 * ‖sourceState‖ ≤ 3 * 10 :=
      mul_le_mul_of_nonneg_left sourceStateLt.le (by norm_num)
    exact mul_le_mul scaledSourceLe tangentDifferenceLt.le
      (norm_nonneg _) (by norm_num)
  have errorLt :
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ +
          3 * ‖sourceState‖ * ‖targetTangent - sourceTangent‖ < 1 := by
    calc
      3 * ‖targetState - sourceState‖ * ‖targetTangent‖ +
            3 * ‖sourceState‖ * ‖targetTangent - sourceTangent‖ ≤
          3 * (1 / (10 : Real) ^ 17) * 5000001 +
            3 * 10 * (1 / 100 : Real) :=
        add_le_add firstTermLe secondTermLe
      _ < 1 := by norm_num
  have pairing := abs_complexCoordinateRealInner_pair_sub_le
    targetState sourceState targetTangent sourceTangent
  have differenceLower :
      -1 < complexCoordinateRealInner targetState targetTangent -
        complexCoordinateRealInner sourceState sourceTangent := by
    have negativeAbsolute := neg_abs_le
      (complexCoordinateRealInner targetState targetTangent -
        complexCoordinateRealInner sourceState sourceTangent)
    linarith
  have sourceWork :=
    (stackedShortContact_sourcePatch.2.2 wave waveMem).2.2
  unfold selfTangentWorkAt at sourceWork ⊢
  dsimp only [targetState, sourceState, targetTangent, sourceTangent]
    at differenceLower
  linarith

theorem stackedSideband_kineticPaymentDensity_pos
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    0 < nextContactKineticEulerPaymentDensity
      stackedShortCurrent wave := by
  have workGt : (10 : Real) <
      complexCoordinateRealInner
        (stackedShortCurrent.contact.physicalState wave)
        (wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedShortCurrent.contact.physicalState wave) := by
    have workTwelve :=
      (stackedShortContact_sourcePatch.2.2 wave waveMem).2.2
    unfold selfTangentWorkAt at workTwelve
    exact (by norm_num : (10 : Real) < 12).trans workTwelve
  have normLt := stackedSideband_currentRow_norm_lt_ten wave
  have upperLt :=
    stackedSideband_kineticTangentSourceUpper_lt_one_hundredth
      wave waveMem
  have upperNonneg : 0 ≤
      fullReplayKineticTangentSourceUpper stackedShortCurrent wave :=
    (fullReplayKineticTangentDriftUpper_nonneg
      stackedShortCurrent wave).trans
        (fullReplayKineticTangentDriftUpper_le_sourceUpper
          stackedShortCurrent wave)
  have productLt :
      ‖stackedShortCurrent.contact.physicalState wave‖ *
          fullReplayKineticTangentSourceUpper stackedShortCurrent wave <
        1 / 10 := by
    calc
      ‖stackedShortCurrent.contact.physicalState wave‖ *
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave ≤
          10 * fullReplayKineticTangentSourceUpper
            stackedShortCurrent wave :=
        mul_le_mul_of_nonneg_right normLt.le upperNonneg
      _ < 10 * (1 / 100 : Real) :=
        mul_lt_mul_of_pos_left upperLt (by norm_num)
      _ = 1 / 10 := by norm_num
  have errorTermLt :
      6 * ‖stackedShortCurrent.contact.physicalState wave‖ *
          fullReplayKineticTangentSourceUpper stackedShortCurrent wave <
        6 / 10 := by
    nlinarith [productLt]
  unfold nextContactKineticEulerPaymentDensity
  nlinarith [errorTermLt]

/-- Both source-owned sideband rows strictly gain actual coefficient mass on
the compiler-selected next contact. -/
theorem stackedSideband_nextContact_amplitudeSq_gt
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    complexCoordinateAmplitudeSq
        (stackedShortCurrent.contact.physicalState wave) <
      complexCoordinateAmplitudeSq
        (stackedShortCurrent.nextContact.physicalState wave) := by
  have waveNe : wave ≠ 0 := fun waveZero => by
    subst wave
    exact stackedSidebandCone.zeroNotMem waveMem
  have lower :=
    nextContact_amplitudeSq_sub_current_le_from_below_kineticSource
      stackedShortCurrent wave waveNe
  have paidPositive : 0 < stackedShortCurrent.nextContact.time.1 *
      nextContactKineticEulerPaymentDensity stackedShortCurrent wave :=
    mul_pos stackedShortCurrent.nextContact.time_pos
      (stackedSideband_kineticPaymentDensity_pos wave waveMem)
  linarith

def stackedStageZeroStanding :=
  runCellStanding stackedShortCurrent 0

def stackedStageZeroMaterial :=
  nativeRestartStandingValuedArithmeticMaterial
    (runStandingCellEffect stackedShortCurrent 0)

theorem stackedStageZeroStanding_anchorLevel_eq :
    stackedStageZeroStanding.anchorLevel = 88 := by
  change wholeRestartCoefficientLevel stackedShortCurrent.contact = 88
  exact stackedShortCurrent_level_eq_eighty_eight

theorem stackedSideband_mem_stageZeroAnchorCube
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    wave ∈ wholeRestartModes (stackedStageZeroStanding.anchorLevel + 1) := by
  rw [stackedStageZeroStanding_anchorLevel_eq]
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
    Finset.mem_erase, integerWaveFrequencyCube, Fintype.mem_piFinset]
  constructor
  · exact fun waveZero => stackedSidebandCone.zeroNotMem (waveZero ▸ waveMem)
  · intro coordinate
    simp only [stackedSidebandModes, plusSideband, minusSideband,
      Finset.mem_insert, Finset.mem_singleton] at waveMem
    rcases waveMem with rfl | rfl <;>
      fin_cases coordinate <;>
      norm_num [axisWave, pumpY]

/-- The root residual's own physical valuation pays the exact selected
clock on the complete two-row kinetic face.  This is one projection of the
standing-valued material, not a post-hoc positivity classifier. -/
theorem stackedStageZeroResidualExpansion_clock_mul_densitySum_le
    (residual : GeneratedParallelResidualAt stackedStageZeroMaterial
      stackedStageZeroMaterial.arithmeticMaterial) :
    stackedShortCurrent.nextContact.time.1 *
        (∑ wave ∈ stackedSidebandModes,
          nextContactKineticEulerPaymentDensity
            stackedShortCurrent wave) ≤
      (stackedStageZeroMaterial.generatedResidualExpansion residual
        ).finiteNetEnstrophyDebit := by
  apply NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.clock_mul_sum_kineticDensity_le_finiteNetEnstrophyDebit
  · intro wave waveMem
    exact stackedSideband_mem_stageZeroAnchorCube wave waveMem
  · intro wave waveMem
    exact stackedSideband_kineticPaymentDensity_pos wave waveMem

/-- The same face has a strictly positive total kinetic density. -/
theorem stackedSideband_kineticPaymentDensity_sum_pos :
    0 < ∑ wave ∈ stackedSidebandModes,
      nextContactKineticEulerPaymentDensity stackedShortCurrent wave := by
  apply Finset.sum_pos'
  · intro wave waveMem
    exact (stackedSideband_kineticPaymentDensity_pos wave waveMem).le
  · refine ⟨plusSideband, by simp [stackedSidebandModes], ?_⟩
    exact stackedSideband_kineticPaymentDensity_pos plusSideband
      (by simp [stackedSidebandModes])

/-- If the root normalization is residual rather than exact, its own
source-generated physical expansion is strictly valued on this same actual
occurrence. -/
theorem stackedStageZeroResidualExpansion_finiteDebit_pos
    (residual : GeneratedParallelResidualAt stackedStageZeroMaterial
      stackedStageZeroMaterial.arithmeticMaterial) :
    0 < (stackedStageZeroMaterial.generatedResidualExpansion residual
      ).finiteNetEnstrophyDebit := by
  have paid :=
    stackedStageZeroResidualExpansion_clock_mul_densitySum_le residual
  have clockPaymentPos : 0 < stackedShortCurrent.nextContact.time.1 *
      (∑ wave ∈ stackedSidebandModes,
        nextContactKineticEulerPaymentDensity stackedShortCurrent wave) :=
    mul_pos stackedShortCurrent.nextContact.time_pos
      stackedSideband_kineticPaymentDensity_sum_pos
  exact clockPaymentPos.trans_le paid

/-- The actual root outcome itself is paid at stage zero.  In particular,
the fresh-gain expansion is now consumed inside the root emitter; it is no
longer merely a downstream alternative to the root's scalar disposition. -/
noncomputable def stackedStageZero_rootOutcome_isPaid :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    (nativeFluidMediumRootOperationalOutcomeAt source source.initial).IsPaid := by
  dsimp only
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt
      (classicalWholeRestartMediumSource stackedShortCurrent)
      (classicalWholeRestartMediumSource stackedShortCurrent).initial =
        outcome
  cases outcome with
  | exactPayment => exact PUnit.unit
  | generatedResidual => exact PUnit.unit
  | obstruction obstruction _demand =>
      rcases obstruction with
        ⟨⟨effect, effectEq⟩, residual, expansion, expansionEq,
          _rawNonpositive, expansionNonpositive⟩
      subst effect
      change expansion.finiteNetEnstrophyDebit ≤ 0 at expansionNonpositive
      rw [expansionEq] at expansionNonpositive
      exact (not_lt_of_ge expansionNonpositive
        (stackedStageZeroResidualExpansion_finiteDebit_pos residual)).elim

/-- The paid root outcome, exact standing-valued material and compiler-owned
successor are three projections of the same stage-zero occurrence. -/
theorem stackedStageZero_paidRootStep_factorizes :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source 0)
    HEq (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter 0)).effect stackedStageZeroMaterial ∧
      Nonempty (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter 0)).IsPaid ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter 1 := by
  dsimp only
  have factorized :=
    classicalWholeRestart_runStandingEffect_rootStep_factorizes
      stackedShortCurrent 0
  exact ⟨factorized.1, ⟨stackedStageZero_rootOutcome_isPaid⟩,
    factorized.2.2⟩

end
end ButterflyStackedKineticAdvance
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
