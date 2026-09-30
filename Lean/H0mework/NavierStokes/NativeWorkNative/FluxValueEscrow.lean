import H0mework.NavierStokes.NativeWork.MixedNegativeOneGradientFixedOutput
import H0mework.NavierStokes.Accumulation.TemporalEnstrophyLedger

/-!
# Value-level native flux escrow

The native coface flux pairs the nonlinear projection error with the
projected vorticity state itself.  Unlike the full normalized-work Frechet
test, this test has a whole-carrier `H¹` energy bound independent of the
projection radius.  The existing nonlinear `H⁻¹` Agmon estimate therefore
gives a genuine inverse-radius value escrow.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientNativeFluxValueEscrow

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientInstantaneousWholeNetPowerCapture
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace

noncomputable section

private theorem puncturedProjection_eq_cubeProjection
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0) :
    complexSharpSupportProjection (wholeRestartModes radius) state =
      complexSharpSupportProjection
        (integerWaveFrequencyCube radius) state := by
  ext wave coordinate
  by_cases waveZero : wave = 0
  · subst wave
    simp [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
      complexSharpSupportProjection_apply, stateZero]
  · simp [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
      complexSharpSupportProjection_apply, waveZero]

private theorem nativeFlux_eq_negativeProjectionPairing
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0) :
    let modes := wholeRestartModes radius
    let projected := complexSharpSupportProjection
      (integerWaveFrequencyCube radius) state
    nativeTurbulenceEnstrophyFlux modes state =
      -(∑ wave ∈ modes,
        complexCoordinateRealInner (state wave)
          (wholeStateVorticityNonlinearCoefficientAt projected wave -
            wholeStateVorticityNonlinearCoefficientAt state wave)) := by
  dsimp only
  have projectionEq := puncturedProjection_eq_cubeProjection
    radius state stateZero
  unfold nativeTurbulenceEnstrophyFlux cofaceInputCorrectionAt
    projectedWholeNonlinearCoefficientAt
  rw [projectionEq]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [if_pos waveMem]
  have projectedRowEq :
      complexSharpSupportProjection
          (integerWaveFrequencyCube radius) state wave = state wave := by
    rw [← projectionEq]
    simp [complexSharpSupportProjection_apply, waveMem]
  rw [projectedRowEq, if_pos waveMem]
  simp only [complexCoordinateRealInner_sub_right]
  ring

private theorem nativeFluxTestEnergy_le_wholeGradient
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    (∑ wave ∈ wholeRestartModes radius,
        3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (state wave)) ≤
      3 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state := by
  have finiteLe := finiteStateVorticityEnstrophyMass_le_wholeGradientMass
    (wholeRestartModes radius) state gradientSummable
  unfold finiteStateVorticityEnstrophyMass at finiteLe
  unfold integerWaveViscousMultiplier
  calc
    (∑ wave ∈ wholeRestartModes radius,
        3 * ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) *
          complexCoordinateAmplitudeSq (state wave)) =
        3 * (2 * Real.pi) ^ 2 *
          (∑ wave ∈ wholeRestartModes radius,
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (state wave)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave _waveMem
      ring
    _ ≤ 3 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state := by
      exact mul_le_mul_of_nonneg_left finiteLe
        (mul_nonneg (by norm_num) (sq_nonneg _))

/-- Radius-uniform `H¹×H⁻¹` bound for the actual native flux value. -/
theorem nativeTurbulenceEnstrophyFlux_sq_le_negativeOne
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    nativeTurbulenceEnstrophyFlux (wholeRestartModes radius) state ^ 2 ≤
      (3 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state) *
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state) state := by
  let modes := wholeRestartModes radius
  let projected := complexSharpSupportProjection
    (integerWaveFrequencyCube radius) state
  have pairing :=
    finiteNonlinearProjectionPairing_sq_le_testEnergy_mul_differenceMass
      state stateTransverse gradientSummable radius modes
      (fun wave waveMem => fun waveZero =>
        zero_not_mem_puncturedIntegerWaveFrequencyCube radius
          (waveZero ▸ waveMem)) state
  have fluxEq := nativeFlux_eq_negativeProjectionPairing
    radius state stateZero
  have testEnergyLe := nativeFluxTestEnergy_le_wholeGradient
    radius state gradientSummable
  have differenceNonneg : 0 ≤
      wholeStateVorticityNonlinearDifferenceNegativeOneMass projected state := by
    unfold wholeStateVorticityNonlinearDifferenceNegativeOneMass
    exact tsum_nonneg fun wave =>
      wholeStateVorticityNonlinearDifferenceNegativeOneDensity_nonneg
        projected state wave
  rw [fluxEq, neg_sq]
  exact pairing.trans
    (mul_le_mul_of_nonneg_right testEnergyLe differenceNonneg)

/-- The Agmon projection law turns the exact value pairing into a genuine
inverse-radius escrow with no radius-dependent dual test. -/
theorem nativeTurbulenceEnstrophyFlux_sq_le_agmon
    (radius : Nat)
    (radiusPos : 0 < radius)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    nativeTurbulenceEnstrophyFlux (wholeRestartModes radius) state ^ 2 ≤
      (3 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state) *
        (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
          wholeVorticityEuclideanMass state *
          wholeStateVorticityGradientMass state) := by
  have base := nativeTurbulenceEnstrophyFlux_sq_le_negativeOne
    radius state stateZero stateTransverse gradientSummable
  have differenceLe :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
      state stateTransverse gradientSummable radius radiusPos
  have testEnergyNonneg : 0 ≤
      3 * (2 * Real.pi) ^ 2 *
        wholeStateVorticityGradientMass state := by
    have gradientNonneg : 0 ≤ wholeStateVorticityGradientMass state := by
      unfold wholeStateVorticityGradientMass
      exact tsum_nonneg fun wave =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
    positivity
  exact base.trans
    (mul_le_mul_of_nonneg_left differenceLe testEnergyNonneg)

/-- Complete current-state numerator of the value escrow. -/
def nativeFluxValueEscrowNumerator
    (state : ComplexVorticityHilbertState) : Real :=
  (3 * (2 * Real.pi) ^ 2 *
      wholeStateVorticityGradientMass state) *
    (728 * biotSavartSerrinConstant *
      wholeVorticityEuclideanMass state *
      wholeStateVorticityGradientMass state)

theorem nativeFluxValueEscrowNumerator_nonneg
    (state : ComplexVorticityHilbertState) :
    0 ≤ nativeFluxValueEscrowNumerator state := by
  have massNonneg := wholeVorticityEuclideanMass_nonneg state
  have gradientNonneg : 0 ≤ wholeStateVorticityGradientMass state := by
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  unfold nativeFluxValueEscrowNumerator
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg _)) gradientNonneg)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        massNonneg)
      gradientNonneg)

/-- Canonical source radius selected from the same state's physical mass,
gradient mass and a positive requested flux tolerance. -/
noncomputable def nativeFluxValueCaptureRadius
    (state : ComplexVorticityHilbertState)
    (tolerance : {value : Real // 0 < value}) : Nat :=
  Nat.ceil
      (nativeFluxValueEscrowNumerator state / tolerance.1 ^ 2) + 1

theorem nativeFluxValueCaptureRadius_pos
    (state : ComplexVorticityHilbertState)
    (tolerance : {value : Real // 0 < value}) :
    0 < nativeFluxValueCaptureRadius state tolerance := by
  unfold nativeFluxValueCaptureRadius
  omega

/-- Every radius beyond the source-generated threshold captures the native
coface flux below the requested positive tolerance. -/
theorem nativeTurbulenceEnstrophyFlux_abs_lt_of_captureRadius_le
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (tolerance : {value : Real // 0 < value})
    (captureLe : nativeFluxValueCaptureRadius state tolerance ≤ radius) :
    |nativeTurbulenceEnstrophyFlux
        (wholeRestartModes radius) state| <
      tolerance.1 := by
  let numerator := nativeFluxValueEscrowNumerator state
  let ratio := numerator / tolerance.1 ^ 2
  let captureRadius := nativeFluxValueCaptureRadius state tolerance
  have numeratorNonneg : 0 ≤ numerator := by
    simpa only [numerator] using nativeFluxValueEscrowNumerator_nonneg state
  have toleranceSqPos : 0 < tolerance.1 ^ 2 :=
    sq_pos_of_pos tolerance.2
  have ratioNonneg : 0 ≤ ratio :=
    div_nonneg numeratorNonneg toleranceSqPos.le
  have ratioLeCeil : ratio ≤ (Nat.ceil ratio : Real) := Nat.le_ceil ratio
  have ratioLtCapture : ratio < (captureRadius : Real) := by
    change ratio < ((Nat.ceil ratio + 1 : Nat) : Real)
    exact ratioLeCeil.trans_lt (by norm_num)
  have captureCastLe : (captureRadius : Real) ≤ (radius : Real) := by
    exact_mod_cast captureLe
  have ratioLtRadius : ratio < (radius : Real) :=
    ratioLtCapture.trans_le captureCastLe
  have radiusPosNat : 0 < radius := by
    exact (nativeFluxValueCaptureRadius_pos state tolerance).trans_le
      captureLe
  have radiusPos : 0 < (radius : Real) := by exact_mod_cast radiusPosNat
  have numeratorLt : numerator < tolerance.1 ^ 2 * (radius : Real) := by
    have scaled := mul_lt_mul_of_pos_left ratioLtRadius toleranceSqPos
    dsimp only [ratio] at scaled
    rw [mul_div_cancel₀ numerator toleranceSqPos.ne'] at scaled
    exact scaled
  have quotientLt : numerator / (radius : Real) < tolerance.1 ^ 2 := by
    exact (div_lt_iff₀ radiusPos).2 (by simpa [mul_comm] using numeratorLt)
  have fluxSqLe := nativeTurbulenceEnstrophyFlux_sq_le_agmon
    radius radiusPosNat state stateZero stateTransverse gradientSummable
  have escrowEq :
      (3 * (2 * Real.pi) ^ 2 *
          wholeStateVorticityGradientMass state) *
          (728 * biotSavartSerrinConstant * (radius : Real)⁻¹ *
            wholeVorticityEuclideanMass state *
            wholeStateVorticityGradientMass state) =
        numerator / (radius : Real) := by
    unfold numerator nativeFluxValueEscrowNumerator
    rw [div_eq_mul_inv]
    ring
  rw [escrowEq] at fluxSqLe
  have fluxSqLt := fluxSqLe.trans_lt quotientLt
  rw [← sq_abs] at fluxSqLt
  exact (sq_lt_sq₀ (abs_nonneg _) tolerance.2.le).mp fluxSqLt

/-- Source-generated value capture at the canonical threshold itself. -/
theorem nativeTurbulenceEnstrophyFlux_abs_lt_captureTolerance
    (state : ComplexVorticityHilbertState)
    (stateZero : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (tolerance : {value : Real // 0 < value}) :
    |nativeTurbulenceEnstrophyFlux
        (wholeRestartModes
          (nativeFluxValueCaptureRadius state tolerance)) state| <
      tolerance.1 := by
  exact nativeTurbulenceEnstrophyFlux_abs_lt_of_captureRadius_le
    (nativeFluxValueCaptureRadius state tolerance)
    state stateZero stateTransverse gradientSummable tolerance le_rfl

/-! ## Actual-current source specialization -/

/-- Every exact current computes its own canonical flux-capture radius from
the physical contact state already carried by that occurrence. -/
noncomputable def currentNativeFluxValueCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat :=
  nativeFluxValueCaptureRadius current.contact.physicalState tolerance

def currentNativeFluxValueCaptureModes
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    Finset IntegerWavevector :=
  wholeRestartModes
    (currentNativeFluxValueCaptureRadius current tolerance)

theorem current_nativeTurbulenceEnstrophyFlux_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    |nativeTurbulenceEnstrophyFlux
        (currentNativeFluxValueCaptureModes current tolerance)
        current.contact.physicalState| < tolerance.1 := by
  exact nativeTurbulenceEnstrophyFlux_abs_lt_captureTolerance
    current.contact.physicalState current.contact.physicalState_zero
    current.contact.transverse current.contact.gradient_summable tolerance

/-- On the source-generated capture modes, the actual time-zero projected
power differs from the resolved finite generator work by less than twice the
requested native-flux tolerance. -/
theorem current_timeZeroPower_sub_resolved_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentNativeFluxValueCaptureModes current tolerance
    |actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      2 * tolerance.1 := by
  dsimp only
  let modes := currentNativeFluxValueCaptureModes current tolerance
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) =
      current.contact.physicalState
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt_initial
  have split :=
    actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
      current.nextReceipt modes 0
  dsimp only at split
  rw [stateAtZero] at split
  change
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 =
      2 * (finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes current.contact.physicalState) +
        nativeTurbulenceEnstrophyFlux modes
          current.contact.physicalState) at split
  have fluxSmall := current_nativeTurbulenceEnstrophyFlux_abs_lt
    current tolerance
  change
    |actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes current.contact.physicalState)| <
      2 * tolerance.1
  rw [split]
  rw [show
    2 * (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes current.contact.physicalState) +
          nativeTurbulenceEnstrophyFlux modes current.contact.physicalState) -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes current.contact.physicalState) =
      2 * nativeTurbulenceEnstrophyFlux modes
        current.contact.physicalState by ring]
  have scaled := mul_lt_mul_of_pos_left fluxSmall (by norm_num : (0 : Real) < 2)
  simpa only [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)] using
    (show |2 * nativeTurbulenceEnstrophyFlux modes
        current.contact.physicalState| < 2 * tolerance.1 by
      simpa [mul_assoc] using scaled)

/-! ## Joint complete-work and native-flux capture -/

def currentInstantaneousWholePower
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  ∑' wave : IntegerWavevector,
    instantaneousWholeNetPowerRow
      nu current.contact.physicalState wave

/-- Canonical punctured cubes, not arbitrary finite inventories, converge to
the current's complete instantaneous work. -/
theorem current_projectedPower_puncturedCube_tendsto_global
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    Filter.Tendsto
      (fun radius : Nat =>
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (wholeRestartModes radius) 0)
      Filter.atTop
      (nhds (currentInstantaneousWholePower current)) := by
  have fullCube :=
    (current_projectedPower_zero_tendsto_global current).comp
      integerWaveFrequencyCube_tendsto_atTop
  have puncturedEq :
      (fun radius : Nat =>
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (wholeRestartModes radius) 0) =
      (fun radius : Nat =>
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (integerWaveFrequencyCube radius) 0) := by
    funext radius
    rw [actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow,
      actualProjectedWholeNetEnstrophyPower_zero_eq_sum_instantaneousRow]
    unfold wholeRestartModes puncturedIntegerWaveFrequencyCube
    by_cases zeroMem :
        (0 : IntegerWavevector) ∈ integerWaveFrequencyCube radius
    · have eraseAdd := Finset.sum_erase_add
        (s := integerWaveFrequencyCube radius)
        (f := instantaneousWholeNetPowerRow
          nu current.contact.physicalState) zeroMem
      rw [instantaneousWholeNetPowerRow_zero
        nu current.contact.physicalState
          current.contact.physicalState_zero, add_zero] at eraseAdd
      exact eraseAdd
    · rw [Finset.erase_eq_of_notMem zeroMem]
  rw [puncturedEq]
  change Filter.Tendsto
    (fun radius : Nat =>
      actualProjectedWholeNetEnstrophyPower current.nextReceipt
        (integerWaveFrequencyCube radius) 0)
    Filter.atTop
    (nhds (currentInstantaneousWholePower current)) at fullCube
  exact fullCube

theorem exists_currentCanonicalPowerCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    ∃ threshold : Nat, ∀ radius : Nat, threshold ≤ radius →
      |currentInstantaneousWholePower current -
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (wholeRestartModes radius) 0| < tolerance.1 := by
  have converges := current_projectedPower_puncturedCube_tendsto_global current
  obtain ⟨threshold, close⟩ :=
    (Metric.tendsto_atTop.mp converges) tolerance.1 tolerance.2
  refine ⟨threshold, ?_⟩
  intro radius thresholdLe
  have distanceClose := close radius thresholdLe
  simpa only [Real.dist_eq, abs_sub_comm] using distanceClose

/-- Least source-generated threshold for complete instantaneous work.  Using
the least valid threshold preserves the quantitative provenance needed by a
later explicit Fourier-tail estimate; it does not alter any world branch. -/
noncomputable def currentCanonicalPowerCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat := by
  classical
  exact Nat.find
    (exists_currentCanonicalPowerCaptureRadius current tolerance)

theorem currentCanonicalPowerCaptureRadius_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (radiusLe : currentCanonicalPowerCaptureRadius current tolerance ≤ radius) :
    |currentInstantaneousWholePower current -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt
        (wholeRestartModes radius) 0| < tolerance.1 := by
  classical
  exact (Nat.find_spec
      (exists_currentCanonicalPowerCaptureRadius current tolerance))
    radius radiusLe

/-- Any explicit source threshold bounds the canonical least signed-work
capture radius. -/
theorem currentCanonicalPowerCaptureRadius_le_of_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (threshold : Nat)
    (thresholdSpec : ∀ radius : Nat, threshold ≤ radius →
      |currentInstantaneousWholePower current -
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          (wholeRestartModes radius) 0| < tolerance.1) :
    currentCanonicalPowerCaptureRadius current tolerance ≤ threshold := by
  classical
  exact Nat.find_min'
    (exists_currentCanonicalPowerCaptureRadius current tolerance)
    thresholdSpec

/-- One deterministic radius simultaneously captures complete signed work
and makes the native coface value small. -/
noncomputable def currentResolvedWorkCaptureRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) : Nat :=
  max (currentCanonicalPowerCaptureRadius current tolerance)
    (currentNativeFluxValueCaptureRadius current tolerance)

def currentResolvedWorkCaptureModes
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    Finset IntegerWavevector :=
  wholeRestartModes (currentResolvedWorkCaptureRadius current tolerance)

/-- At every radius beyond the joint source threshold, complete
instantaneous whole work and twice the resolved finite generator work differ
by less than three source-requested tolerances. -/
theorem current_wholePower_sub_two_resolved_abs_lt_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe : currentResolvedWorkCaptureRadius current tolerance ≤ radius) :
    let modes := wholeRestartModes radius
    |currentInstantaneousWholePower current -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      3 * tolerance.1 := by
  dsimp only
  let modes := wholeRestartModes radius
  change
    |currentInstantaneousWholePower current -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      3 * tolerance.1
  have powerClose := currentCanonicalPowerCaptureRadius_spec
    current tolerance radius
      ((le_max_left _ _).trans captureLe)
  have fluxClose :=
    nativeTurbulenceEnstrophyFlux_abs_lt_of_captureRadius_le
      radius current.contact.physicalState
      current.contact.physicalState_zero current.contact.transverse
      current.contact.gradient_summable tolerance
      ((le_max_right _ _).trans captureLe)
  have stateAtZero :
      (actualWholeProjectedTransversePath current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) =
      current.contact.physicalState
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt_initial
  have split :=
    actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
      current.nextReceipt modes 0
  dsimp only at split
  rw [stateAtZero] at split
  change
    actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 =
      2 * (finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes current.contact.physicalState) +
        nativeTurbulenceEnstrophyFlux modes
          current.contact.physicalState) at split
  have triangle := abs_add_le
    (currentInstantaneousWholePower current -
      actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0)
    (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
      2 * finiteGeneratorRealWork modes nu.coeff
        (complexSharpSupportProjection modes current.contact.physicalState))
  have secondClose :
      |actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes current.contact.physicalState)| <
        2 * tolerance.1 := by
    rw [split]
    rw [show
      2 * (finiteGeneratorRealWork modes nu.coeff
              (complexSharpSupportProjection modes current.contact.physicalState) +
            nativeTurbulenceEnstrophyFlux modes current.contact.physicalState) -
          2 * finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes current.contact.physicalState) =
        2 * nativeTurbulenceEnstrophyFlux modes
          current.contact.physicalState by ring]
    have scaled := mul_lt_mul_of_pos_left fluxClose
      (by norm_num : (0 : Real) < 2)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)] using
      (show |2 * nativeTurbulenceEnstrophyFlux modes
          current.contact.physicalState| < 2 * tolerance.1 by
        simpa [mul_assoc] using scaled)
  have combined :
      |(currentInstantaneousWholePower current -
          actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0) +
        (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
          2 * finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              current.contact.physicalState))| <
        tolerance.1 + 2 * tolerance.1 :=
    triangle.trans_lt (add_lt_add powerClose secondClose)
  have leftEq :
      (currentInstantaneousWholePower current -
          actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0) +
        (actualProjectedWholeNetEnstrophyPower current.nextReceipt modes 0 -
          2 * finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              current.contact.physicalState)) =
        currentInstantaneousWholePower current -
          2 * finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              current.contact.physicalState) := by ring
  have rightEq : tolerance.1 + 2 * tolerance.1 =
      3 * tolerance.1 := by ring
  rw [leftEq, rightEq] at combined
  exact combined

/-- Complete instantaneous whole work and twice the resolved finite
generator work differ by less than three source-requested tolerances. -/
theorem current_wholePower_sub_two_resolved_abs_lt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value}) :
    let modes := currentResolvedWorkCaptureModes current tolerance
    |currentInstantaneousWholePower current -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      3 * tolerance.1 := by
  dsimp only [currentResolvedWorkCaptureModes]
  exact current_wholePower_sub_two_resolved_abs_lt_of_captureRadius_le
    current tolerance (currentResolvedWorkCaptureRadius current tolerance)
      le_rfl

/-- A positive complete-work margin is converted by the source-generated
joint radius into a strictly positive resolved finite generator work. -/
theorem current_resolvedGeneratorWork_pos_of_wholePower_headroom
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (headroom : 3 * tolerance.1 <
      currentInstantaneousWholePower current) :
    let modes := currentResolvedWorkCaptureModes current tolerance
    0 < finiteGeneratorRealWork modes nu.coeff
      (complexSharpSupportProjection modes current.contact.physicalState) := by
  dsimp only
  have close := current_wholePower_sub_two_resolved_abs_lt
    current tolerance
  rcases abs_lt.mp close with ⟨_lower, upper⟩
  linarith

end

end ThreeDimensionalVorticityCoefficientNativeFluxValueEscrow
end NavierStokes
end SaturationMonoid
