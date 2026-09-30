import H0mework.Versions.X.NavierStokes.Butterfly.CompleteRowRightDerivative
import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance

/-!
# Source-selected butterfly cell crossing

The complete butterfly carrier has coefficient mass exactly `24`.  This
module source-selects the viscosity whose Fourier-scaled coefficient is
`1 / 100`; on the same actual source occurrence its exact NS enstrophy
tangent is positive.  Consequently every sufficiently short positive
physical time crosses the source cell wall `24`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace SaturationMonoid.NavierStokes.RationalVorticityEvaluator

open scoped BigOperators Matrix ENNReal Topology Interval
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientFiniteSupportWholeActionTube
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall

noncomputable section

def gaussianRatVectorRealInner
    (left right : GaussianRatVector) : ℚ :=
  ∑ coordinate : Fin 3,
    ((left coordinate).re * (right coordinate).re +
      (left coordinate).im * (right coordinate).im)

def butterflyRationalSeedStateAt (a : ℚ) : GaussianRatState := fun wave =>
  if wave ∈ butterflySeedModes then butterflySeedRow a wave else 0

def butterflyRationalTangentStateAt
    (a viscosityScaled : ℚ) : GaussianRatState :=
  rationalVorticityGeneratorCoefficientAt butterflySeedModes
    viscosityScaled (butterflyRationalSeedStateAt a)

def butterflyRationalEnstrophyTangentPairing
    (a viscosityScaled : ℚ) : ℚ :=
  ∑ wave ∈ butterflySeedModes,
    gaussianRatVectorRealInner
      (butterflyRationalSeedStateAt a wave)
      (butterflyRationalTangentStateAt a viscosityScaled wave)

def butterflyRationalCoefficientMass (a : ℚ) : ℚ :=
  ∑ wave ∈ butterflySeedModes,
    gaussianRatVectorRealInner
      (butterflyRationalSeedStateAt a wave)
      (butterflyRationalSeedStateAt a wave)

theorem butterflyRationalEnstrophyTangentPairing_gain :
    butterflyRationalEnstrophyTangentPairing 1 (1 / 100) = 157 / 50 := by
  simp (config := { maxSteps := 1000000 })
    [butterflyRationalEnstrophyTangentPairing,
      butterflyRationalTangentStateAt, butterflyRationalSeedStateAt,
      gaussianRatVectorRealInner, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow,
      rationalVorticityGeneratorCoefficientAt,
      rationalVorticityNonlinearCoefficientAt,
      rationalVorticityBilinearCoefficientAt,
      rationalVorticityPairContribution, rationalIntegerWaveNormSq,
      sidebandPlusZ_eq 2 (by norm_num) 1,
      sidebandMinusZ_eq 2 (by norm_num) 1,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      GaussianRatVector.waveDot, GaussianRatVector.waveCross,
      GaussianRatVector.tripleWaveCrossDot,
      GaussianRatVector.add, GaussianRatVector.sub,
      GaussianRatVector.complexScale, GaussianRatVector.ratScale,
      GaussianRat.add, GaussianRat.sub, GaussianRat.neg, GaussianRat.mul,
      GaussianRat.ratScale, GaussianRat.intScale, GaussianRat.ratDiv,
      Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
  norm_num [GaussianRat.ratScale]

theorem butterflyRationalCoefficientMass_one :
    butterflyRationalCoefficientMass 1 = 24 := by
  simp (config := { maxSteps := 1000000 })
    [butterflyRationalCoefficientMass, butterflyRationalSeedStateAt,
      gaussianRatVectorRealInner, butterflySeedModes, butterflySeedRow,
      butterflyZTwoModes, butterflyZTwoRow,
      sidebandPlusZ_eq 2 (by norm_num) 1,
      sidebandMinusZ_eq 2 (by norm_num) 1,
      axisWave, pumpY, pumpZ, realRow, realGaussian,
      Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num [GaussianRat.ratScale]

def butterflyGainViscosity : Viscosity where
  coeff := (1 / 100 : ℝ) / (2 * Real.pi) ^ 2
  coeff_pos := by positivity

theorem butterflyGainViscosity_scaled :
    butterflyGainViscosity.coeff * (2 * Real.pi) ^ 2 =
      ((1 / 100 : ℚ) : ℝ) := by
  unfold butterflyGainViscosity
  field_simp [Real.pi_ne_zero]
  norm_num

def butterflyGainReplay := butterflyReplay butterflyGainViscosity

def butterflyGainReceipt := butterflyReceipt butterflyGainViscosity

def butterflyGainPhysicalTime : ℝ :=
  wholeRestartDuration (butterflyPhysicalSeed butterflyGainViscosity)

def butterflyGainPhysicalActionState : ComplexVorticityHilbertState :=
  wholeFiniteSupportActionState butterflyGainViscosity.coeff
    butterflySeedModes (butterflyPhysicalState 1)

theorem butterflyGainRationalSeedState_toComplex
    (wave : IntegerWavevector) :
    GaussianRatVector.toComplex (butterflyRationalSeedStateAt 1 wave) =
      butterflyPhysicalState 1 wave := by
  by_cases waveMem : wave ∈ butterflySeedModes
  · simp [butterflyRationalSeedStateAt,
      butterflyPhysicalState_apply, waveMem]
  · simp [butterflyRationalSeedStateAt,
      butterflyPhysicalState_apply, waveMem]

theorem butterflyGainRationalTangentState_toComplex
    (wave : IntegerWavevector) :
    GaussianRatVector.toComplex
        (butterflyRationalTangentStateAt 1 (1 / 100) wave) =
      butterflyGainPhysicalActionState wave := by
  have bridge := rationalVorticityGeneratorCoefficientAt_toComplex
    butterflySeedModes (1 / 100) (butterflyRationalSeedStateAt 1)
    (butterflyPhysicalState 1) wave butterflyGainViscosity.coeff
    butterflySeedModes_zero_not_mem
    (fun actual _actualMem => butterflyGainRationalSeedState_toComplex actual)
    (butterflyGainRationalSeedState_toComplex wave)
    butterflyGainViscosity_scaled
  rw [butterflyGainPhysicalActionState,
    wholeFiniteSupportActionState_apply_eq_wholeTangent
      butterflyGainViscosity.coeff butterflySeedModes
      (butterflyPhysicalState 1)
      (butterflyPhysicalState_supported 1) wave]
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1) wave]
  exact bridge

theorem complexCoordinateRealInner_gaussianRat_toComplex
    (left right : GaussianRatVector) :
    complexCoordinateRealInner
        (GaussianRatVector.toComplex left)
        (GaussianRatVector.toComplex right) =
      (gaussianRatVectorRealInner left right : ℝ) := by
  unfold complexCoordinateRealInner gaussianRatVectorRealInner
    GaussianRatVector.toComplex GaussianRat.toComplex
  simp [Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im]

theorem butterflyGainPhysicalEnstrophyTangentPairing_eq :
    (∑ wave ∈ butterflySeedModes,
      complexCoordinateRealInner
        (butterflyPhysicalState 1 wave)
        (butterflyGainPhysicalActionState wave)) =
      (157 / 50 : ℝ) := by
  calc
    (∑ wave ∈ butterflySeedModes,
        complexCoordinateRealInner
          (butterflyPhysicalState 1 wave)
          (butterflyGainPhysicalActionState wave)) =
        ∑ wave ∈ butterflySeedModes,
          (gaussianRatVectorRealInner
            (butterflyRationalSeedStateAt 1 wave)
            (butterflyRationalTangentStateAt 1 (1 / 100) wave) : ℝ) := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [← butterflyGainRationalSeedState_toComplex,
        ← butterflyGainRationalTangentState_toComplex,
        complexCoordinateRealInner_gaussianRat_toComplex]
    _ = (butterflyRationalEnstrophyTangentPairing
          1 (1 / 100) : ℚ) := by
      norm_cast
    _ = (157 / 50 : ℝ) := by
      rw [butterflyRationalEnstrophyTangentPairing_gain]
      norm_num

theorem butterflyPhysicalState_one_coefficientMass_eq :
    wholeVorticityEuclideanMass (butterflyPhysicalState 1) = 24 := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1)]
  unfold finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ butterflySeedModes,
        complexCoordinateAmplitudeSq (butterflyPhysicalState 1 wave)) =
        ∑ wave ∈ butterflySeedModes,
          (gaussianRatVectorRealInner
            (butterflyRationalSeedStateAt 1 wave)
            (butterflyRationalSeedStateAt 1 wave) : ℝ) := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
        ← complexCoordinateRealInner_self,
        ← butterflyGainRationalSeedState_toComplex,
        complexCoordinateRealInner_gaussianRat_toComplex]
    _ = (butterflyRationalCoefficientMass 1 : ℚ) := by
      norm_cast
    _ = (24 : ℝ) := by
      rw [butterflyRationalCoefficientMass_one]
      norm_num

def butterflyGainHeatPath
    (wave : IntegerWavevector) (actual : ℝ) : ComplexCoordinateVector :=
  actualWholeContinuousHeatDuhamelPath butterflyGainReceipt wave actual

def butterflyGainFiniteMassPath (actual : ℝ) : ℝ :=
  ∑ wave ∈ butterflySeedModes,
    complexCoordinateAmplitudeSq (butterflyGainHeatPath wave actual)

theorem butterflyGainHeatPath_hasDerivAt_zero
    (wave : IntegerWavevector) :
    HasDerivAt (butterflyGainHeatPath wave)
      (butterflyGainPhysicalActionState wave) 0 := by
  have generated :=
    actualWholeContinuousHeatDuhamelPath_hasDerivAt_zero
      butterflyGainReceipt wave
  have tangentEq :
      wholeStateVorticityNonlinearCoefficientAt
            (butterflyPhysicalState 1) wave -
          (butterflyGainViscosity.coeff *
            integerWaveViscousMultiplier wave) •
            butterflyPhysicalState 1 wave =
        butterflyGainPhysicalActionState wave := by
    rw [butterflyGainPhysicalActionState,
      wholeFiniteSupportActionState_apply_eq_wholeTangent
        butterflyGainViscosity.coeff butterflySeedModes
        (butterflyPhysicalState 1)
        (butterflyPhysicalState_supported 1) wave]
    rfl
  change HasDerivAt
    (actualWholeContinuousHeatDuhamelPath butterflyGainReceipt wave)
    (butterflyGainPhysicalActionState wave) 0
  simpa only [butterflyPhysicalSeed_wholeState] using
    generated.congr_deriv tangentEq

@[simp] theorem butterflyGainHeatPath_zero
    (wave : IntegerWavevector) :
    butterflyGainHeatPath wave 0 = butterflyPhysicalState 1 wave := by
  unfold butterflyGainHeatPath actualWholeContinuousHeatDuhamelPath
    ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.heatDuhamelComplexCoordinatePath
    ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport.intervalIntegralComplexCoordinatePath
  simp [butterflyPhysicalSeed_wholeState]

theorem butterflyGainFiniteMassPath_hasDerivAt_zero :
    HasDerivAt butterflyGainFiniteMassPath (157 / 25 : ℝ) 0 := by
  unfold butterflyGainFiniteMassPath
  have waveDerivative : ∀ wave ∈ butterflySeedModes,
      HasDerivAt
        (fun actual =>
          complexCoordinateAmplitudeSq (butterflyGainHeatPath wave actual))
        (2 * complexCoordinateRealInner
          (butterflyPhysicalState 1 wave)
          (butterflyGainPhysicalActionState wave)) 0 := by
    intro wave waveMem
    simpa using complexCoordinateAmplitudeSq_hasDerivAt
      (butterflyGainHeatPath wave) 0
      (butterflyGainPhysicalActionState wave)
      (butterflyGainHeatPath_hasDerivAt_zero wave)
  have summed := HasDerivAt.fun_sum waveDerivative
  rw [← Finset.mul_sum] at summed
  exact summed.congr_deriv (by
    rw [butterflyGainPhysicalEnstrophyTangentPairing_eq]
    norm_num)

@[simp] theorem butterflyGainFiniteMassPath_zero :
    butterflyGainFiniteMassPath 0 = 24 := by
  unfold butterflyGainFiniteMassPath
  simp only [butterflyGainHeatPath_zero]
  change finiteStateVorticityCoefficientEnstrophy butterflySeedModes
    (butterflyPhysicalState 1) = 24
  rw [← wholeVorticityEuclideanMass_eq_finite_of_supported
    butterflySeedModes (butterflyPhysicalState 1)
    (butterflyPhysicalState_supported 1)]
  exact butterflyPhysicalState_one_coefficientMass_eq

theorem exists_butterflyGainFiniteMassCrossingTime :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ butterflyGainPhysicalTime ∧
        ∀ actual : ℝ, 0 < actual → actual < epsilon →
          24 < butterflyGainFiniteMassPath actual := by
  have eventuallyPositiveSlopeWithin :
      ∀ᶠ actual in 𝓝[>] (0 : ℝ),
        (157 / 50 : ℝ) <
          actual⁻¹ •
            (butterflyGainFiniteMassPath (0 + actual) -
              butterflyGainFiniteMassPath 0) :=
    butterflyGainFiniteMassPath_hasDerivAt_zero.tendsto_slope_zero_right
      |>.eventually (eventually_gt_nhds (by norm_num))
  have eventuallyPositiveSlope :
      ∀ᶠ actual in 𝓝 (0 : ℝ),
        actual ∈ Ioi (0 : ℝ) →
          (157 / 50 : ℝ) <
            actual⁻¹ •
              (butterflyGainFiniteMassPath (0 + actual) -
                butterflyGainFiniteMassPath 0) :=
    eventually_nhdsWithin_iff.mp eventuallyPositiveSlopeWithin
  obtain ⟨radius, radiusPos, slopePositive⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyPositiveSlope
  have physicalTimePos : 0 < butterflyGainPhysicalTime :=
    wholeRestartDuration_pos (butterflyPhysicalSeed butterflyGainViscosity)
  let epsilon := min radius (butterflyGainPhysicalTime / 2)
  have epsilonPos : 0 < epsilon :=
    lt_min radiusPos (half_pos physicalTimePos)
  have epsilonLePhysical : epsilon ≤ butterflyGainPhysicalTime :=
    (min_le_right radius (butterflyGainPhysicalTime / 2)).trans
      (half_le_self physicalTimePos.le)
  refine ⟨epsilon, epsilonPos, epsilonLePhysical, ?_⟩
  intro actual actualPos actualLt
  have slope := slopePositive (by
    rw [Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact actualLt.trans_le (min_le_left _ _)) actualPos
  rw [zero_add, butterflyGainFiniteMassPath_zero] at slope
  have inversePos : 0 < actual⁻¹ := inv_pos.mpr actualPos
  have differencePos :
      0 < butterflyGainFiniteMassPath actual - 24 := by
    by_contra notPositive
    have differenceNonpos :
        butterflyGainFiniteMassPath actual - 24 ≤ 0 := le_of_not_gt notPositive
    have scaledNonpos :
        actual⁻¹ * (butterflyGainFiniteMassPath actual - 24) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos inversePos.le differenceNonpos
    exact (not_lt_of_ge scaledNonpos) (lt_trans (by norm_num) slope)
  linarith

theorem exists_butterflyGainWholeMassCrossingTime :
    ∃ epsilon : ℝ,
      0 < epsilon ∧ epsilon ≤ butterflyGainPhysicalTime ∧
        ∀ actual : ℝ, 0 < actual → actual < epsilon →
          24 < wholeVorticityEuclideanMass
            (actualWholeProjectedTransversePath
              butterflyGainReceipt actual).1 := by
  obtain ⟨epsilon, epsilonPos, epsilonLePhysical, finiteCrossing⟩ :=
    exists_butterflyGainFiniteMassCrossingTime
  refine ⟨epsilon, epsilonPos, epsilonLePhysical, ?_⟩
  intro actual actualPos actualLt
  have actualMem : actual ∈ Icc (0 : ℝ) butterflyGainPhysicalTime :=
    ⟨actualPos.le, actualLt.le.trans epsilonLePhysical⟩
  have actualMem' : actual ∈ Icc (0 : ℝ)
      (wholeRestartDuration
        (butterflyPhysicalSeed butterflyGainViscosity)) := by
    simpa only [butterflyGainPhysicalTime] using actualMem
  have finitePathEq :
      butterflyGainFiniteMassPath actual =
        finiteStateVorticityCoefficientEnstrophy butterflySeedModes
          (actualWholeProjectedTransversePath
            butterflyGainReceipt actual).1 := by
    unfold butterflyGainFiniteMassPath
      finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro wave waveMem
    have waveNonzero : wave ≠ 0 := fun waveZero =>
      butterflySeedModes_zero_not_mem (waveZero ▸ waveMem)
    congr 1
    change actualWholeContinuousHeatDuhamelPath
        butterflyGainReceipt wave actual =
      butterflyGainReceipt.wholePath
        (Set.projIcc 0
          (wholeRestartDuration
            (butterflyPhysicalSeed butterflyGainViscosity))
          butterflyGainReceipt.requestedTimePos.le actual) wave
    rw [Set.projIcc_of_mem
      butterflyGainReceipt.requestedTimePos.le actualMem']
    exact (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      butterflyGainReceipt wave waveNonzero ⟨actual, actualMem'⟩).symm
  have crossing := finiteCrossing actual actualPos actualLt
  rw [finitePathEq] at crossing
  exact crossing.trans_le
    (finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      butterflySeedModes _)

/-! ## Source-owned current carrying the joint physical gain row -/

/-- The exact time-zero net-enstrophy valuation of the butterfly material.
This is the physical projection of the same complete finite action, before
any contact or arithmetic branch is selected. -/
theorem butterflyGainReceipt_netPower_zero_eq :
    actualProjectedWholeNetEnstrophyPower butterflyGainReceipt
        butterflySeedModes 0 = (157 / 25 : Real) := by
  rw [actualProjectedWholeNetEnstrophyPower_zero_eq_wholeTangentWork]
  change
    2 * ∑ wave ∈ butterflySeedModes,
        complexCoordinateRealInner (butterflyPhysicalState 1 wave)
          (wholeLatticeVorticityFourierTangentAt
            butterflyGainViscosity.coeff
            (butterflyPhysicalState 1) wave) = _
  have tangentEq : ∀ wave : IntegerWavevector,
      wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff (butterflyPhysicalState 1) wave =
        butterflyGainPhysicalActionState wave := by
    intro wave
    rw [butterflyGainPhysicalActionState,
      wholeFiniteSupportActionState_apply_eq_wholeTangent
        butterflyGainViscosity.coeff butterflySeedModes
        (butterflyPhysicalState 1)
        (butterflyPhysicalState_supported 1) wave]
  simp_rw [tangentEq]
  rw [butterflyGainPhysicalEnstrophyTangentPairing_eq]
  norm_num

/-- One source-selected interval simultaneously retains the physical
projected power and crosses the whole coefficient wall.  The selected
window is source data; no future contact or branch occurs in its predicate. -/
theorem exists_butterflyGainJointMaterialWindow :
    ∃ epsilon : Real,
      0 < epsilon ∧ epsilon ≤ butterflyGainPhysicalTime ∧
        ∀ actual : Real, 0 < actual → actual < epsilon →
          (3 : Real) <
              actualProjectedWholeNetEnstrophyPower butterflyGainReceipt
                butterflySeedModes actual ∧
            24 < wholeVorticityEuclideanMass
              (actualWholeProjectedTransversePath
                butterflyGainReceipt actual).1 := by
  let power : Real → Real := fun actual =>
    actualProjectedWholeNetEnstrophyPower butterflyGainReceipt
      butterflySeedModes actual
  have powerContinuous : Continuous power :=
    actualProjectedWholeNetEnstrophyPower_continuous
      butterflyGainReceipt butterflySeedModes
  have zeroMem : 0 ∈ {actual | (3 : Real) < power actual} := by
    change (3 : Real) < power 0
    dsimp only [power]
    rw [butterflyGainReceipt_netPower_zero_eq]
    norm_num
  have powerOpen : IsOpen {actual | (3 : Real) < power actual} :=
    isOpen_lt continuous_const powerContinuous
  obtain ⟨powerRadius, powerRadiusPos, powerSubset⟩ :=
    Metric.isOpen_iff.mp powerOpen 0 zeroMem
  obtain ⟨massRadius, massRadiusPos, massRadiusLe, massCrossing⟩ :=
    exists_butterflyGainWholeMassCrossingTime
  let epsilon := min powerRadius massRadius
  have epsilonPos : 0 < epsilon := lt_min powerRadiusPos massRadiusPos
  have epsilonLe : epsilon ≤ butterflyGainPhysicalTime :=
    (min_le_right powerRadius massRadius).trans massRadiusLe
  refine ⟨epsilon, epsilonPos, epsilonLe, ?_⟩
  intro actual actualPos actualLt
  have powerLt : actual < powerRadius :=
    actualLt.trans_le (min_le_left powerRadius massRadius)
  have powerAt : (3 : Real) < power actual := by
    apply powerSubset
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos actualPos]
    exact powerLt
  have massLt : actual < massRadius :=
    actualLt.trans_le (min_le_right powerRadius massRadius)
  exact ⟨powerAt, massCrossing actual actualPos massLt⟩

def butterflyGainJointMaterialWindow : Real :=
  Classical.choose exists_butterflyGainJointMaterialWindow

theorem butterflyGainJointMaterialWindow_pos :
    0 < butterflyGainJointMaterialWindow :=
  (Classical.choose_spec exists_butterflyGainJointMaterialWindow).1

theorem butterflyGainJointMaterialWindow_le :
    butterflyGainJointMaterialWindow ≤ butterflyGainPhysicalTime :=
  (Classical.choose_spec exists_butterflyGainJointMaterialWindow).2.1

theorem butterflyGainJointMaterialWindow_spec
    (actual : Real)
    (actualPos : 0 < actual)
    (actualLt : actual < butterflyGainJointMaterialWindow) :
    (3 : Real) <
          actualProjectedWholeNetEnstrophyPower butterflyGainReceipt
            butterflySeedModes actual ∧
      24 < wholeVorticityEuclideanMass
        (actualWholeProjectedTransversePath
          butterflyGainReceipt actual).1 :=
  (Classical.choose_spec exists_butterflyGainJointMaterialWindow).2.2
    actual actualPos actualLt

def butterflyGainShortDuration : Real :=
  butterflyGainJointMaterialWindow / 2

theorem butterflyGainShortDuration_pos :
    0 < butterflyGainShortDuration :=
  half_pos butterflyGainJointMaterialWindow_pos

theorem butterflyGainShortDuration_le_original :
    butterflyGainShortDuration ≤ butterflyGainPhysicalTime := by
  unfold butterflyGainShortDuration
  exact (half_le_self butterflyGainJointMaterialWindow_pos.le).trans
    butterflyGainJointMaterialWindow_le

theorem butterflyGainShortDuration_lt_window :
    butterflyGainShortDuration < butterflyGainJointMaterialWindow := by
  unfold butterflyGainShortDuration
  linarith [butterflyGainJointMaterialWindow_pos]

def butterflyGainShortReceipt :
    WholeContinuousMildSerrinReceipt butterflyGainViscosity
      (butterflyPhysicalState 1) butterflyGainShortDuration :=
  restrictWholeContinuousMildSerrinReceipt
    butterflyGainShortDuration_pos
    butterflyGainShortDuration_le_original
    butterflyGainReceipt

def butterflyGainShortContact :=
  generatedPositiveWholeRestartContact butterflyGainShortReceipt

/-- Concrete source-owned actual current whose physical state, projected
power and cell-wall crossing were selected in one joint material fibre. -/
def butterflyGainShortCurrent :
    GeneratedWholeRestartCurrent butterflyGainViscosity where
  initialState := butterflyPhysicalState 1
  duration := butterflyGainShortDuration
  receipt := butterflyGainShortReceipt
  contact := butterflyGainShortContact

def butterflyGainShortContactOriginalTime :
    Set.Icc (0 : Real) butterflyGainPhysicalTime :=
  commonTimeInclusion butterflyGainShortDuration_le_original
    butterflyGainShortContact.time

theorem butterflyGainShortContact_state_eq_original :
    butterflyGainShortContact.physicalState =
      butterflyGainReceipt.wholePath
        butterflyGainShortContactOriginalTime := by
  rfl

theorem butterflyGainShortContact_joint_material :
    (3 : Real) <
          actualProjectedWholeNetEnstrophyPower butterflyGainReceipt
            butterflySeedModes
            butterflyGainShortContact.time.1 ∧
      24 < wholeVorticityEuclideanMass
        butterflyGainShortContact.physicalState := by
  have contactLtWindow :
      butterflyGainShortContact.time.1 <
        butterflyGainJointMaterialWindow :=
    butterflyGainShortContact.time.2.2.trans_lt
      butterflyGainShortDuration_lt_window
  have generated := butterflyGainJointMaterialWindow_spec
    butterflyGainShortContact.time.1
    butterflyGainShortContact.time_pos contactLtWindow
  refine ⟨generated.1, ?_⟩
  rw [butterflyGainShortContact_state_eq_original]
  have timeMem : butterflyGainShortContact.time.1 ∈
      Set.Icc (0 : Real) butterflyGainPhysicalTime :=
    ⟨butterflyGainShortContact.time_pos.le,
      butterflyGainShortContact.time.2.2.trans
        butterflyGainShortDuration_le_original⟩
  change 24 < wholeVorticityEuclideanMass
    (butterflyGainReceipt.wholePath
      butterflyGainShortContactOriginalTime)
  have generatedMass := generated.2
  have physicalTimePos : 0 < butterflyGainPhysicalTime :=
    wholeRestartDuration_pos
      (butterflyPhysicalSeed butterflyGainViscosity)
  change 24 < wholeVorticityEuclideanMass
    (butterflyGainReceipt.wholePath
      (Set.projIcc (0 : Real) butterflyGainPhysicalTime
        physicalTimePos.le butterflyGainShortContact.time.1))
    at generatedMass
  rw [Set.projIcc_of_mem physicalTimePos.le timeMem] at generatedMass
  exact generatedMass

theorem butterflyPhysicalSeed_one_level_eq_twenty_five :
    wholeRestartCoefficientLevel
      (butterflyPhysicalSeed butterflyGainViscosity) = 25 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  change Nat.ceil
    (wholeVorticityEuclideanMass (butterflyPhysicalState 1) + 1) = 25
  rw [butterflyPhysicalState_one_coefficientMass_eq]
  norm_num

theorem butterflyPhysicalSeed_one_ceiling_eq_twenty_five :
    wholeRestartCoefficientCeiling
      (butterflyPhysicalSeed butterflyGainViscosity) = 25 := by
  unfold wholeRestartCoefficientCeiling
  rw [butterflyPhysicalSeed_one_level_eq_twenty_five]
  norm_num

theorem butterflyGainReceipt_mass_le_twenty_five
    (time : Set.Icc (0 : Real) butterflyGainPhysicalTime) :
    wholeVorticityEuclideanMass
        (butterflyGainReceipt.wholePath time) ≤ 25 := by
  apply continuous_le_of_ae_le_commonTime
    (wholeRestartDuration_pos
      (butterflyPhysicalSeed butterflyGainViscosity))
    (fun actual => wholeVorticityEuclideanMass
      (butterflyGainReceipt.wholePath actual))
    (wholeReceiptVorticityMass_continuous butterflyGainReceipt)
  rw [← butterflyPhysicalSeed_one_ceiling_eq_twenty_five]
  simpa only [butterflyGainReceipt, butterflyGainReplay,
    butterflyGainPhysicalTime, butterflyReceipt, butterflyReplay] using
    generatedWholeRestartWholeContinuousMildSerrinReceipt_coefficientMass_ae_le
      butterflyGainReplay

theorem butterflyGainShortContact_mass_le_twenty_five :
    wholeVorticityEuclideanMass
        butterflyGainShortContact.physicalState ≤ 25 := by
  rw [butterflyGainShortContact_state_eq_original]
  exact butterflyGainReceipt_mass_le_twenty_five
    butterflyGainShortContactOriginalTime

theorem butterflyGainShortContact_level_eq_twenty_six :
    wholeRestartCoefficientLevel butterflyGainShortContact = 26 := by
  unfold wholeRestartCoefficientLevel wholeRestartRawCoefficientCeiling
  rw [Nat.ceil_eq_iff (by norm_num : (26 : Nat) ≠ 0)]
  norm_num
  constructor
  · linarith [butterflyGainShortContact_joint_material.2]
  · linarith [butterflyGainShortContact_mass_le_twenty_five]

theorem butterflyGainShortCurrent_ceiling_eq_twenty_six :
    wholeRestartCoefficientCeiling butterflyGainShortCurrent.contact = 26 := by
  unfold wholeRestartCoefficientCeiling
  change (wholeRestartCoefficientLevel butterflyGainShortContact : Real) = 26
  rw [butterflyGainShortContact_level_eq_twenty_six]
  norm_num

theorem butterflyGainShortCurrent_nextReceipt_state_zero :
    (actualWholeProjectedTransversePath
      butterflyGainShortCurrent.nextReceipt 0).1 =
        butterflyGainShortContact.physicalState := by
  change butterflyGainShortCurrent.nextReceipt.wholePath
      (Set.projIcc (0 : Real)
        (wholeRestartDuration butterflyGainShortCurrent.contact)
        butterflyGainShortCurrent.nextReceipt.requestedTimePos.le 0) =
    butterflyGainShortContact.physicalState
  rw [Set.projIcc_of_mem
    butterflyGainShortCurrent.nextReceipt.requestedTimePos.le
    ⟨le_rfl, butterflyGainShortCurrent.nextReceipt.requestedTimePos.le⟩]
  exact butterflyGainShortCurrent.nextReceipt.wholePath_initial

theorem butterflyGainReceipt_state_at_shortContact :
    (actualWholeProjectedTransversePath butterflyGainReceipt
      butterflyGainShortContact.time.1).1 =
        butterflyGainShortContact.physicalState := by
  have physicalTimePos : 0 < butterflyGainPhysicalTime :=
    wholeRestartDuration_pos
      (butterflyPhysicalSeed butterflyGainViscosity)
  have timeMem : butterflyGainShortContact.time.1 ∈
      Set.Icc (0 : Real) butterflyGainPhysicalTime :=
    ⟨butterflyGainShortContact.time_pos.le,
      butterflyGainShortContact.time.2.2.trans
        butterflyGainShortDuration_le_original⟩
  change butterflyGainReceipt.wholePath
      (Set.projIcc (0 : Real) butterflyGainPhysicalTime
        physicalTimePos.le butterflyGainShortContact.time.1) = _
  rw [Set.projIcc_of_mem physicalTimePos.le timeMem]
  exact butterflyGainShortContact_state_eq_original.symm

/-- The same actual endpoint becomes the exact source state of its canonical
native successor, retaining two full units of headroom above the unit
payment threshold.  No future contact, branch or recurrence is supplied. -/
theorem butterflyGainShortCurrent_nextReceipt_netPower_zero_gt_three :
    (3 : Real) <
      actualProjectedWholeNetEnstrophyPower
        butterflyGainShortCurrent.nextReceipt butterflySeedModes 0 := by
  have sourcePositive := butterflyGainShortContact_joint_material.1
  have powerEq :
      actualProjectedWholeNetEnstrophyPower
          butterflyGainShortCurrent.nextReceipt butterflySeedModes 0 =
        actualProjectedWholeNetEnstrophyPower
          butterflyGainReceipt butterflySeedModes
          butterflyGainShortContact.time.1 := by
    unfold actualProjectedWholeNetEnstrophyPower
      actualProjectedWholeEnstrophyPower
      actualProjectedWholeViscousEnstrophyPower
    rw [butterflyGainShortCurrent_nextReceipt_state_zero,
      butterflyGainReceipt_state_at_shortContact]
  rwa [powerEq]

theorem butterflyGainShortCurrent_nextReceipt_netPower_zero_gt_one :
    (1 : Real) <
      actualProjectedWholeNetEnstrophyPower
        butterflyGainShortCurrent.nextReceipt butterflySeedModes 0 :=
  (by norm_num : (1 : Real) < 3).trans
    butterflyGainShortCurrent_nextReceipt_netPower_zero_gt_three

end
end SaturationMonoid.NavierStokes.RationalVorticityEvaluator
