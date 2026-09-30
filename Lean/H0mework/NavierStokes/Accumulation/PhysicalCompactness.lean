import H0mework.NavierStokes.Accumulation.ScaleCriticalWindow

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration

open scoped BigOperators ContDiff ENNReal FourierTransform Pointwise SchwartzMap Topology

open Set Filter MeasureTheory
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.TotalReality
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ZeroLawRootAdmission
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicIntegerCharacterUnitCellMean
open ThreeDimensionalPeriodicCoarseFilterSpatialCommutation
open ThreeDimensionalPeriodicUnitCellDivergence
open ThreeDimensionalPeriodicLocalEnergyAlgebra
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientPhysicalFourierCoordinateObserver
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearRowLimit
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinWeakAction
open ThreeDimensionalVorticityCoefficientWholeSerrinEnstrophyGronwall
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeHighFrequencyTailDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeVorticityDivergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartBoundedPreAccumulationVelocityStrongTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationVorticityCourt
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceRateSettlement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSymmetricVelocityMultiplierGapTransport
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticFluxWork
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualKineticViscousExhaustion
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFrequencySupportExhaustion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateCharge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateResponsibility
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityFixedWindowLanding
open
  ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinPositiveTimeSuffix

noncomputable section

variable {nu : Viscosity}

private theorem finite_stretching_rate_nonpos_of_gradient_large
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (viscosity level : Real)
    (viscosityPos : 0 < viscosity)
    (levelNonneg : 0 ≤ level)
    (massLe :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ level)
    (gradientLarge :
      16 * 24336 * level ^ 3 <
        (viscosity * (2 * Real.pi) ^ 2) ^ 4 *
          finiteStateVorticityEnstrophyMass modes state) :
    finiteStateVorticityStretchingWork modes state -
        (viscosity * (2 * Real.pi) ^ 2 / 2) *
          finiteStateVorticityEnstrophyMass modes state ≤ 0 := by
  let S := finiteStateVorticityStretchingWork modes state
  let M := finiteStateVorticityCoefficientEnstrophy modes state
  let W := finiteStateVorticityEnstrophyMass modes state
  let A := viscosity * (2 * Real.pi) ^ 2
  have APos : 0 < A := by
    dsimp only [A]
    positivity
  have MNonneg : 0 ≤ M := by
    dsimp only [M]
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg (state wave)
  have WNonneg : 0 ≤ W := by
    dsimp only [W]
    exact finiteStateVorticityEnstrophyMass_nonneg modes state
  have M3Le : M ^ 3 ≤ level ^ 3 := by
    exact pow_le_pow_left₀ MNonneg massLe 3
  have fourth :=
    finiteStateVorticityStretchingWork_abs_pow_four_le_scaleCritical
      modes state zeroNotMem transverse
  change |S| ^ 4 ≤ 24336 * M ^ 3 * W ^ 3 at fourth
  change 16 * 24336 * level ^ 3 < A ^ 4 * W at gradientLarge
  by_contra ratePos
  have SPos : 0 < S := by
    have ratePositive :
      0 < finiteStateVorticityStretchingWork modes state -
          (viscosity * (2 * Real.pi) ^ 2 / 2) *
            finiteStateVorticityEnstrophyMass modes state :=
      lt_of_not_ge ratePos
    change 0 < S - (A / 2) * W at ratePositive
    have halfANonneg : 0 ≤ A / 2 :=
      div_nonneg APos.le (by norm_num)
    nlinarith [mul_nonneg halfANonneg WNonneg]
  have absS : |S| = S := abs_of_pos SPos
  rw [absS] at fourth
  have AWLt : (A / 2) * W < S := by
    have ratePositive :
        0 < S - (A / 2) * W := by
      change 0 < finiteStateVorticityStretchingWork modes state -
          (viscosity * (2 * Real.pi) ^ 2 / 2) *
            finiteStateVorticityEnstrophyMass modes state
      exact lt_of_not_ge ratePos
    exact sub_pos.mp ratePositive
  have fourthStrict : ((A / 2) * W) ^ 4 < S ^ 4 := by
    exact pow_lt_pow_left₀ AWLt
      (mul_nonneg (div_nonneg APos.le (by norm_num)) WNonneg)
      (by norm_num)
  have scaleLe : 24336 * M ^ 3 * W ^ 3 ≤
      24336 * level ^ 3 * W ^ 3 := by
    gcongr
  have gradientScaled :
      24336 * level ^ 3 * W ^ 3 <
        (A / 2) ^ 4 * W ^ 4 := by
    calc
      24336 * level ^ 3 * W ^ 3 <
          ((A ^ 4 * W) / 16) * W ^ 3 := by
        have divided : 24336 * level ^ 3 < A ^ 4 * W / 16 := by
          nlinarith
        exact mul_lt_mul_of_pos_right divided (pow_pos (by
          have WPos : 0 < W := by
            by_contra WNotPos
            have WZero : W = 0 := le_antisymm (le_of_not_gt WNotPos) WNonneg
            rw [WZero, mul_zero] at gradientLarge
            have : 0 ≤ 24336 * level ^ 3 := by positivity
            linarith
          exact WPos) 3)
      _ = (A / 2) ^ 4 * W ^ 4 := by ring
  nlinarith [fourthStrict, fourth, scaleLe, gradientScaled]

private theorem finiteMeasure_exists_valid_good_stretching_state
    {Time : Type*}
    [MeasurableSpace Time]
    (measure : Measure Time)
    [IsFiniteMeasure measure]
    (valid : Time → Prop)
    (stretching gradient : Time → Real)
    (viscosity threshold target duration : Real)
    (durationPos : 0 < duration)
    (viscosityNonneg : 0 ≤ viscosity)
    (targetPos : 0 < target)
    (measureDuration : measure.real Set.univ = duration)
    (validAE : ∀ᵐ time ∂measure, valid time)
    (gradientNonneg : ∀ᵐ time ∂measure, 0 ≤ gradient time)
    (rateIntegrable :
      Integrable (fun time => stretching time - viscosity * gradient time)
        measure)
    (badRateNonpos : ∀ time,
      threshold < gradient time →
        stretching time - viscosity * gradient time ≤ 0)
    (targetLtRate :
      target < ∫ time, stretching time - viscosity * gradient time ∂measure) :
    ∃ time, valid time ∧ gradient time ≤ threshold ∧
      target / duration < stretching time := by
  by_contra noTime
  push Not at noTime
  have ceilingNonneg : 0 ≤ target / duration :=
    div_nonneg targetPos.le durationPos.le
  have pointwise :
      (fun time => stretching time - viscosity * gradient time) ≤ᵐ[measure]
        fun _time => target / duration := by
    filter_upwards [validAE, gradientNonneg] with time timeValid gradientNonnegAt
    by_cases good : gradient time ≤ threshold
    · have stretchingLe := noTime time timeValid good
      exact (sub_le_self _
        (mul_nonneg viscosityNonneg gradientNonnegAt)).trans stretchingLe
    · exact (badRateNonpos time (lt_of_not_ge good)).trans ceilingNonneg
  have rateLe := integral_mono_ae rateIntegrable (integrable_const _) pointwise
  have constantIntegral :
      (∫ _time : Time, target / duration ∂measure) = target := by
    rw [integral_const, smul_eq_mul, measureDuration]
    field_simp [durationPos.ne']
  rw [constantIntegral] at rateLe
  linarith

private theorem physicalUnitCell_exists_norm_peak
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field) :
    ∃ center ∈ physicalUnitCell,
      ∀ x ∈ physicalUnitCell, ‖field x‖ ≤ ‖field center‖ := by
  obtain ⟨center, centerMem, peak⟩ :=
    physicalUnitCell_isCompact.exists_isMaxOn
      (by
        refine ⟨0, ?_⟩
        rw [mem_physicalUnitCell_iff]
        simp)
      fieldContinuous.norm.continuousOn
  exact ⟨center, centerMem, fun _x xMem => peak xMem⟩

private theorem physicalUnitCell_finiteRealComplexFourierField_mass_parseval
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    (∫ x in physicalUnitCell,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  have parseval :=
    physicalUnitCell_finiteRealComplexFourierField_parseval_of_observer
      modes state (fun wave waveMem => by
        rw [physicalUnitCellComplexFourierCoordinate_finiteRealComplexFourierField]
        funext coordinate
        rw [if_pos waveMem, if_pos (negClosed waveMem), reality wave]
        simp [vectorConj])
  rw [show (∫ x in physicalUnitCell,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
      ∫ x in physicalUnitCell,
        velocityDot
          (finiteRealComplexFourierField modes state)
          (finiteRealComplexFourierField modes state) x by
    apply integral_congr_ae
    filter_upwards with x
    unfold velocityDot
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]]
  rw [parseval]
  unfold finiteStateVorticityCoefficientEnstrophy
  apply Finset.sum_congr rfl
  intro wave _
  exact
    (complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq
      (state wave)).symm

private theorem physicalUnitCell_finiteField_fourth_le_peak_sq_mul_mass
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    ∃ center ∈ physicalUnitCell,
      (∫ x in physicalUnitCell,
        ‖finiteRealComplexFourierField modes state x‖ ^ 4) ≤
        ‖finiteRealComplexFourierField modes state center‖ ^ 2 *
          finiteStateVorticityCoefficientEnstrophy modes state := by
  let field : PhysicalSpace → PhysicalSpace :=
    finiteRealComplexFourierField modes state
  obtain ⟨center, centerMem, peak⟩ :=
    physicalUnitCell_exists_norm_peak field
      (finiteRealComplexFourierField_contDiff modes state).continuous
  refine ⟨center, centerMem, ?_⟩
  have fourthIntegrable :
      IntegrableOn (fun x => ‖field x‖ ^ 4) physicalUnitCell volume :=
    ((finiteRealComplexFourierField_contDiff modes state).continuous.norm.pow 4)
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  have majorantIntegrable :
      IntegrableOn
        (fun x => ‖field center‖ ^ 2 * ‖field x‖ ^ 2)
        physicalUnitCell volume :=
    (((finiteRealComplexFourierField_contDiff modes state).continuous.norm.pow 2)
      |>.const_mul (‖field center‖ ^ 2))
      |>.continuousOn.integrableOn_compact physicalUnitCell_isCompact
  calc
    (∫ x in physicalUnitCell, ‖field x‖ ^ 4) ≤
        ∫ x in physicalUnitCell,
          ‖field center‖ ^ 2 * ‖field x‖ ^ 2 := by
      apply setIntegral_mono_on fourthIntegrable majorantIntegrable
        physicalUnitCell_isCompact.measurableSet
      intro x xMem
      have normLe := peak x xMem
      calc
        ‖field x‖ ^ 4 = ‖field x‖ ^ 2 * ‖field x‖ ^ 2 := by ring
        _ ≤ ‖field center‖ ^ 2 * ‖field x‖ ^ 2 := by
          gcongr
        _ = _ := rfl
    _ = ‖field center‖ ^ 2 *
        finiteStateVorticityCoefficientEnstrophy modes state := by
      rw [integral_const_mul]
      rw [physicalUnitCell_finiteRealComplexFourierField_mass_parseval
        modes negClosed state reality]

private theorem finiteStretching_abs_le_actual_peak_mul_mass
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    ∃ center ∈ physicalUnitCell,
      |finiteStateVorticityStretchingWork modes state| ≤
        ‖finiteRealComplexFourierField modes state center‖ *
          finiteStateVorticityCoefficientEnstrophy modes state := by
  let field : PhysicalSpace → PhysicalSpace :=
    finiteRealComplexFourierField modes state
  let fourth : Real :=
    ∫ x in physicalUnitCell, ‖field x‖ ^ 4
  let mass := finiteStateVorticityCoefficientEnstrophy modes state
  obtain ⟨center, centerMem, fourthLe⟩ :=
    physicalUnitCell_finiteField_fourth_le_peak_sq_mul_mass
      modes negClosed state reality
  refine ⟨center, centerMem, ?_⟩
  have cauchy :=
    ThreeDimensionalVorticityCoefficientClosedEnstrophyPhysicalBridge.finiteStateVorticityStretchingWork_abs_le_physicalL4
      modes zeroNotMem (fun wave waveMem => negClosed waveMem)
      state supported transverse reality
  change |finiteStateVorticityStretchingWork modes state| ≤
    Real.sqrt fourth * Real.sqrt mass at cauchy
  change fourth ≤ ‖field center‖ ^ 2 * mass at fourthLe
  have fourthNonneg : 0 ≤ fourth := by
    dsimp only [fourth]
    exact integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have massNonneg : 0 ≤ mass := by
    dsimp only [mass]
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg (state wave)
  have cauchySq :
      |finiteStateVorticityStretchingWork modes state| ^ 2 ≤
        fourth * mass := by
    have squared :=
      (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 cauchy
    rw [mul_pow, Real.sq_sqrt fourthNonneg,
      Real.sq_sqrt massNonneg] at squared
    exact squared
  have targetSq :
      |finiteStateVorticityStretchingWork modes state| ^ 2 ≤
        (‖field center‖ * mass) ^ 2 := by
    calc
      |finiteStateVorticityStretchingWork modes state| ^ 2 ≤
          fourth * mass := cauchySq
      _ ≤ (‖field center‖ ^ 2 * mass) * mass :=
        mul_le_mul_of_nonneg_right fourthLe massNonneg
      _ = (‖field center‖ * mass) ^ 2 := by ring
  exact
    (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) massNonneg)).1 targetSq

private theorem closedBall_mass_lower_of_peak_and_lipschitz
    (field : PhysicalSpace → PhysicalSpace)
    (fieldContinuous : Continuous field)
    (center : PhysicalSpace)
    (peakFloor lipschitz : Real)
    (peakFloorPos : 0 < peakFloor)
    (lipschitzPos : 0 < lipschitz)
    (peak : peakFloor ≤ ‖field center‖)
    (modulus : ∀ point,
      ‖field point - field center‖ ≤
        lipschitz * ‖point - center‖) :
    (peakFloor / 2) ^ 2 *
        (volume (Metric.closedBall center
          (peakFloor / (2 * lipschitz)))).toReal ≤
      ∫ point in Metric.closedBall center
          (peakFloor / (2 * lipschitz)),
        ‖field point‖ ^ 2 := by
  let radius := peakFloor / (2 * lipschitz)
  have radiusPos : 0 < radius := by
    dsimp only [radius]
    positivity
  have fieldIntegrable :
      IntegrableOn (fun point => ‖field point‖ ^ 2)
        (Metric.closedBall center radius) volume :=
    (fieldContinuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall center radius)
  have constantIntegrable :
      IntegrableOn (fun _point : PhysicalSpace => (peakFloor / 2) ^ 2)
        (Metric.closedBall center radius) volume :=
    integrableOn_const
      (isCompact_closedBall center radius).measure_lt_top.ne
  have lower :
      (∫ _point : PhysicalSpace in Metric.closedBall center radius,
          (peakFloor / 2) ^ 2) ≤
        ∫ point in Metric.closedBall center radius,
          ‖field point‖ ^ 2 := by
    apply setIntegral_mono_on constantIntegrable fieldIntegrable
      (isCompact_closedBall center radius).measurableSet
    intro point pointMem
    rw [Metric.mem_closedBall, dist_eq_norm] at pointMem
    have differenceLe :
        ‖field point - field center‖ ≤ peakFloor / 2 := by
      calc
        ‖field point - field center‖ ≤
            lipschitz * ‖point - center‖ := modulus point
        _ ≤ lipschitz * radius :=
          mul_le_mul_of_nonneg_left pointMem lipschitzPos.le
        _ = peakFloor / 2 := by
          dsimp only [radius]
          field_simp [lipschitzPos.ne']
    have normLower : peakFloor / 2 ≤ ‖field point‖ := by
      have triangle :
          ‖field center‖ ≤
            ‖field point - field center‖ + ‖field point‖ := by
        calc
          ‖field center‖ =
              ‖(field center - field point) + field point‖ := by
            rw [sub_add_cancel]
          _ ≤ ‖field center - field point‖ + ‖field point‖ :=
            norm_add_le _ _
          _ = ‖field point - field center‖ + ‖field point‖ := by
            rw [norm_sub_rev]
      linarith
    exact pow_le_pow_left₀ (by positivity) normLower 2
  calc
    (peakFloor / 2) ^ 2 *
        (volume (Metric.closedBall center radius)).toReal =
        ∫ _point : PhysicalSpace in Metric.closedBall center radius,
          (peakFloor / 2) ^ 2 := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, measureReal_def]
      ring
    _ ≤ _ := lower

private theorem finiteStretching_generates_closedBall_mass
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (stretchingFloor massCeiling lipschitzCeiling : Real)
    (stretchingFloorPos : 0 < stretchingFloor)
    (massCeilingPos : 0 < massCeiling)
    (lipschitzCeilingPos : 0 < lipschitzCeiling)
    (stretchingLower : stretchingFloor ≤
      |finiteStateVorticityStretchingWork modes state|)
    (massUpper :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ massCeiling)
    (lipschitzUpper :
      Real.sqrt
        ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state) ≤
        lipschitzCeiling) :
    ∃ center ∈ physicalUnitCell,
      ((stretchingFloor / massCeiling) / 2) ^ 2 *
          (volume (Metric.closedBall center
            ((stretchingFloor / massCeiling) /
              (2 * lipschitzCeiling)))).toReal ≤
        ∫ point in Metric.closedBall center
            ((stretchingFloor / massCeiling) /
              (2 * lipschitzCeiling)),
          ‖finiteRealComplexFourierField modes state point‖ ^ 2 := by
  let field : PhysicalSpace → PhysicalSpace :=
    finiteRealComplexFourierField modes state
  obtain ⟨center, centerMem, stretchingToPeak⟩ :=
    finiteStretching_abs_le_actual_peak_mul_mass
      modes zeroNotMem negClosed state supported transverse reality
  refine ⟨center, centerMem, ?_⟩
  have massNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes state := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg (state wave)
  have peakFloor :
      stretchingFloor / massCeiling ≤ ‖field center‖ := by
    have floorToPeakMass :
        stretchingFloor ≤
          ‖field center‖ * massCeiling := by
      calc
        stretchingFloor ≤
            |finiteStateVorticityStretchingWork modes state| :=
          stretchingLower
        _ ≤ ‖field center‖ *
            finiteStateVorticityCoefficientEnstrophy modes state :=
          stretchingToPeak
        _ ≤ ‖field center‖ * massCeiling :=
          mul_le_mul_of_nonneg_left massUpper (norm_nonneg _)
    exact (div_le_iff₀ massCeilingPos).2 floorToPeakMass
  have modulus (point : PhysicalSpace) :
      ‖field point - field center‖ ≤
        lipschitzCeiling * ‖point - center‖ := by
    calc
      ‖field point - field center‖ ≤
          Real.sqrt
              ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
                finiteStateVorticityEnstrophyMass modes state) *
            ‖point - center‖ :=
        finiteRealComplexFourierField_norm_sub_le_sqrt_card_gradientMass_mul_norm_sub
          modes state center point
      _ ≤ lipschitzCeiling * ‖point - center‖ :=
        mul_le_mul_of_nonneg_right lipschitzUpper (norm_nonneg _)
  exact closedBall_mass_lower_of_peak_and_lipschitz
    field (finiteRealComplexFourierField_contDiff modes state).continuous
    center (stretchingFloor / massCeiling) lipschitzCeiling
    (div_pos stretchingFloorPos massCeilingPos) lipschitzCeilingPos
    peakFloor modulus

private theorem parabolicScaledField_closedBall_mass_eq
    (field : PhysicalSpace → PhysicalSpace)
    (center : PhysicalSpace)
    (scale radius : Real)
    (scalePos : 0 < scale)
    (radiusNonneg : 0 ≤ radius) :
    (∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
      ‖(scale ^ 2 : Real) • field (center + scale • x)‖ ^ 2) =
      scale *
        ∫ y in Metric.closedBall center (scale * radius),
          ‖field y‖ ^ 2 := by
  let density : PhysicalSpace → Real := fun y => ‖field y‖ ^ 2
  have translated :
      (∫ x in Metric.closedBall (0 : PhysicalSpace) (scale * radius),
          density (center + x)) =
        ∫ y in Metric.closedBall center (scale * radius), density y := by
    have generated :=
      (measurePreserving_add_left volume center).setIntegral_preimage_emb
        (Homeomorph.addLeft center).isClosedEmbedding.measurableEmbedding
        density (Metric.closedBall center (scale * radius))
    simpa only [preimage_add_closedBall, add_zero, sub_self] using generated
  have scaled :=
    MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (volume : Measure PhysicalSpace)
      (fun y : PhysicalSpace => density (center + y))
      (Metric.closedBall (0 : PhysicalSpace) radius) scalePos
  have scaledSet :
      scale • Metric.closedBall (0 : PhysicalSpace) radius =
        Metric.closedBall (0 : PhysicalSpace) (scale * radius) := by
    rw [_root_.smul_closedBall scale (0 : PhysicalSpace) radiusNonneg,
      smul_zero,
      Real.norm_of_nonneg scalePos.le]
  rw [scaledSet, translated] at scaled
  calc
    (∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
      ‖(scale ^ 2 : Real) • field (center + scale • x)‖ ^ 2) =
        scale ^ 4 *
          ∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
            density (center + scale • x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [density]
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg scale)]
      ring
    _ = scale ^ 4 *
        ((scale ^ Module.finrank Real PhysicalSpace)⁻¹ *
          ∫ y in Metric.closedBall center (scale * radius), density y) := by
      rw [scaled]
      rfl
    _ = scale *
        ∫ y in Metric.closedBall center (scale * radius), density y := by
      rw [show Module.finrank Real PhysicalSpace = 3 by simp [PhysicalSpace]]
      field_simp [scalePos.ne']

private theorem parabolicScaledVelocityField_closedBall_mass_eq
    (field : PhysicalSpace → PhysicalSpace)
    (center : PhysicalSpace)
    (scale radius : Real)
    (scalePos : 0 < scale)
    (radiusNonneg : 0 ≤ radius) :
    (∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
      ‖scale • field (center + scale • x)‖ ^ 2) =
      scale⁻¹ *
        ∫ y in Metric.closedBall center (scale * radius),
          ‖field y‖ ^ 2 := by
  let density : PhysicalSpace → Real := fun y => ‖field y‖ ^ 2
  have translated :
      (∫ x in Metric.closedBall (0 : PhysicalSpace) (scale * radius),
          density (center + x)) =
        ∫ y in Metric.closedBall center (scale * radius), density y := by
    have generated :=
      (measurePreserving_add_left volume center).setIntegral_preimage_emb
        (Homeomorph.addLeft center).isClosedEmbedding.measurableEmbedding
        density (Metric.closedBall center (scale * radius))
    simpa only [preimage_add_closedBall, add_zero, sub_self] using generated
  have scaled :=
    MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (volume : Measure PhysicalSpace)
      (fun y : PhysicalSpace => density (center + y))
      (Metric.closedBall (0 : PhysicalSpace) radius) scalePos
  have scaledSet :
      scale • Metric.closedBall (0 : PhysicalSpace) radius =
        Metric.closedBall (0 : PhysicalSpace) (scale * radius) := by
    rw [_root_.smul_closedBall scale (0 : PhysicalSpace) radiusNonneg,
      smul_zero, Real.norm_of_nonneg scalePos.le]
  rw [scaledSet, translated] at scaled
  calc
    (∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
      ‖scale • field (center + scale • x)‖ ^ 2) =
        scale ^ 2 *
          ∫ x in Metric.closedBall (0 : PhysicalSpace) radius,
            density (center + scale • x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [density]
      rw [norm_smul, Real.norm_of_nonneg scalePos.le]
      ring
    _ = scale ^ 2 *
        ((scale ^ Module.finrank Real PhysicalSpace)⁻¹ *
          ∫ y in Metric.closedBall center (scale * radius), density y) := by
      rw [scaled]
      rfl
    _ = scale⁻¹ *
        ∫ y in Metric.closedBall center (scale * radius), density y := by
      rw [show Module.finrank Real PhysicalSpace = 3 by simp [PhysicalSpace]]
      field_simp [scalePos.ne']

private def shiftedPhysicalUnitCell
    (shift : IntegerShift) : Set PhysicalSpace :=
  (fun x => latticeShift shift + x) '' physicalUnitCell

private theorem preimage_add_latticeShift_shiftedPhysicalUnitCell
    (shift : IntegerShift) :
    (fun x : PhysicalSpace => latticeShift shift + x) ⁻¹'
        shiftedPhysicalUnitCell shift = physicalUnitCell := by
  ext x
  simp only [shiftedPhysicalUnitCell, Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨y, yMem, equality⟩
    have : y = x := add_left_cancel equality
    simpa [this] using yMem
  · intro xMem
    exact ⟨x, xMem, rfl⟩

private theorem shiftedPhysicalUnitCell_finiteField_mass_eq
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (shift : IntegerShift) :
    (∫ x in shiftedPhysicalUnitCell shift,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
      finiteStateVorticityCoefficientEnstrophy modes state := by
  let density : PhysicalSpace → Real := fun x =>
    ‖finiteRealComplexFourierField modes state x‖ ^ 2
  have translated :=
    (measurePreserving_add_left volume (latticeShift shift))
      |>.setIntegral_preimage_emb
        (Homeomorph.addLeft
          (latticeShift shift)).isClosedEmbedding.measurableEmbedding
        density (shiftedPhysicalUnitCell shift)
  rw [preimage_add_latticeShift_shiftedPhysicalUnitCell shift] at translated
  have periodic (x : PhysicalSpace) :
      density (latticeShift shift + x) = density x := by
    dsimp only [density]
    rw [add_comm,
      finiteRealComplexFourierField_latticePeriodic modes state shift]
  have cellMass :=
    physicalUnitCell_finiteRealComplexFourierField_parabolicScale_mass
      modes negClosed state reality 1 zero_lt_one
  have oneCell : (1 : Real) • physicalUnitCell = physicalUnitCell := by
    ext x
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨y, yMem, equality⟩
      have equality' : y = x := by
        simpa only [one_smul] using equality
      exact equality' ▸ yMem
    · intro xMem
      exact ⟨x, xMem, one_smul Real x⟩
  rw [inv_one, oneCell] at cellMass
  calc
    (∫ x in shiftedPhysicalUnitCell shift,
      ‖finiteRealComplexFourierField modes state x‖ ^ 2) =
        ∫ x in physicalUnitCell,
          density (latticeShift shift + x) := translated.symm
    _ = ∫ x in physicalUnitCell, density x := by
      apply integral_congr_ae
      filter_upwards with x
      exact periodic x
    _ = finiteStateVorticityCoefficientEnstrophy modes state := by
      simpa [density] using cellMass

private theorem closedBall_subset_biUnion_shiftedPhysicalUnitCell
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (scale spatialRadius : Real)
    (_scaleNonneg : 0 ≤ scale)
    (scaleLeOne : scale ≤ 1)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real)) :
    Metric.closedBall center (scale * spatialRadius) ⊆
      ⋃ shift ∈ integerWaveFrequencyCube coverRadius,
        shiftedPhysicalUnitCell shift := by
  intro y yMem
  let shift : IntegerShift := fun coordinate => ⌊y coordinate⌋
  let base : PhysicalSpace := y - latticeShift shift
  have distanceLe : ‖y - center‖ ≤ scale * spatialRadius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using yMem
  have scaleRadiusLe : scale * spatialRadius ≤ spatialRadius := by
    nlinarith
  have coordinateBounds (coordinate : Coordinate) :
      -spatialRadius ≤ y coordinate ∧
        y coordinate ≤ spatialRadius + 1 := by
    have coordinateNorm :
        |(y - center) coordinate| ≤ ‖y - center‖ := by
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (y - center) coordinate
    change |y coordinate - center coordinate| ≤ ‖y - center‖ at coordinateNorm
    have coordinateDifference :
        |y coordinate - center coordinate| ≤ spatialRadius :=
      coordinateNorm.trans (distanceLe.trans scaleRadiusLe)
    rcases (mem_physicalUnitCell_iff center).mp centerMem coordinate with
      ⟨centerNonneg, centerLe⟩
    have signed := abs_le.mp coordinateDifference
    constructor <;> linarith
  have shiftMem : shift ∈ integerWaveFrequencyCube coverRadius := by
    rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
    intro coordinate
    rw [Finset.mem_Icc]
    have yBounds := coordinateBounds coordinate
    have floorCastLe :
        (⌊y coordinate⌋ : Real) ≤ (coverRadius : Real) := by
      calc
        (⌊y coordinate⌋ : Real) ≤ y coordinate := Int.floor_le _
        _ ≤ spatialRadius + 1 := yBounds.2
        _ ≤ (coverRadius : Real) := by linarith
    have negCoverLeFloorCast :
        -((coverRadius : Real)) ≤ (⌊y coordinate⌋ : Real) := by
      have floorWindow := Int.lt_floor_add_one (y coordinate)
      push_cast at floorWindow
      linarith
    constructor
    · exact_mod_cast negCoverLeFloorCast
    · exact_mod_cast floorCastLe
  have baseMem : base ∈ physicalUnitCell := by
    rw [mem_physicalUnitCell_iff]
    intro coordinate
    change
      0 ≤ y coordinate - (⌊y coordinate⌋ : Real) ∧
        y coordinate - (⌊y coordinate⌋ : Real) ≤ 1
    constructor
    · exact sub_nonneg.mpr (Int.floor_le _)
    · have floorWindow := Int.lt_floor_add_one (y coordinate)
      push_cast at floorWindow
      linarith
  refine Set.mem_iUnion.2 ⟨shift, ?_⟩
  refine Set.mem_iUnion.2 ⟨shiftMem, ?_⟩
  refine ⟨base, baseMem, ?_⟩
  dsimp only [base]
  abel

private theorem closedBall_finiteField_mass_le_cover
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (scale spatialRadius : Real)
    (scaleNonneg : 0 ≤ scale)
    (scaleLeOne : scale ≤ 1)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real)) :
    (∫ y in Metric.closedBall center (scale * spatialRadius),
      ‖finiteRealComplexFourierField modes state y‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) *
        finiteStateVorticityCoefficientEnstrophy modes state := by
  let shifts := integerWaveFrequencyCube coverRadius
  let density : PhysicalSpace → Real := fun y =>
    ‖finiteRealComplexFourierField modes state y‖ ^ 2
  let cells : ↑shifts → Set PhysicalSpace := fun shift =>
    shiftedPhysicalUnitCell shift.1
  have coverRaw :=
    closedBall_subset_biUnion_shiftedPhysicalUnitCell
      center centerMem scale spatialRadius scaleNonneg scaleLeOne
      spatialRadiusNonneg coverRadius coverRadiusLarge
  have cover :
      Metric.closedBall center (scale * spatialRadius) ⊆
        ⋃ shift : ↑shifts, cells shift := by
    intro y yMem
    obtain ⟨shift, shiftMem, yCell⟩ := by
      simpa only [Set.mem_iUnion] using coverRaw yMem
    exact Set.mem_iUnion.2 ⟨⟨shift, shiftMem⟩, yCell⟩
  have measureLe :
      volume.restrict (Metric.closedBall center (scale * spatialRadius)) ≤
        Measure.sum fun shift : ↑shifts =>
          volume.restrict (cells shift) :=
    (Measure.restrict_mono cover le_rfl).trans Measure.restrict_iUnion_le
  have densityContinuous : Continuous density := by
    dsimp only [density]
    exact
      (finiteRealComplexFourierField_contDiff modes state).continuous.norm.pow 2
  have cellCompact (shift : ↑shifts) : IsCompact (cells shift) := by
    dsimp only [cells]
    exact physicalUnitCell_isCompact.image
      (continuous_const.add continuous_id)
  have cellIntegrable (shift : ↑shifts) :
      Integrable density (volume.restrict (cells shift)) :=
    densityContinuous.continuousOn.integrableOn_compact (cellCompact shift)
  have sumIntegrable :
      Integrable density
        (Measure.sum fun shift : ↑shifts =>
          volume.restrict (cells shift)) :=
    integrable_sum_measure cellIntegrable (hasSum_fintype _).summable
  have comparison := integral_mono_measure measureLe
    (Filter.Eventually.of_forall fun y => sq_nonneg
      ‖finiteRealComplexFourierField modes state y‖)
    sumIntegrable
  rw [integral_sum_measure sumIntegrable] at comparison
  have eachCell (shift : ↑shifts) :
      (∫ y, density y ∂volume.restrict (cells shift)) =
        finiteStateVorticityCoefficientEnstrophy modes state := by
    simpa only [density, cells] using
      shiftedPhysicalUnitCell_finiteField_mass_eq
        modes negClosed state reality shift.1
  simp_rw [eachCell] at comparison
  simpa only [density, shifts, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using comparison

private theorem scaledFiniteField_ball_mass_le_cellCover
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (scale spatialRadius : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real)) :
    (∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
      ‖(scale ^ 2 : Real) •
        finiteRealComplexFourierField modes state
          (center + scale • x)‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) *
        (scale * finiteStateVorticityCoefficientEnstrophy modes state) := by
  rw [parabolicScaledField_closedBall_mass_eq
    (finiteRealComplexFourierField modes state) center scale spatialRadius
    scalePos spatialRadiusNonneg]
  have originalMass := closedBall_finiteField_mass_le_cover
    modes negClosed state reality center centerMem scale spatialRadius
    scalePos.le scaleLeOne spatialRadiusNonneg coverRadius coverRadiusLarge
  calc
    scale *
        (∫ y in Metric.closedBall center (scale * spatialRadius),
          ‖finiteRealComplexFourierField modes state y‖ ^ 2) ≤
        scale *
          (((integerWaveFrequencyCube coverRadius).card : Real) *
            finiteStateVorticityCoefficientEnstrophy modes state) :=
      mul_le_mul_of_nonneg_left originalMass scalePos.le
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) *
        (scale * finiteStateVorticityCoefficientEnstrophy modes state) := by
      ring

private theorem finiteVelocityState_reality
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (finiteComplexVorticityState modes
        (finiteStateVelocityCoefficient state)) := by
  intro wave
  have negMemIff : waveNeg wave ∈ modes ↔ wave ∈ modes := by
    constructor
    · intro negMem
      simpa using negClosed negMem
    · exact negClosed
  rw [finiteComplexVorticityState_apply,
    finiteComplexVorticityState_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem, if_pos (negMemIff.mpr waveMem)]
    exact finiteStateVelocityCoefficient_waveNeg (reality wave)
  · rw [if_neg waveMem, if_neg (not_congr negMemIff |>.mpr waveMem)]
    exact vectorConj_zero.symm

private theorem finiteVelocityState_field_eq
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField modes
        (finiteComplexVorticityState modes
          (finiteStateVelocityCoefficient state)) point =
      finiteRealComplexFourierField modes
        (finiteStateVelocityCoefficient state) point := by
  unfold finiteRealComplexFourierField
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [finiteComplexVorticityState_apply, if_pos waveMem]

private theorem scaledFiniteVelocityField_ball_mass_le_cellCover
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (scale spatialRadius : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real)) :
    (∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
      ‖scale •
        finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient state)
          (center + scale • x)‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) *
        (scale⁻¹ *
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient state))) := by
  rw [parabolicScaledVelocityField_closedBall_mass_eq
    (finiteRealComplexFourierField modes
      (finiteStateVelocityCoefficient state)) center scale spatialRadius
    scalePos spatialRadiusNonneg]
  have velocityReality :=
    finiteVelocityState_reality modes negClosed state reality
  have originalMass := closedBall_finiteField_mass_le_cover
    modes negClosed
      (finiteComplexVorticityState modes
        (finiteStateVelocityCoefficient state)) velocityReality
      center centerMem scale spatialRadius scalePos.le scaleLeOne
      spatialRadiusNonneg coverRadius coverRadiusLarge
  have originalMass' :
      (∫ y in Metric.closedBall center (scale * spatialRadius),
        ‖finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient state) y‖ ^ 2) ≤
        ((integerWaveFrequencyCube coverRadius).card : Real) *
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient state)) := by
    simpa only [finiteVelocityState_field_eq] using originalMass
  calc
    scale⁻¹ *
        (∫ y in Metric.closedBall center (scale * spatialRadius),
          ‖finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient state) y‖ ^ 2) ≤
      scale⁻¹ *
        (((integerWaveFrequencyCube coverRadius).card : Real) *
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient state))) :=
        mul_le_mul_of_nonneg_left originalMass'
          (inv_nonneg.mpr scalePos.le)
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) *
        (scale⁻¹ *
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient state))) := by ring

private theorem scaledFiniteField_spacetime_ball_mass_le_cellCover
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (path : Real → ComplexVorticityHilbertState)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (anchor scale timeLength spatialRadius : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (timeLengthNonneg : 0 ≤ timeLength)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real))
    (reality : ∀ᵐ scaledTime
      ∂volume.restrict (Set.Icc (0 : Real) timeLength),
        FiniteStateFourierReality
          (path (anchor + scale ^ 2 * scaledTime)))
    (scaledFieldIntegrable :
      IntervalIntegrable
        (fun scaledTime =>
          ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            ‖(scale ^ 2 : Real) •
              finiteRealComplexFourierField modes
                (path (anchor + scale ^ 2 * scaledTime))
                (center + scale • x)‖ ^ 2)
        volume 0 timeLength)
    (scaledMassIntegrable :
      IntervalIntegrable
        (fun scaledTime =>
          finiteStateVorticityCoefficientEnstrophy modes
            (path (anchor + scale ^ 2 * scaledTime)))
        volume 0 timeLength) :
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes
            (path (anchor + scale ^ 2 * scaledTime))
            (center + scale • x)‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
        ∫ originalTime in anchor..anchor + scale ^ 2 * timeLength,
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime) := by
  let scaledFieldMass : Real → Real := fun scaledTime =>
    ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
      ‖(scale ^ 2 : Real) •
        finiteRealComplexFourierField modes
          (path (anchor + scale ^ 2 * scaledTime))
          (center + scale • x)‖ ^ 2
  let scaledCoefficientMass : Real → Real := fun scaledTime =>
    finiteStateVorticityCoefficientEnstrophy modes
      (path (anchor + scale ^ 2 * scaledTime))
  have scaledRightIntegrable :
      IntervalIntegrable
        (fun scaledTime =>
          ((integerWaveFrequencyCube coverRadius).card : Real) * scale *
            scaledCoefficientMass scaledTime)
        volume 0 timeLength :=
    scaledMassIntegrable.const_mul
      (((integerWaveFrequencyCube coverRadius).card : Real) * scale)
  have pointwise : ∀ᵐ scaledTime
      ∂volume.restrict (Set.Icc (0 : Real) timeLength),
      scaledFieldMass scaledTime ≤
        ((integerWaveFrequencyCube coverRadius).card : Real) * scale *
          scaledCoefficientMass scaledTime := by
    filter_upwards [reality] with scaledTime scaledReality
    simpa only [scaledFieldMass, scaledCoefficientMass, mul_assoc] using
      scaledFiniteField_ball_mass_le_cellCover modes negClosed
        (path (anchor + scale ^ 2 * scaledTime)) scaledReality center centerMem
        scale spatialRadius scalePos scaleLeOne spatialRadiusNonneg
        coverRadius coverRadiusLarge
  have integrated := intervalIntegral.integral_mono_ae_restrict
    timeLengthNonneg scaledFieldIntegrable scaledRightIntegrable pointwise
  have changeVariables :=
    intervalIntegral.smul_integral_comp_add_mul
      (f := fun originalTime =>
        finiteStateVorticityCoefficientEnstrophy modes (path originalTime))
      (a := (0 : Real)) (b := timeLength) (c := scale ^ 2) anchor
  have changeVariables' :
      scale ^ 2 *
          ∫ scaledTime in 0..timeLength,
            scaledCoefficientMass scaledTime =
        ∫ originalTime in anchor..anchor + scale ^ 2 * timeLength,
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime) := by
    simpa only [smul_eq_mul, mul_zero, add_zero, scaledCoefficientMass] using
      changeVariables
  rw [intervalIntegral.integral_const_mul] at integrated
  calc
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes
            (path (anchor + scale ^ 2 * scaledTime))
            (center + scale • x)‖ ^ 2) =
        ∫ scaledTime in 0..timeLength,
          scaledFieldMass scaledTime := by rfl
    _ ≤ ((integerWaveFrequencyCube coverRadius).card : Real) * scale *
          ∫ scaledTime in 0..timeLength,
            scaledCoefficientMass scaledTime := integrated
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
        ∫ originalTime in anchor..anchor + scale ^ 2 * timeLength,
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime) := by
      rw [← changeVariables']
      field_simp [scalePos.ne']

private theorem
    scaledFiniteField_spacetime_ball_mass_le_cellCover_originalReality
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (path : Real → ComplexVorticityHilbertState)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (anchor finish scale timeLength spatialRadius : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (timeLengthNonneg : 0 ≤ timeLength)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (finishEq : finish = anchor + scale ^ 2 * timeLength)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real))
    (reality : ∀ᵐ originalTime
      ∂volume.restrict (Set.Icc anchor finish),
        FiniteStateFourierReality (path originalTime))
    (fieldIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            ‖(scale ^ 2 : Real) •
              finiteRealComplexFourierField modes (path originalTime)
                (center + scale • x)‖ ^ 2)
        volume anchor finish)
    (coefficientIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime))
        volume anchor finish) :
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes
            (path (anchor + scale ^ 2 * scaledTime))
            (center + scale • x)‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
        ∫ originalTime in anchor..finish,
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime) := by
  let fieldMass : Real → Real := fun originalTime =>
    ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
      ‖(scale ^ 2 : Real) •
        finiteRealComplexFourierField modes (path originalTime)
          (center + scale • x)‖ ^ 2
  let coefficientMass : Real → Real := fun originalTime =>
    finiteStateVorticityCoefficientEnstrophy modes (path originalTime)
  have anchorLeFinish : anchor ≤ finish := by
    rw [finishEq]
    exact le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg scale) timeLengthNonneg)
  have rightIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          ((integerWaveFrequencyCube coverRadius).card : Real) * scale *
            coefficientMass originalTime)
        volume anchor finish :=
    coefficientIntegrable.const_mul
      (((integerWaveFrequencyCube coverRadius).card : Real) * scale)
  have pointwise : ∀ᵐ originalTime
      ∂volume.restrict (Set.Icc anchor finish),
      fieldMass originalTime ≤
        ((integerWaveFrequencyCube coverRadius).card : Real) * scale *
          coefficientMass originalTime := by
    filter_upwards [reality] with originalTime originalReality
    simpa only [fieldMass, coefficientMass, mul_assoc] using
      scaledFiniteField_ball_mass_le_cellCover modes negClosed
        (path originalTime) originalReality center centerMem scale spatialRadius
        scalePos scaleLeOne spatialRadiusNonneg coverRadius coverRadiusLarge
  have integrated := intervalIntegral.integral_mono_ae_restrict
    anchorLeFinish fieldIntegrable rightIntegrable pointwise
  rw [intervalIntegral.integral_const_mul] at integrated
  have changeVariables :=
    intervalIntegral.smul_integral_comp_add_mul
      (f := fieldMass) (a := (0 : Real)) (b := timeLength)
      (c := scale ^ 2) anchor
  have changeVariables' :
      scale ^ 2 *
          ∫ scaledTime in 0..timeLength,
            fieldMass (anchor + scale ^ 2 * scaledTime) =
        ∫ originalTime in anchor..finish,
          fieldMass originalTime := by
    rw [finishEq]
    simpa only [smul_eq_mul, mul_zero, add_zero] using changeVariables
  have scaled := mul_le_mul_of_nonneg_left integrated
    (inv_nonneg.mpr (sq_nonneg scale))
  calc
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes
            (path (anchor + scale ^ 2 * scaledTime))
            (center + scale • x)‖ ^ 2) =
        ∫ scaledTime in 0..timeLength,
          fieldMass (anchor + scale ^ 2 * scaledTime) := by rfl
    _ = (scale ^ 2)⁻¹ *
        ∫ originalTime in anchor..finish, fieldMass originalTime := by
      rw [← changeVariables']
      field_simp [scalePos.ne']
    _ ≤ (scale ^ 2)⁻¹ *
        (((integerWaveFrequencyCube coverRadius).card : Real) * scale *
          ∫ originalTime in anchor..finish,
            coefficientMass originalTime) := scaled
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
        ∫ originalTime in anchor..finish,
          finiteStateVorticityCoefficientEnstrophy modes
            (path originalTime) := by
      dsimp only [coefficientMass]
      field_simp [scalePos.ne']

private theorem
    scaledFiniteVelocityField_spacetime_ball_mass_le_cellCover_originalReality
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (path : Real → ComplexVorticityHilbertState)
    (center : PhysicalSpace)
    (centerMem : center ∈ physicalUnitCell)
    (anchor finish scale timeLength spatialRadius : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (timeLengthNonneg : 0 ≤ timeLength)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (finishEq : finish = anchor + scale ^ 2 * timeLength)
    (coverRadius : Nat)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real))
    (reality : ∀ᵐ originalTime
      ∂volume.restrict (Set.Icc anchor finish),
        FiniteStateFourierReality (path originalTime))
    (fieldIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            ‖scale •
              finiteRealComplexFourierField modes
                (finiteStateVelocityCoefficient (path originalTime))
                (center + scale • x)‖ ^ 2)
        volume anchor finish)
    (coefficientIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient (path originalTime))))
        volume anchor finish) :
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient
              (path (anchor + scale ^ 2 * scaledTime)))
            (center + scale • x)‖ ^ 2) ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ ^ 3 *
        ∫ originalTime in anchor..finish,
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient (path originalTime))) := by
  let fieldMass : Real → Real := fun originalTime =>
    ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
      ‖scale •
        finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient (path originalTime))
          (center + scale • x)‖ ^ 2
  let coefficientMass : Real → Real := fun originalTime =>
    finiteStateVorticityCoefficientEnstrophy modes
      (finiteComplexVorticityState modes
        (finiteStateVelocityCoefficient (path originalTime)))
  have anchorLeFinish : anchor ≤ finish := by
    rw [finishEq]
    exact le_add_of_nonneg_right
      (mul_nonneg (sq_nonneg scale) timeLengthNonneg)
  have rightIntegrable :
      IntervalIntegrable
        (fun originalTime =>
          ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
            coefficientMass originalTime)
        volume anchor finish :=
    coefficientIntegrable.const_mul
      (((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹)
  have pointwise : ∀ᵐ originalTime
      ∂volume.restrict (Set.Icc anchor finish),
      fieldMass originalTime ≤
        ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
          coefficientMass originalTime := by
    filter_upwards [reality] with originalTime originalReality
    simpa only [fieldMass, coefficientMass, mul_assoc] using
      scaledFiniteVelocityField_ball_mass_le_cellCover modes negClosed
        (path originalTime) originalReality center centerMem scale spatialRadius
        scalePos scaleLeOne spatialRadiusNonneg coverRadius coverRadiusLarge
  have integrated := intervalIntegral.integral_mono_ae_restrict
    anchorLeFinish fieldIntegrable rightIntegrable pointwise
  rw [intervalIntegral.integral_const_mul] at integrated
  have changeVariables :=
    intervalIntegral.smul_integral_comp_add_mul
      (f := fieldMass) (a := (0 : Real)) (b := timeLength)
      (c := scale ^ 2) anchor
  have changeVariables' :
      scale ^ 2 *
          ∫ scaledTime in 0..timeLength,
            fieldMass (anchor + scale ^ 2 * scaledTime) =
        ∫ originalTime in anchor..finish,
          fieldMass originalTime := by
    rw [finishEq]
    simpa only [smul_eq_mul, mul_zero, add_zero] using changeVariables
  have scaled := mul_le_mul_of_nonneg_left integrated
    (inv_nonneg.mpr (sq_nonneg scale))
  calc
    (∫ scaledTime in 0..timeLength,
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient
              (path (anchor + scale ^ 2 * scaledTime)))
            (center + scale • x)‖ ^ 2) =
        ∫ scaledTime in 0..timeLength,
          fieldMass (anchor + scale ^ 2 * scaledTime) := by rfl
    _ = (scale ^ 2)⁻¹ *
        ∫ originalTime in anchor..finish, fieldMass originalTime := by
      rw [← changeVariables']
      field_simp [scalePos.ne']
    _ ≤ (scale ^ 2)⁻¹ *
        (((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
          ∫ originalTime in anchor..finish,
            coefficientMass originalTime) := scaled
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ ^ 3 *
        ∫ originalTime in anchor..finish,
          finiteStateVorticityCoefficientEnstrophy modes
            (finiteComplexVorticityState modes
              (finiteStateVelocityCoefficient (path originalTime))) := by
      dsimp only [coefficientMass]
      field_simp [scalePos.ne']

private theorem finiteFieldBallMass_intervalIntegrable_of_continuousOn
    (path : Real → ComplexVorticityHilbertState)
    (modes : Finset IntegerWavevector)
    (center : PhysicalSpace)
    (scale spatialRadius start finish : Real)
    (startLeFinish : start ≤ finish)
    (pathContinuous : ContinuousOn path (Icc start finish)) :
    IntervalIntegrable
      (fun time =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          ‖(scale ^ 2 : Real) •
            finiteRealComplexFourierField modes
              (path time)
              (center + scale • x)‖ ^ 2)
      volume start finish := by
  let restrictedPath : Icc start finish → ComplexVorticityHilbertState :=
    fun time => path time.1
  have restrictedPathContinuous : Continuous restrictedPath :=
    continuousOn_iff_continuous_restrict.mp pathContinuous
  let integrand : Icc start finish → PhysicalSpace → Real :=
    fun time x =>
      ‖(scale ^ 2 : Real) •
        finiteRealComplexFourierField modes (restrictedPath time)
          (center + scale • x)‖ ^ 2
  have integrandContinuous : Continuous (Function.uncurry integrand) := by
    dsimp only [integrand]
    unfold finiteRealComplexFourierField
    apply Continuous.pow
    apply Continuous.norm
    have sumContinuous : Continuous
        (fun pair : Icc start finish × PhysicalSpace =>
          ∑ wave ∈ modes,
            realComplexFourierMode wave (restrictedPath pair.1 wave)
              (center + scale • pair.2)) := by
      apply continuous_finsetSum
      intro wave _waveMem
      unfold realComplexFourierMode
      apply Continuous.sub
      · have cosineContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              integerCosine wave (center + scale • pair.2)) :=
          (integerCosine_contDiff wave).continuous.comp
            (continuous_const.add
              ((continuous_const_smul scale).comp continuous_snd))
        have coefficientContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              coefficientReal (restrictedPath pair.1 wave)) :=
          (PiLp.continuous_toLp
              (p := 2) (β := fun _ : Coordinate => ℝ)).comp
            (continuous_pi fun coordinate =>
              Complex.continuous_re.comp
                ((continuous_apply coordinate).comp
                  (((lp.evalCLM ℂ
                    (fun _ : IntegerWavevector => ComplexCoordinateVector)
                    2 wave).continuous.comp restrictedPathContinuous).comp
                      continuous_fst)))
        exact cosineContinuous.smul coefficientContinuous
      · have sineContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              integerSine wave (center + scale • pair.2)) :=
          (integerSine_contDiff wave).continuous.comp
            (continuous_const.add
              ((continuous_const_smul scale).comp continuous_snd))
        have coefficientContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              coefficientImag (restrictedPath pair.1 wave)) :=
          (PiLp.continuous_toLp
              (p := 2) (β := fun _ : Coordinate => ℝ)).comp
            (continuous_pi fun coordinate =>
              Complex.continuous_im.comp
                ((continuous_apply coordinate).comp
                  (((lp.evalCLM ℂ
                    (fun _ : IntegerWavevector => ComplexCoordinateVector)
                    2 wave).continuous.comp restrictedPathContinuous).comp
                      continuous_fst)))
        exact sineContinuous.smul coefficientContinuous
    exact sumContinuous.const_smul (scale ^ 2)
  have restrictedIntegralContinuous : Continuous
      (fun time : Icc start finish =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          integrand time x) :=
    continuous_parametric_integral_of_continuous integrandContinuous
      (isCompact_closedBall _ _)
  have integralContinuousOn : ContinuousOn
      (fun time =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          ‖(scale ^ 2 : Real) •
            finiteRealComplexFourierField modes
              (path time)
              (center + scale • x)‖ ^ 2)
      (Icc start finish) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun time : Icc start finish =>
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖(scale ^ 2 : Real) •
          finiteRealComplexFourierField modes
            (path time.1)
            (center + scale • x)‖ ^ 2)
    simpa only [restrictedPath, integrand] using restrictedIntegralContinuous
  exact integralContinuousOn.intervalIntegrable_of_Icc startLeFinish

private theorem finiteVelocityFieldBallMass_intervalIntegrable_of_continuousOn
    (path : Real → ComplexVorticityHilbertState)
    (modes : Finset IntegerWavevector)
    (center : PhysicalSpace)
    (scale spatialRadius start finish : Real)
    (startLeFinish : start ≤ finish)
    (pathContinuous : ContinuousOn path (Icc start finish)) :
    IntervalIntegrable
      (fun time =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          ‖scale •
            finiteRealComplexFourierField modes
              (finiteStateVelocityCoefficient (path time))
              (center + scale • x)‖ ^ 2)
      volume start finish := by
  let restrictedPath : Icc start finish → ComplexVorticityHilbertState :=
    fun time => path time.1
  have restrictedPathContinuous : Continuous restrictedPath :=
    continuousOn_iff_continuous_restrict.mp pathContinuous
  let integrand : Icc start finish → PhysicalSpace → Real :=
    fun time x =>
      ‖scale •
        finiteRealComplexFourierField modes
          (finiteStateVelocityCoefficient (restrictedPath time))
          (center + scale • x)‖ ^ 2
  have integrandContinuous : Continuous (Function.uncurry integrand) := by
    dsimp only [integrand]
    unfold finiteRealComplexFourierField
    apply Continuous.pow
    apply Continuous.norm
    have sumContinuous : Continuous
        (fun pair : Icc start finish × PhysicalSpace =>
          ∑ wave ∈ modes,
            realComplexFourierMode wave
              (finiteStateVelocityCoefficient
                (restrictedPath pair.1) wave)
              (center + scale • pair.2)) := by
      apply continuous_finsetSum
      intro wave _waveMem
      unfold realComplexFourierMode
      apply Continuous.sub
      · have cosineContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              integerCosine wave (center + scale • pair.2)) :=
          (integerCosine_contDiff wave).continuous.comp
            (continuous_const.add
              ((continuous_const_smul scale).comp continuous_snd))
        have coefficientContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              coefficientReal
                (finiteStateVelocityCoefficient
                  (restrictedPath pair.1) wave)) :=
          (PiLp.continuous_toLp
              (p := 2) (β := fun _ : Coordinate => ℝ)).comp
            (continuous_pi fun coordinate =>
              Complex.continuous_re.comp
                ((continuous_apply coordinate).comp
                  (((finiteStateVelocityCoefficient_contDiff wave).continuous.comp
                    restrictedPathContinuous).comp continuous_fst)))
        exact cosineContinuous.smul coefficientContinuous
      · have sineContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              integerSine wave (center + scale • pair.2)) :=
          (integerSine_contDiff wave).continuous.comp
            (continuous_const.add
              ((continuous_const_smul scale).comp continuous_snd))
        have coefficientContinuous : Continuous
            (fun pair : Icc start finish × PhysicalSpace =>
              coefficientImag
                (finiteStateVelocityCoefficient
                  (restrictedPath pair.1) wave)) :=
          (PiLp.continuous_toLp
              (p := 2) (β := fun _ : Coordinate => ℝ)).comp
            (continuous_pi fun coordinate =>
              Complex.continuous_im.comp
                ((continuous_apply coordinate).comp
                  (((finiteStateVelocityCoefficient_contDiff wave).continuous.comp
                    restrictedPathContinuous).comp continuous_fst)))
        exact sineContinuous.smul coefficientContinuous
    exact sumContinuous.const_smul scale
  have restrictedIntegralContinuous : Continuous
      (fun time : Icc start finish =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          integrand time x) :=
    continuous_parametric_integral_of_continuous integrandContinuous
      (isCompact_closedBall _ _)
  have integralContinuousOn : ContinuousOn
      (fun time =>
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          ‖scale •
            finiteRealComplexFourierField modes
              (finiteStateVelocityCoefficient (path time))
              (center + scale • x)‖ ^ 2)
      (Icc start finish) := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun time : Icc start finish =>
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        ‖scale •
          finiteRealComplexFourierField modes
            (finiteStateVelocityCoefficient (path time.1))
            (center + scale • x)‖ ^ 2)
    simpa only [restrictedPath, integrand] using restrictedIntegralContinuous
  exact integralContinuousOn.intervalIntegrable_of_Icc startLeFinish

private theorem
    finiteVelocityCoefficientMass_intervalIntegrable_of_continuousOn
    (path : Real → ComplexVorticityHilbertState)
    (modes : Finset IntegerWavevector)
    (start finish : Real)
    (startLeFinish : start ≤ finish)
    (pathContinuous : ContinuousOn path (Icc start finish)) :
    IntervalIntegrable
      (fun time =>
        finiteStateVorticityCoefficientEnstrophy modes
          (finiteComplexVorticityState modes
            (finiteStateVelocityCoefficient (path time))))
      volume start finish := by
  have massEq (time : Real) :
      finiteStateVorticityCoefficientEnstrophy modes
          (finiteComplexVorticityState modes
            (finiteStateVelocityCoefficient (path time))) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (finiteStateVelocityCoefficient (path time) wave) := by
    unfold finiteStateVorticityCoefficientEnstrophy
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [finiteComplexVorticityState_apply, if_pos waveMem]
  simp_rw [massEq]
  apply ContinuousOn.intervalIntegrable_of_Icc startLeFinish
  apply continuousOn_finsetSum
  intro wave _waveMem
  exact complexCoordinateAmplitudeSq_continuous.comp_continuousOn
    ((finiteStateVelocityCoefficient_contDiff wave).continuous
      |>.comp_continuousOn pathContinuous)

private theorem finiteCoefficientMass_intervalIntegrable_of_continuousOn
    (path : Real → ComplexVorticityHilbertState)
    (modes : Finset IntegerWavevector)
    (start finish : Real)
    (startLeFinish : start ≤ finish)
    (pathContinuous : ContinuousOn path (Icc start finish)) :
    IntervalIntegrable
      (fun time =>
        finiteStateVorticityCoefficientEnstrophy modes
          (path time))
      volume start finish := by
  apply ContinuousOn.intervalIntegrable_of_Icc startLeFinish
  unfold finiteStateVorticityCoefficientEnstrophy
  apply continuousOn_finsetSum
  intro wave _waveMem
  exact complexCoordinateAmplitudeSq_continuous.comp_continuousOn
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp_continuousOn pathContinuous)

private theorem commonTimeMeasure_eq_comap_volume_for_tail
    (requestedTime : Real) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : Real) requestedTime → Real)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

private theorem receiptPhysicalTrajectory_gradientSummable_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᶠ time : Real in
        MeasureTheory.ae (volume.restrict (Icc 0 requestedTime)),
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq
            (wholeRestartReceiptPhysicalTrajectory receipt time wave) := by
  rw [ae_restrict_iff_subtype measurableSet_Icc]
  rw [← commonTimeMeasure_eq_comap_volume_for_tail]
  filter_upwards [
    receiptPointwiseGradient_ae_summable receipt,
    receiptStateLimit_eq_wholePath_ae receipt] with time gradientSummable pathEq
  unfold wholeRestartReceiptPhysicalTrajectory
  rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  simpa only [← pathEq] using gradientSummable

theorem wholeRestartPrefixPhysicalTrajectory_gradientSummable_ae
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ length : Nat,
      ∀ᶠ time : Real in
          MeasureTheory.ae
            (volume.restrict (Icc 0 (elapsedTime initial length))),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (wholeRestartPrefixPhysicalTrajectory initial length time wave)
  | 0 => by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [volume.ae_ne (0 : Real)] with time timeNe
      intro timeMem
      have timeEq : time = 0 := by simpa using timeMem
      exact (timeNe timeEq).elim
  | length + 1 => by
      let joinTime := elapsedTime initial length
      let localDuration := (run initial length).contact.time.1
      let receipt := (run initial length).contact.prefixReceipt
      have priorAE :=
        wholeRestartPrefixPhysicalTrajectory_gradientSummable_ae
          initial length
      have localAE :=
        receiptPhysicalTrajectory_gradientSummable_ae receipt
      have priorGlobal :
          ∀ᶠ time : Real in MeasureTheory.ae volume,
            time ∈ Icc 0 joinTime →
              Summable fun wave : IntegerWavevector =>
                integerWaveNormSq wave *
                  complexCoordinateAmplitudeSq
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time wave) := by
        simpa only [joinTime] using
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).1 priorAE
      have localGlobal :
          ∀ᶠ localTime : Real in MeasureTheory.ae volume,
            localTime ∈ Icc 0 localDuration →
              Summable fun wave : IntegerWavevector =>
                integerWaveNormSq wave *
                  complexCoordinateAmplitudeSq
                    (wholeRestartReceiptPhysicalTrajectory receipt
                      localTime wave) := by
        simpa only [localDuration, receipt] using
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).1 localAE
      have shiftedLocal :
          ∀ᶠ time : Real in MeasureTheory.ae volume,
            time - joinTime ∈ Icc 0 localDuration →
              Summable fun wave : IntegerWavevector =>
                integerWaveNormSq wave *
                  complexCoordinateAmplitudeSq
                    (wholeRestartReceiptPhysicalTrajectory receipt
                      (time - joinTime) wave) := by
        have shifted :=
          ((measurePreserving_add_left volume (-joinTime))
            |>.quasiMeasurePreserving.tendsto_ae) localGlobal
        rw [Filter.mem_map] at shifted
        filter_upwards [shifted] with time timeGood
        change
          -joinTime + time ∈ Icc 0 localDuration →
            Summable fun wave : IntegerWavevector =>
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq
                  (wholeRestartReceiptPhysicalTrajectory receipt
                    (-joinTime + time) wave)
          at timeGood
        simpa only [neg_add_eq_sub] using timeGood
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [priorGlobal, shiftedLocal] with time priorGood localGood
      intro timeMem
      by_cases timeLeJoin : time ≤ joinTime
      · rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_le _ _ _ _ timeLeJoin]
        exact priorGood ⟨timeMem.1, timeLeJoin⟩
      · have joinLtTime : joinTime < time := lt_of_not_ge timeLeJoin
        have localMem : time - joinTime ∈ Icc 0 localDuration := by
          constructor
          · exact sub_nonneg.mpr joinLtTime.le
          · dsimp only [joinTime, localDuration] at timeMem ⊢
            rw [elapsedTime_succ] at timeMem
            linarith [timeMem.2]
        rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_lt _ _ _ _ joinLtTime]
        exact localGood localMem

private theorem receiptPhysicalTrajectory_fourierReality_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᶠ time : Real in
        MeasureTheory.ae (volume.restrict (Icc 0 requestedTime)),
      FiniteStateFourierReality
        (wholeRestartReceiptPhysicalTrajectory receipt time) := by
  rw [ae_restrict_iff_subtype measurableSet_Icc]
  rw [← commonTimeMeasure_eq_comap_volume_for_tail]
  filter_upwards [wholePath_fourierReality_ae receipt] with time reality
  unfold wholeRestartReceiptPhysicalTrajectory
  rw [projIcc_of_mem receipt.requestedTimePos.le time.2]
  exact reality

theorem wholeRestartPrefixPhysicalTrajectory_fourierReality_ae
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ length : Nat,
      ∀ᶠ time : Real in
          MeasureTheory.ae
            (volume.restrict (Icc 0 (elapsedTime initial length))),
        FiniteStateFourierReality
          (wholeRestartPrefixPhysicalTrajectory initial length time)
  | 0 => by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [volume.ae_ne (0 : Real)] with time timeNe
      intro timeMem
      have timeEq : time = 0 := by simpa using timeMem
      exact (timeNe timeEq).elim
  | length + 1 => by
      let joinTime := elapsedTime initial length
      let localDuration := (run initial length).contact.time.1
      let receipt := (run initial length).contact.prefixReceipt
      have priorAE :=
        wholeRestartPrefixPhysicalTrajectory_fourierReality_ae initial length
      have localAE := receiptPhysicalTrajectory_fourierReality_ae receipt
      have priorGlobal :
          ∀ᶠ time : Real in MeasureTheory.ae volume,
            time ∈ Icc 0 joinTime →
              FiniteStateFourierReality
                (wholeRestartPrefixPhysicalTrajectory initial length time) := by
        simpa only [joinTime] using
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).1 priorAE
      have localGlobal :
          ∀ᶠ localTime : Real in MeasureTheory.ae volume,
            localTime ∈ Icc 0 localDuration →
              FiniteStateFourierReality
                (wholeRestartReceiptPhysicalTrajectory receipt localTime) := by
        simpa only [localDuration, receipt] using
          (MeasureTheory.ae_restrict_iff' measurableSet_Icc).1 localAE
      have shiftedLocal :
          ∀ᶠ time : Real in MeasureTheory.ae volume,
            time - joinTime ∈ Icc 0 localDuration →
              FiniteStateFourierReality
                (wholeRestartReceiptPhysicalTrajectory receipt
                  (time - joinTime)) := by
        have shifted :=
          ((measurePreserving_add_left volume (-joinTime))
            |>.quasiMeasurePreserving.tendsto_ae) localGlobal
        rw [Filter.mem_map] at shifted
        filter_upwards [shifted] with time timeGood
        change
          -joinTime + time ∈ Icc 0 localDuration →
            FiniteStateFourierReality
              (wholeRestartReceiptPhysicalTrajectory receipt
                (-joinTime + time)) at timeGood
        simpa only [neg_add_eq_sub] using timeGood
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      filter_upwards [priorGlobal, shiftedLocal] with time priorGood localGood
      intro timeMem
      by_cases timeLeJoin : time ≤ joinTime
      · rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_le _ _ _ _ timeLeJoin]
        exact priorGood ⟨timeMem.1, timeLeJoin⟩
      · have joinLtTime : joinTime < time := lt_of_not_ge timeLeJoin
        have localMem : time - joinTime ∈ Icc 0 localDuration := by
          constructor
          · exact sub_nonneg.mpr joinLtTime.le
          · dsimp only [joinTime, localDuration] at timeMem ⊢
            rw [elapsedTime_succ] at timeMem
            linarith [timeMem.2]
        rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_lt _ _ _ _ joinLtTime]
        exact localGood localMem

private theorem complexSharpSupportProjection_continuous_local
    (modes : Finset IntegerWavevector) :
    Continuous (complexSharpSupportProjection modes) := by
  have contractive :
      LipschitzWith 1 (complexSharpSupportProjection modes) := by
    apply LipschitzWith.of_dist_le_mul
    intro left right
    simpa using complexSharpSupportProjection_dist_le modes left right
  exact contractive.continuous

private theorem wholeRestartPrefix_cubeComplementMass_intervalIntegrable
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length radius : Nat)
    (start finish : Real)
    (startNonneg : 0 ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ elapsedTime initial length) :
    IntervalIntegrable
      (fun time =>
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
              (integerWaveFrequencyCube radius)
              (wholeRestartPrefixPhysicalTrajectory initial length time) -
            wholeRestartPrefixPhysicalTrajectory initial length time))
      volume start finish := by
  have pathContinuous :
      ContinuousOn
        (wholeRestartPrefixPhysicalTrajectory initial length)
        (Icc start finish) :=
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial length).mono
      (Icc_subset_Icc startNonneg finishLe)
  have projectedContinuous :
      ContinuousOn
        (fun time =>
          complexSharpSupportProjection
            (integerWaveFrequencyCube radius)
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        (Icc start finish) :=
    (complexSharpSupportProjection_continuous_local
      (integerWaveFrequencyCube radius)).comp_continuousOn pathContinuous
  have differenceContinuous :
      ContinuousOn
        (fun time =>
          complexSharpSupportProjection
              (integerWaveFrequencyCube radius)
              (wholeRestartPrefixPhysicalTrajectory initial length time) -
            wholeRestartPrefixPhysicalTrajectory initial length time)
        (Icc start finish) :=
    projectedContinuous.sub pathContinuous
  exact ContinuousOn.intervalIntegrable_of_Icc startLeFinish
    (continuous_wholeVorticityEuclideanMass.comp_continuousOn
      differenceContinuous)

private theorem scaled_cubeComplement_spacetimeTail_le_gradient
    (path : Real → ComplexVorticityHilbertState)
    (start finish scale physicalBand : Real)
    (startLeFinish : start ≤ finish)
    (scalePos : 0 < scale)
    (physicalBandPos : 0 < physicalBand)
    (gradientIntegrable :
      IntervalIntegrable
        (fun time => wholeStateVorticityGradientMass (path time))
        volume start finish)
    (tailIntegrable :
      IntervalIntegrable
        (fun time =>
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube
                  (Nat.ceil (physicalBand / scale)))
                (path time) -
              path time))
        volume start finish)
    (gradientSummableAE :
      ∀ᶠ time : Real in
          MeasureTheory.ae
            (MeasureTheory.volume.restrict (Icc start finish)),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (path time wave)) :
    scale⁻¹ *
        (∫ time in start..finish,
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube
                  (Nat.ceil (physicalBand / scale)))
                (path time) -
              path time)) ≤
      (scale *
        ∫ time in start..finish,
          wholeStateVorticityGradientMass (path time)) /
        physicalBand ^ 2 := by
  let radius : Nat := Nat.ceil (physicalBand / scale)
  have ratioPos : 0 < physicalBand / scale :=
    div_pos physicalBandPos scalePos
  have radiusPos : 0 < radius := by
    dsimp only [radius]
    exact Nat.ceil_pos.mpr ratioPos
  have ratioLeRadius : physicalBand / scale ≤ (radius : Real) := by
    dsimp only [radius]
    exact Nat.le_ceil _
  have physicalBandLe : physicalBand ≤ scale * (radius : Real) := by
    simpa only [mul_comm] using (div_le_iff₀ scalePos).mp ratioLeRadius
  have physicalBandSqLe :
      physicalBand ^ 2 ≤ scale ^ 2 * (radius : Real) ^ 2 := by
    calc
      physicalBand ^ 2 ≤ (scale * (radius : Real)) ^ 2 :=
        (sq_le_sq₀ physicalBandPos.le
          (mul_nonneg scalePos.le (Nat.cast_nonneg radius))).2
          physicalBandLe
      _ = scale ^ 2 * (radius : Real) ^ 2 := by ring
  have pointwise :
      ∀ᶠ time : Real in
          MeasureTheory.ae
            (MeasureTheory.volume.restrict (Icc start finish)),
        wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube radius) (path time) -
              path time) ≤
          (scale ^ 2 / physicalBand ^ 2) *
            wholeStateVorticityGradientMass (path time) := by
    filter_upwards [gradientSummableAE] with time gradientSummable
    let tailMass :=
      wholeVorticityEuclideanMass
        (complexSharpSupportProjection
            (integerWaveFrequencyCube radius) (path time) - path time)
    let gradientMass := wholeStateVorticityGradientMass (path time)
    have tailNonneg : 0 ≤ tailMass := by
      dsimp only [tailMass]
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun _ => sq_nonneg _
    have core :
        (radius : Real) ^ 2 * tailMass ≤ gradientMass := by
      dsimp only [tailMass, gradientMass]
      exact wholeVorticity_cubeComplement_mul_radius_sq_le_gradient
        (path time) gradientSummable radius
    have paid : physicalBand ^ 2 * tailMass ≤ scale ^ 2 * gradientMass := by
      calc
        physicalBand ^ 2 * tailMass ≤
            (scale ^ 2 * (radius : Real) ^ 2) * tailMass :=
          mul_le_mul_of_nonneg_right physicalBandSqLe tailNonneg
        _ = scale ^ 2 * ((radius : Real) ^ 2 * tailMass) := by ring
        _ ≤ scale ^ 2 * gradientMass :=
          mul_le_mul_of_nonneg_left core (sq_nonneg scale)
    have bandSqPos : 0 < physicalBand ^ 2 := sq_pos_of_pos physicalBandPos
    calc
      tailMass ≤ (scale ^ 2 * gradientMass) / physicalBand ^ 2 :=
        (le_div_iff₀ bandSqPos).2 (by
          simpa only [mul_comm] using paid)
      _ = (scale ^ 2 / physicalBand ^ 2) * gradientMass := by
        field_simp [physicalBandPos.ne']
  have majorantIntegrable :
      IntervalIntegrable
        (fun time =>
          (scale ^ 2 / physicalBand ^ 2) *
            wholeStateVorticityGradientMass (path time))
        volume start finish :=
    gradientIntegrable.const_mul _
  have integrated :
      (∫ time in start..finish,
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube radius) (path time) -
              path time)) ≤
        (scale ^ 2 / physicalBand ^ 2) *
          ∫ time in start..finish,
            wholeStateVorticityGradientMass (path time) := by
    calc
      (∫ time in start..finish,
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube radius) (path time) -
              path time)) ≤
          ∫ time in start..finish,
            (scale ^ 2 / physicalBand ^ 2) *
              wholeStateVorticityGradientMass (path time) :=
        intervalIntegral.integral_mono_ae_restrict startLeFinish tailIntegrable
          majorantIntegrable pointwise
      _ = (scale ^ 2 / physicalBand ^ 2) *
          ∫ time in start..finish,
            wholeStateVorticityGradientMass (path time) := by
        rw [intervalIntegral.integral_const_mul]
  have scaled := mul_le_mul_of_nonneg_left integrated
    (inv_nonneg.mpr scalePos.le)
  simpa only [radius] using (show
    scale⁻¹ *
          (∫ time in start..finish,
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                  (integerWaveFrequencyCube radius) (path time) -
                path time)) ≤
        (scale *
          ∫ time in start..finish,
            wholeStateVorticityGradientMass (path time)) /
          physicalBand ^ 2 by
    calc
      scale⁻¹ *
            (∫ time in start..finish,
              wholeVorticityEuclideanMass
                (complexSharpSupportProjection
                    (integerWaveFrequencyCube radius) (path time) -
                  path time)) ≤
          scale⁻¹ *
            ((scale ^ 2 / physicalBand ^ 2) *
              ∫ time in start..finish,
                wholeStateVorticityGradientMass (path time)) := scaled
      _ = (scale *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass (path time)) /
          physicalBand ^ 2 := by
        field_simp [scalePos.ne', physicalBandPos.ne'])

private theorem
    wholeRestartPrefix_scaledCubeComplement_spacetimeTail_le_gradientCeiling
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (start finish level physicalBand gradientCeiling : Real)
    (startNonneg : 0 ≤ start)
    (startLeFinish : start ≤ finish)
    (finishLe : finish ≤ elapsedTime initial length)
    (levelPos : 0 < level)
    (physicalBandPos : 0 < physicalBand)
    (gradientIntegrable :
      IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume start finish)
    (gradientPayment :
      level⁻¹ *
          (∫ time in start..finish,
            wholeStateVorticityGradientMass
              (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        gradientCeiling) :
    level *
        (∫ time in start..finish,
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube
                  (Nat.ceil (physicalBand / level⁻¹)))
                (wholeRestartPrefixPhysicalTrajectory initial length time) -
              wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
      gradientCeiling / physicalBand ^ 2 := by
  have tailIntegrable :=
    wholeRestartPrefix_cubeComplementMass_intervalIntegrable
      initial length (Nat.ceil (physicalBand / level⁻¹)) start finish
      startNonneg startLeFinish finishLe
  have prefixGradientAE :=
    wholeRestartPrefixPhysicalTrajectory_gradientSummable_ae initial length
  have windowSubset :
      Icc start finish ⊆ Icc 0 (elapsedTime initial length) :=
    Icc_subset_Icc startNonneg finishLe
  have windowGradientAE :
      ∀ᶠ time : Real in
          MeasureTheory.ae (volume.restrict (Icc start finish)),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              (wholeRestartPrefixPhysicalTrajectory initial length
                time wave) :=
    ae_mono (Measure.restrict_mono windowSubset le_rfl) prefixGradientAE
  have raw :=
    scaled_cubeComplement_spacetimeTail_le_gradient
      (wholeRestartPrefixPhysicalTrajectory initial length)
      start finish level⁻¹ physicalBand startLeFinish
      (inv_pos.mpr levelPos) physicalBandPos gradientIntegrable
      tailIntegrable windowGradientAE
  have paid :
      (level⁻¹ *
          ∫ time in start..finish,
            wholeStateVorticityGradientMass
              (wholeRestartPrefixPhysicalTrajectory initial length time)) /
            physicalBand ^ 2 ≤
        gradientCeiling / physicalBand ^ 2 :=
    div_le_div_of_nonneg_right gradientPayment (sq_nonneg physicalBand)
  simpa only [inv_inv] using raw.trans paid

private theorem finiteStretching_generates_scaled_closedBall_mass
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (stretchingFloor massCeiling lipschitzCeiling scale : Real)
    (stretchingFloorPos : 0 < stretchingFloor)
    (massCeilingPos : 0 < massCeiling)
    (lipschitzCeilingPos : 0 < lipschitzCeiling)
    (scalePos : 0 < scale)
    (stretchingLower : stretchingFloor ≤
      |finiteStateVorticityStretchingWork modes state|)
    (massUpper :
      finiteStateVorticityCoefficientEnstrophy modes state ≤ massCeiling)
    (lipschitzUpper :
      Real.sqrt
        ((modes.card : ℝ) * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state) ≤
        lipschitzCeiling) :
    ∃ center ∈ physicalUnitCell,
      scale *
          (((stretchingFloor / massCeiling) / 2) ^ 2 *
            (volume (Metric.closedBall center
              ((stretchingFloor / massCeiling) /
                (2 * lipschitzCeiling)))).toReal) ≤
        ∫ x in Metric.closedBall (0 : PhysicalSpace)
            (((stretchingFloor / massCeiling) /
              (2 * lipschitzCeiling)) / scale),
          ‖(scale ^ 2 : Real) •
            finiteRealComplexFourierField modes state
              (center + scale • x)‖ ^ 2 := by
  obtain ⟨center, centerMem, originalLower⟩ :=
    finiteStretching_generates_closedBall_mass
      modes zeroNotMem negClosed state supported transverse reality
      stretchingFloor massCeiling lipschitzCeiling
      stretchingFloorPos massCeilingPos lipschitzCeilingPos
      stretchingLower massUpper lipschitzUpper
  refine ⟨center, centerMem, ?_⟩
  let originalRadius :=
    (stretchingFloor / massCeiling) / (2 * lipschitzCeiling)
  let scaledRadius := originalRadius / scale
  have originalRadiusPos : 0 < originalRadius := by
    dsimp only [originalRadius]
    positivity
  have scaledRadiusPos : 0 < scaledRadius := by
    dsimp only [scaledRadius]
    positivity
  have radiusEq : scale * scaledRadius = originalRadius := by
    dsimp only [scaledRadius]
    field_simp [scalePos.ne']
  have scaledEq :=
    parabolicScaledField_closedBall_mass_eq
      (finiteRealComplexFourierField modes state) center scale scaledRadius
      scalePos scaledRadiusPos.le
  rw [radiusEq] at scaledEq
  change scale *
      (((stretchingFloor / massCeiling) / 2) ^ 2 *
        (volume (Metric.closedBall center originalRadius)).toReal) ≤
    ∫ x in Metric.closedBall (0 : PhysicalSpace) scaledRadius,
      ‖(scale ^ 2 : Real) • finiteRealComplexFourierField modes state
        (center + scale • x)‖ ^ 2
  rw [scaledEq]
  exact mul_le_mul_of_nonneg_left originalLower scalePos.le

private theorem scaleCritical_closedBall_lower_constant
    (center : PhysicalSpace)
    (stretchingConstant lipschitzConstant level : Real)
    (stretchingConstantPos : 0 < stretchingConstant)
    (lipschitzConstantPos : 0 < lipschitzConstant)
    (levelPos : 0 < level) :
    level⁻¹ *
        ((((stretchingConstant * level ^ 3) / level) / 2) ^ 2 *
          (volume (Metric.closedBall center
            (((stretchingConstant * level ^ 3) / level) /
              (2 * (lipschitzConstant * level ^ 3))))).toReal) =
      stretchingConstant ^ 5 * (Real.pi * 4 / 3) /
        (32 * lipschitzConstant ^ 3) := by
  have radiusPos :
      0 < ((stretchingConstant * level ^ 3) / level) /
        (2 * (lipschitzConstant * level ^ 3)) := by positivity
  rw [EuclideanSpace.volume_closedBall_fin_three]
  rw [ENNReal.toReal_mul]
  rw [ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal radiusPos.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  field_simp [levelPos.ne', lipschitzConstantPos.ne']
  ring

private theorem wholeRestartModes_card_cast_le_radius_cube
    (radius : Nat) :
    ((wholeRestartModes radius).card : Real) ≤
      (2 * (radius : Real) + 1) ^ 3 := by
  have cardLe :
      (wholeRestartModes radius).card ≤
        (integerWaveFrequencyCube radius).card := by
    apply Finset.card_le_card
    intro wave waveMem
    rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
      Finset.mem_erase] at waveMem
    exact waveMem.2
  have cubeCard :
      (integerWaveFrequencyCube radius).card = (2 * radius + 1) ^ 3 := by
    (simp [integerWaveFrequencyCube, Fintype.card_piFinset, Int.card_Icc];
      omega)
  rw [cubeCard] at cardLe
  exact_mod_cast cardLe

private theorem wholeRestartModes_card_cast_le_scaled_cube
    (radius : Nat)
    (level radiusConstant : Real)
    (levelOne : 1 ≤ level)
    (radiusConstantNonneg : 0 ≤ radiusConstant)
    (radiusLe : (radius : Real) ≤ radiusConstant * level) :
    ((wholeRestartModes radius).card : Real) ≤
      (2 * radiusConstant + 1) ^ 3 * level ^ 3 := by
  calc
    ((wholeRestartModes radius).card : Real) ≤
        (2 * (radius : Real) + 1) ^ 3 :=
      wholeRestartModes_card_cast_le_radius_cube radius
    _ ≤ ((2 * radiusConstant + 1) * level) ^ 3 := by
      gcongr
      have radiusConstantLevelNonneg : 0 ≤ radiusConstant * level :=
        mul_nonneg radiusConstantNonneg (by linarith)
      nlinarith
    _ = (2 * radiusConstant + 1) ^ 3 * level ^ 3 := by ring

private theorem complexCoordinateAmplitudeSq_single
    (testCoordinate : Coordinate) (a : ℂ) :
    complexCoordinateAmplitudeSq (Pi.single testCoordinate a) =
      Complex.normSq a := by
  unfold complexCoordinateAmplitudeSq
  rw [Finset.sum_eq_single testCoordinate]
  · simp
  · intro coordinate _ coordinateNe
    simp [coordinateNe]
  · simp

private theorem recenteredCoefficient_norm_le_scaleCube
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale : ℝ)
    (scalePos : 0 < scale)
    (center : PhysicalSpace)
    (wave : IntegerWavevector)
    (sampleNormLe : ∀ coordinate frequency,
      ‖frequencyTest coordinate frequency‖ ≤ 1) :
    ‖recenteredTensorSchwartzFourierCoefficient
        (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
        scale scalePos.ne' center wave‖ ≤ scale ^ 3 := by
  rw [recenteredInverseFourierTensorSchwartzCoefficient_eq_scaleCube_samples_phase
    frequencyTest scale scalePos center wave]
  rw [norm_mul, norm_mul, Complex.norm_exp]
  have phaseRe :
      (-Complex.I * (integerWavePhase wave center : ℂ)).re = 0 := by
    simp
  rw [phaseRe, Real.exp_zero, mul_one]
  rw [show ‖(((scale ^ 3 : ℝ) : ℂ))‖ = scale ^ 3 by
    simp [abs_of_pos scalePos]]
  have h0 := sampleNormLe (0 : Coordinate) (scale * (wave 0 : ℝ))
  have h1 := sampleNormLe (1 : Coordinate) (scale * (wave 1 : ℝ))
  have h2 := sampleNormLe (2 : Coordinate) (scale * (wave 2 : ℝ))
  rw [Fin.prod_univ_three, norm_mul, norm_mul]
  have n0 : 0 ≤ ‖frequencyTest 0 (scale * (wave 0 : ℝ))‖ := norm_nonneg _
  have n1 : 0 ≤ ‖frequencyTest 1 (scale * (wave 1 : ℝ))‖ := norm_nonneg _
  have n2 : 0 ≤ ‖frequencyTest 2 (scale * (wave 2 : ℝ))‖ := norm_nonneg _
  have h01 :
      ‖frequencyTest 0 (scale * (wave 0 : ℝ))‖ *
          ‖frequencyTest 1 (scale * (wave 1 : ℝ))‖ ≤ 1 :=
    mul_le_one₀ h0 n1 h1
  have h012 :
      (‖frequencyTest 0 (scale * (wave 0 : ℝ))‖ *
          ‖frequencyTest 1 (scale * (wave 1 : ℝ))‖) *
          ‖frequencyTest 2 (scale * (wave 2 : ℝ))‖ ≤ 1 :=
    mul_le_one₀ h01 n2 h2
  simpa using mul_le_mul_of_nonneg_left h012 (pow_nonneg scalePos.le 3)

private theorem integerWaveNormSq_le_three_mul_radius_sq_of_cubeMem
    (radius : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube radius) :
    integerWaveNormSq wave ≤ 3 * (radius : Real) ^ 2 := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem
  have h0 := waveMem (0 : Fin 3)
  have h1 := waveMem (1 : Fin 3)
  have h2 := waveMem (2 : Fin 3)
  rw [Finset.mem_Icc] at h0 h1 h2
  have h0r :
      -((radius : Nat) : Real) ≤ (wave (0 : Fin 3) : Real) ∧
        (wave (0 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h0
  have h1r :
      -((radius : Nat) : Real) ≤ (wave (1 : Fin 3) : Real) ∧
        (wave (1 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h1
  have h2r :
      -((radius : Nat) : Real) ≤ (wave (2 : Fin 3) : Real) ∧
        (wave (2 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h2
  have h0sq : (wave (0 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h1sq : (wave (1 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h2sq : (wave (2 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  unfold integerWaveNormSq
  rw [Fin.sum_univ_three]
  nlinarith

private theorem integerWaveFrequencyCube_scaled_card_le
    (scale bandRadius : Real)
    (radius : Nat)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (_bandRadiusNonneg : 0 ≤ bandRadius)
    (radiusLe : scale * (radius : Real) ≤ bandRadius) :
    scale ^ 3 * ((integerWaveFrequencyCube radius).card : Real) ≤
      (2 * bandRadius + 1) ^ 3 := by
  have cubeCard :
      (integerWaveFrequencyCube radius).card = (2 * radius + 1) ^ 3 := by
    (simp [integerWaveFrequencyCube, Fintype.card_piFinset, Int.card_Icc];
      omega)
  rw [cubeCard]
  push_cast
  calc
    scale ^ 3 * (2 * (radius : Real) + 1) ^ 3 =
        (scale * (2 * (radius : Real) + 1)) ^ 3 := by ring
    _ ≤ (2 * bandRadius + 1) ^ 3 := by
      gcongr
      nlinarith

private theorem recenteredTensorSchwartz_testEnergy_le_scale
    (frequencyTest : Coordinate → SchwartzMap ℝ ℂ)
    (scale bandRadius : Real)
    (radius : Nat)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (center : PhysicalSpace)
    (testCoordinate : Coordinate)
    (sampleNormLe : ∀ coordinate frequency,
      ‖frequencyTest coordinate frequency‖ ≤ 1) :
    (∑ wave ∈ puncturedIntegerWaveFrequencyCube radius,
      3 * integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq
          (Pi.single testCoordinate
            (recenteredTensorSchwartzFourierCoefficient
              (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
              scale scalePos.ne' center wave))) ≤
      scale *
        (9 * (2 * Real.pi) ^ 2 * bandRadius ^ 2 *
          (2 * bandRadius + 1) ^ 3) := by
  let cube := integerWaveFrequencyCube radius
  let modes := puncturedIntegerWaveFrequencyCube radius
  let ceiling : Real :=
    9 * (2 * Real.pi) ^ 2 * (radius : Real) ^ 2 * scale ^ 6
  have modesSubset : modes ⊆ cube := by
    intro wave waveMem
    exact (Finset.mem_erase.mp waveMem).2
  have ceilingNonneg : 0 ≤ ceiling := by
    dsimp only [ceiling]
    positivity
  have pointwise (wave : IntegerWavevector) (waveMem : wave ∈ modes) :
      3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq
            (Pi.single testCoordinate
              (recenteredTensorSchwartzFourierCoefficient
                (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
                scale scalePos.ne' center wave)) ≤ ceiling := by
    let coefficient :=
      recenteredTensorSchwartzFourierCoefficient
        (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
        scale scalePos.ne' center wave
    have coefficientNormLe : ‖coefficient‖ ≤ scale ^ 3 :=
      recenteredCoefficient_norm_le_scaleCube
        frequencyTest scale scalePos center wave sampleNormLe
    have coefficientNormSqLe : Complex.normSq coefficient ≤ scale ^ 6 := by
      rw [← Complex.sq_norm]
      calc
        ‖coefficient‖ ^ 2 ≤ (scale ^ 3) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg coefficient)
            (pow_nonneg scalePos.le 3)).2 coefficientNormLe
        _ = scale ^ 6 := by ring
    have waveNormLe :
        integerWaveNormSq wave ≤ 3 * (radius : Real) ^ 2 :=
      integerWaveNormSq_le_three_mul_radius_sq_of_cubeMem
        radius wave (modesSubset waveMem)
    have multiplierNonneg : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    have normSqNonneg : 0 ≤ Complex.normSq coefficient :=
      Complex.normSq_nonneg coefficient
    rw [complexCoordinateAmplitudeSq_single]
    unfold integerWaveViscousMultiplier
    dsimp only [ceiling, coefficient]
    calc
      3 * ((2 * Real.pi) ^ 2 * integerWaveNormSq wave) *
            Complex.normSq coefficient ≤
          3 * ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) *
            Complex.normSq coefficient := by
        gcongr
      _ ≤ 3 * ((2 * Real.pi) ^ 2 * (3 * (radius : Real) ^ 2)) *
            scale ^ 6 := by
        exact mul_le_mul_of_nonneg_left coefficientNormSqLe
          (mul_nonneg (by norm_num)
            (mul_nonneg multiplierNonneg
              (mul_nonneg (by norm_num) (sq_nonneg _))))
      _ = 9 * (2 * Real.pi) ^ 2 * (radius : Real) ^ 2 * scale ^ 6 := by
        ring
  have sumLe :
      (∑ wave ∈ modes,
        3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq
            (Pi.single testCoordinate
              (recenteredTensorSchwartzFourierCoefficient
                (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
                scale scalePos.ne' center wave))) ≤
        (modes.card : Real) * ceiling := by
    calc
      _ ≤ ∑ _wave ∈ modes, ceiling := by
        exact Finset.sum_le_sum fun wave waveMem => pointwise wave waveMem
      _ = (modes.card : Real) * ceiling := by simp
  have cardLe : (modes.card : Real) ≤ (cube.card : Real) := by
    exact_mod_cast Finset.card_le_card modesSubset
  have sumCubeLe :
      (∑ wave ∈ modes,
        3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq
            (Pi.single testCoordinate
              (recenteredTensorSchwartzFourierCoefficient
                (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
                scale scalePos.ne' center wave))) ≤
        (cube.card : Real) * ceiling :=
    sumLe.trans (mul_le_mul_of_nonneg_right cardLe ceilingNonneg)
  have scaledCard :
      scale ^ 3 * (cube.card : Real) ≤ (2 * bandRadius + 1) ^ 3 := by
    exact integerWaveFrequencyCube_scaled_card_le
      scale bandRadius radius scalePos scaleLeOne bandRadiusNonneg radiusLe
  have scaledRadiusSq :
      scale ^ 2 * (radius : Real) ^ 2 ≤ bandRadius ^ 2 := by
    nlinarith [sq_le_sq₀
      (mul_nonneg scalePos.le (Nat.cast_nonneg radius))
      bandRadiusNonneg |>.2 radiusLe]
  have scaledProduct :
      (scale ^ 2 * (radius : Real) ^ 2) *
          (scale ^ 3 * (cube.card : Real)) ≤
        bandRadius ^ 2 * (2 * bandRadius + 1) ^ 3 := by
    calc
      _ ≤ bandRadius ^ 2 * (scale ^ 3 * (cube.card : Real)) :=
        mul_le_mul_of_nonneg_right scaledRadiusSq
          (mul_nonneg (pow_nonneg scalePos.le 3)
            (Nat.cast_nonneg cube.card))
      _ ≤ _ := mul_le_mul_of_nonneg_left scaledCard (sq_nonneg _)
  calc
    _ ≤ (cube.card : Real) * ceiling := sumCubeLe
    _ = scale * (9 * (2 * Real.pi) ^ 2) *
        ((scale ^ 2 * (radius : Real) ^ 2) *
          (scale ^ 3 * (cube.card : Real))) := by
      dsimp only [ceiling]
      ring
    _ ≤ scale * (9 * (2 * Real.pi) ^ 2) *
        (bandRadius ^ 2 * (2 * bandRadius + 1) ^ 3) := by
      exact mul_le_mul_of_nonneg_left scaledProduct
        (mul_nonneg scalePos.le
          (mul_nonneg (by norm_num) (sq_nonneg _)))
    _ = _ := by ring

private theorem integral_pairing_sq_le_measure_mul_energy_mul_difference
    {μ : Measure Real}
    [IsFiniteMeasure μ]
    (pairing difference : Real → Real)
    (testEnergy : Real)
    (pairingMeasurable : AEStronglyMeasurable pairing μ)
    (differenceIntegrable : Integrable difference μ)
    (differenceNonneg : ∀ᵐ time ∂μ, 0 ≤ difference time)
    (pointwise : ∀ᵐ time ∂μ,
      pairing time ^ 2 ≤ testEnergy * difference time) :
    (∫ time, pairing time ∂μ) ^ 2 ≤
      μ.real Set.univ * testEnergy * ∫ time, difference time ∂μ := by
  have majorantIntegrable :
      Integrable (fun time => testEnergy * difference time) μ :=
    differenceIntegrable.const_mul testEnergy
  have pairingNormSqMeasurable :
      AEStronglyMeasurable (fun time => ‖pairing time‖ ^ 2) μ :=
    pairingMeasurable.norm.pow 2
  have pairingNormSqIntegrable :
      Integrable (fun time => ‖pairing time‖ ^ 2) μ := by
    apply majorantIntegrable.mono' pairingNormSqMeasurable
    filter_upwards [differenceNonneg, pointwise] with time differenceTimeNonneg pairingSqLe
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using pairingSqLe
  have pairingSqIntegrable :
      Integrable (fun time => pairing time ^ 2) μ := by
    convert pairingNormSqIntegrable using 1
    funext time
    rw [Real.norm_eq_abs, sq_abs]
  have pairingMemLp : MemLp pairing 2 μ :=
    (memLp_two_iff_integrable_sq pairingMeasurable).mpr pairingSqIntegrable
  have cauchy :=
    ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation.norm_integral_sq_le_measureReal_mul_integral_norm_sq
      pairing pairingMemLp
  have integralLe :
      (∫ time, ‖pairing time‖ ^ 2 ∂μ) ≤
        testEnergy * ∫ time, difference time ∂μ := by
    calc
      (∫ time, ‖pairing time‖ ^ 2 ∂μ) ≤
          ∫ time, testEnergy * difference time ∂μ :=
        integral_mono_ae pairingNormSqIntegrable majorantIntegrable (by
          filter_upwards [pointwise] with time pairingSqLe
          simpa only [Real.norm_eq_abs, sq_abs] using pairingSqLe)
      _ = testEnergy * ∫ time, difference time ∂μ := by
        rw [integral_const_mul]
  have measureNonneg : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  calc
    (∫ time, pairing time ∂μ) ^ 2 =
        ‖∫ time, pairing time ∂μ‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    _ ≤ μ.real Set.univ * ∫ time, ‖pairing time‖ ^ 2 ∂μ := cauchy
    _ ≤ μ.real Set.univ *
        (testEnergy * ∫ time, difference time ∂μ) :=
      mul_le_mul_of_nonneg_left integralLe measureNonneg
    _ = μ.real Set.univ * testEnergy *
        ∫ time, difference time ∂μ := by ring

private theorem complexCoordinateRealInner_conj_smul_left_probe
    (scalar : Complex) (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner (star scalar • left) right =
      complexCoordinateRealInner left (scalar • right) := by
  unfold complexCoordinateRealInner
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, smul_eq_mul, Complex.star_def,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem complexCoordinateAmplitudeSq_star_smul_probe
    (scalar : Complex) (vector : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (star scalar • vector) =
      Complex.normSq scalar * complexCoordinateAmplitudeSq vector := by
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [complexCoordinateVectorNormSq_smul]
  simp

private theorem finiteProjectionComplexTemporallyWeightedPairing_interval_sq_le_gradient
    (path : Real → ComplexVorticityHilbertState)
    (start finish massCeiling temporalCeiling : Real)
    (startLeFinish : start ≤ finish)
    (inputRadius : Nat)
    (inputRadiusPos : 0 < inputRadius)
    (testModes : Finset IntegerWavevector)
    (testModesZeroFree : ∀ wave ∈ testModes, wave ≠ 0)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalCeilingNonneg : 0 ≤ temporalCeiling)
    (temporalContinuous : ContinuousOn temporalWeight (Icc start finish))
    (temporalBound : ∀ time ∈ Icc start finish,
      ‖temporalWeight time‖ ≤ temporalCeiling)
    (pathContinuous : ContinuousOn path (Icc start finish))
    (pathTransverse : ∀ time ∈ Icc start finish,
      WholeStateTransverse (path time))
    (gradientSummableAE :
      ∀ᵐ time ∂volume.restrict (Ioc start finish),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (path time wave))
    (massBoundAE : ∀ᵐ time ∂volume.restrict (Ioc start finish),
      wholeVorticityEuclideanMass (path time) ≤ massCeiling)
    (gradientIntegrable : IntervalIntegrable
      (fun time => wholeStateVorticityGradientMass (path time))
      volume start finish) :
    let pairing : Real → Real := fun time =>
      ∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (temporalWeight time •
            (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube inputRadius) (path time)) wave -
              wholeStateVorticityNonlinearCoefficientAt (path time) wave))
    let testEnergy : Real :=
      ∑ wave ∈ testModes,
        3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (testCoefficient wave)
    (∫ time in start..finish, pairing time) ^ 2 ≤
      (finish - start) *
        (temporalCeiling ^ 2 * testEnergy *
          (728 * biotSavartSerrinConstant *
            (inputRadius : Real)⁻¹ * massCeiling)) *
        ∫ time in start..finish,
          wholeStateVorticityGradientMass (path time) := by
  dsimp only
  let pairing : Real → Real := fun time =>
    ∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        (temporalWeight time •
          (wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube inputRadius) (path time)) wave -
            wholeStateVorticityNonlinearCoefficientAt (path time) wave))
  let testEnergy : Real :=
    ∑ wave ∈ testModes,
      3 * integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq (testCoefficient wave)
  have testEnergyNonneg : 0 ≤ testEnergy := by
    dsimp only [testEnergy]
    exact Finset.sum_nonneg fun wave _ =>
      mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)))
        (complexCoordinateAmplitudeSq_nonneg _)
  have projectedPathContinuous : ContinuousOn
      (fun time => complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time))
      (Icc start finish) := by
    rw [show (fun time => complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)) =
      (sharpSupportProjectionCLM (integerWaveFrequencyCube inputRadius)) ∘
        path by
      funext time
      exact (sharpSupportProjectionCLM_apply
        (integerWaveFrequencyCube inputRadius) (path time)).symm]
    exact (sharpSupportProjectionCLM
      (integerWaveFrequencyCube inputRadius)).continuous.comp_continuousOn
        pathContinuous
  have pairingContinuous : ContinuousOn pairing (Icc start finish) := by
    dsimp only [pairing]
    apply continuousOn_finsetSum
    intro wave _waveMem
    have projectedNonlinearContinuous : ContinuousOn
        (fun time => wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time)) wave)
        (Icc start finish) := by
      apply wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        (fun time => complexSharpSupportProjection
          (integerWaveFrequencyCube inputRadius) (path time))
        wave start finish projectedPathContinuous
      intro time timeMem
      exact wholeStateTransverse_sharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)
        (pathTransverse time timeMem)
    have fullNonlinearContinuous : ContinuousOn
        (fun time => wholeStateVorticityNonlinearCoefficientAt
          (path time) wave) (Icc start finish) :=
      wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        path wave start finish pathContinuous pathTransverse
    have weightedDifferenceContinuous : ContinuousOn
        (fun time => temporalWeight time •
          (wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube inputRadius) (path time)) wave -
            wholeStateVorticityNonlinearCoefficientAt (path time) wave))
        (Icc start finish) :=
      temporalContinuous.smul
        (projectedNonlinearContinuous.sub fullNonlinearContinuous)
    have coefficientContinuous : ContinuousOn
        (fun _time : Real => testCoefficient wave) (Icc start finish) :=
      continuousOn_const
    have pairContinuous := coefficientContinuous.prodMk
      weightedDifferenceContinuous
    change ContinuousOn
      ((fun pair : ComplexCoordinateVector × ComplexCoordinateVector =>
          complexCoordinateRealInner pair.1 pair.2) ∘
        (fun time =>
          (testCoefficient wave,
            temporalWeight time •
              (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection
                    (integerWaveFrequencyCube inputRadius) (path time)) wave -
                wholeStateVorticityNonlinearCoefficientAt
                  (path time) wave))))
      (Icc start finish)
    exact complexCoordinateRealInner_prod_continuous.comp_continuousOn
      pairContinuous
  have pairingMeasurable :
      AEStronglyMeasurable pairing (volume.restrict (Ioc start finish)) :=
    (pairingContinuous.mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  have gradientIntegrableOn : Integrable
      (fun time => wholeStateVorticityGradientMass (path time))
      (volume.restrict (Ioc start finish)) :=
    gradientIntegrable.1
  have gradientNonneg :
      ∀ᵐ time ∂volume.restrict (Ioc start finish),
        0 ≤ wholeStateVorticityGradientMass (path time) :=
    Filter.Eventually.of_forall fun time => by
      unfold wholeStateVorticityGradientMass
      exact tsum_nonneg fun wave =>
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
  have timeMem :
      ∀ᵐ time ∂volume.restrict (Ioc start finish),
        time ∈ Ioc start finish := ae_restrict_mem measurableSet_Ioc
  have pointwise :
      ∀ᵐ time ∂volume.restrict (Ioc start finish),
        pairing time ^ 2 ≤
          (temporalCeiling ^ 2 * testEnergy *
            (728 * biotSavartSerrinConstant *
              (inputRadius : Real)⁻¹ * massCeiling)) *
            wholeStateVorticityGradientMass (path time) := by
    filter_upwards [timeMem, gradientSummableAE, massBoundAE] with
      time timeMem gradientSummable massLe
    have timeIcc : time ∈ Icc start finish :=
      ⟨timeMem.1.le, timeMem.2⟩
    let weightedCoefficient :
        IntegerWavevector → ComplexCoordinateVector := fun wave =>
      star (temporalWeight time) • testCoefficient wave
    have pairingEq : pairing time =
        ∑ wave ∈ testModes,
          complexCoordinateRealInner (weightedCoefficient wave)
            (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube inputRadius) (path time)) wave -
              wholeStateVorticityNonlinearCoefficientAt
                (path time) wave) := by
      dsimp only [pairing]
      apply Finset.sum_congr rfl
      intro wave _waveMem
      exact (complexCoordinateRealInner_conj_smul_left_probe
        (temporalWeight time) (testCoefficient wave)
        (wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time)) wave -
          wholeStateVorticityNonlinearCoefficientAt
            (path time) wave)).symm
    have weightedEnergyEq :
        (∑ wave ∈ testModes,
          3 * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq (weightedCoefficient wave)) =
          Complex.normSq (temporalWeight time) * testEnergy := by
      dsimp only [weightedCoefficient, testEnergy]
      calc
        (∑ wave ∈ testModes,
          3 * integerWaveViscousMultiplier wave *
            complexCoordinateAmplitudeSq
              (star (temporalWeight time) • testCoefficient wave)) =
            ∑ wave ∈ testModes,
              Complex.normSq (temporalWeight time) *
                (3 * integerWaveViscousMultiplier wave *
                  complexCoordinateAmplitudeSq (testCoefficient wave)) := by
          apply Finset.sum_congr rfl
          intro wave _waveMem
          rw [complexCoordinateAmplitudeSq_star_smul_probe]
          ring
        _ = Complex.normSq (temporalWeight time) *
            ∑ wave ∈ testModes,
              3 * integerWaveViscousMultiplier wave *
                complexCoordinateAmplitudeSq (testCoefficient wave) := by
          rw [Finset.mul_sum]
    have temporalSqLe :
        Complex.normSq (temporalWeight time) ≤ temporalCeiling ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact (sq_le_sq₀ (norm_nonneg _) temporalCeilingNonneg).2
        (temporalBound time timeIcc)
    have weightedEnergyLe :
        Complex.normSq (temporalWeight time) * testEnergy ≤
          temporalCeiling ^ 2 * testEnergy :=
      mul_le_mul_of_nonneg_right temporalSqLe testEnergyNonneg
    have basePairingSq :=
      finiteNonlinearProjectionPairing_sq_le_testEnergy_mul_differenceMass
        (path time) (pathTransverse time timeIcc) gradientSummable
        inputRadius testModes testModesZeroFree weightedCoefficient
    have differenceLe :=
      wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_le_agmon
        (path time) (pathTransverse time timeIcc) gradientSummable
        inputRadius inputRadiusPos
    have differenceNonneg : 0 ≤
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time))
          (path time) := by
      unfold wholeStateVorticityNonlinearDifferenceNegativeOneMass
      exact tsum_nonneg fun wave =>
        wholeStateVorticityNonlinearDifferenceNegativeOneDensity_nonneg
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time))
          (path time) wave
    have coefficientNonneg :
        0 ≤ 728 * biotSavartSerrinConstant *
          (inputRadius : Real)⁻¹ :=
      mul_nonneg
        (mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg)
        (inv_nonneg.mpr (Nat.cast_nonneg inputRadius))
    rw [pairingEq]
    calc
      _ ≤ (∑ wave ∈ testModes,
            3 * integerWaveViscousMultiplier wave *
              complexCoordinateAmplitudeSq (weightedCoefficient wave)) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time))
            (path time) := basePairingSq
      _ = (Complex.normSq (temporalWeight time) * testEnergy) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time))
            (path time) := by rw [weightedEnergyEq]
      _ ≤ (temporalCeiling ^ 2 * testEnergy) *
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time))
            (path time) :=
        mul_le_mul_of_nonneg_right weightedEnergyLe differenceNonneg
      _ ≤ (temporalCeiling ^ 2 * testEnergy) *
          (728 * biotSavartSerrinConstant *
            (inputRadius : Real)⁻¹ *
            wholeVorticityEuclideanMass (path time) *
            wholeStateVorticityGradientMass (path time)) :=
        mul_le_mul_of_nonneg_left differenceLe
          (mul_nonneg (sq_nonneg _) testEnergyNonneg)
      _ ≤ (temporalCeiling ^ 2 * testEnergy *
          (728 * biotSavartSerrinConstant *
            (inputRadius : Real)⁻¹ * massCeiling)) *
          wholeStateVorticityGradientMass (path time) := by
        have gradientNonnegTime :
            0 ≤ wholeStateVorticityGradientMass (path time) := by
          unfold wholeStateVorticityGradientMass
          exact tsum_nonneg fun wave =>
            mul_nonneg (integerWaveNormSq_nonneg wave)
              (complexCoordinateAmplitudeSq_nonneg _)
        have massScaledLe :=
          mul_le_mul_of_nonneg_left massLe coefficientNonneg
        have gradientScaledLe :=
          mul_le_mul_of_nonneg_right massScaledLe gradientNonnegTime
        have paid := mul_le_mul_of_nonneg_left gradientScaledLe
          (mul_nonneg (sq_nonneg temporalCeiling) testEnergyNonneg)
        simpa only [mul_assoc] using paid
  have integrated :=
    integral_pairing_sq_le_measure_mul_energy_mul_difference
      pairing (fun time => wholeStateVorticityGradientMass (path time))
      (temporalCeiling ^ 2 * testEnergy *
        (728 * biotSavartSerrinConstant *
          (inputRadius : Real)⁻¹ * massCeiling))
      pairingMeasurable gradientIntegrableOn gradientNonneg pointwise
  have measureEq :
      (volume.restrict (Ioc start finish)).real Set.univ =
        finish - start := by
    rw [Measure.real, Measure.restrict_apply_univ]
    rw [Real.volume_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr startLeFinish)
  rw [measureEq] at integrated
  simpa only [pairing, testEnergy,
    intervalIntegral.integral_of_le startLeFinish] using integrated

theorem finiteProjectionComplexTemporalPairing_scaled_sq_le_invBand
    (path : Real → ComplexVorticityHilbertState)
    (start finish scale timeLength errorBand normalizedMass
      gradientCeiling temporalCeiling : Real)
    (inputRadius : Nat)
    (testModes : Finset IntegerWavevector)
    (testModesZeroFree : ∀ wave ∈ testModes, wave ≠ 0)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (startLeFinish : start ≤ finish)
    (scalePos : 0 < scale)
    (timeLengthNonneg : 0 ≤ timeLength)
    (durationLe : finish - start ≤ scale ^ 2 * timeLength)
    (errorBandPos : 0 < errorBand)
    (errorBandLeRadius : errorBand ≤ scale * (inputRadius : Real))
    (normalizedMassNonneg : 0 ≤ normalizedMass)
    (temporalCeilingNonneg : 0 ≤ temporalCeiling)
    (temporalContinuous : ContinuousOn temporalWeight (Icc start finish))
    (temporalBound : ∀ time ∈ Icc start finish,
      ‖temporalWeight time‖ ≤ temporalCeiling)
    (pathContinuous : ContinuousOn path (Icc start finish))
    (pathTransverse : ∀ time ∈ Icc start finish,
      WholeStateTransverse (path time))
    (gradientSummableAE :
      ∀ᵐ time ∂volume.restrict (Ioc start finish),
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (path time wave))
    (scaledMassBoundAE : ∀ᵐ time ∂volume.restrict (Ioc start finish),
      scale * wholeVorticityEuclideanMass (path time) ≤ normalizedMass)
    (gradientIntegrable : IntervalIntegrable
      (fun time => wholeStateVorticityGradientMass (path time))
      volume start finish)
    (gradientPayment :
      scale * (∫ time in start..finish,
        wholeStateVorticityGradientMass (path time)) ≤ gradientCeiling) :
    let pairing : Real → Real := fun time =>
      ∑ wave ∈ testModes,
        complexCoordinateRealInner (testCoefficient wave)
          (temporalWeight time •
            (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube inputRadius) (path time)) wave -
              wholeStateVorticityNonlinearCoefficientAt (path time) wave))
    let testEnergy : Real :=
      ∑ wave ∈ testModes,
        3 * integerWaveViscousMultiplier wave *
          complexCoordinateAmplitudeSq (testCoefficient wave)
    (scale ^ 2 * ∫ time in start..finish, pairing time) ^ 2 ≤
      scale ^ 5 *
        (temporalCeiling ^ 2 *
          (timeLength * testEnergy *
            (728 * biotSavartSerrinConstant * normalizedMass *
              gradientCeiling / errorBand))) := by
  dsimp only
  let pairing : Real → Real := fun time =>
    ∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        (temporalWeight time •
          (wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube inputRadius) (path time)) wave -
            wholeStateVorticityNonlinearCoefficientAt (path time) wave))
  let testEnergy : Real :=
    ∑ wave ∈ testModes,
      3 * integerWaveViscousMultiplier wave *
        complexCoordinateAmplitudeSq (testCoefficient wave)
  have radiusCastPos : 0 < (inputRadius : Real) := by
    have : 0 < scale * (inputRadius : Real) :=
      errorBandPos.trans_le errorBandLeRadius
    rcases mul_pos_iff.mp this with positive | negative
    · exact positive.2
    · exact (not_lt_of_ge scalePos.le negative.1).elim
  have inputRadiusPos : 0 < inputRadius := by exact_mod_cast radiusCastPos
  have massBoundAE : ∀ᵐ time ∂volume.restrict (Ioc start finish),
      wholeVorticityEuclideanMass (path time) ≤ normalizedMass / scale := by
    filter_upwards [scaledMassBoundAE] with time massLe
    exact (le_div_iff₀ scalePos).2 (by simpa [mul_comm] using massLe)
  have raw :=
    finiteProjectionComplexTemporallyWeightedPairing_interval_sq_le_gradient
      path start finish (normalizedMass / scale) temporalCeiling startLeFinish
      inputRadius inputRadiusPos testModes testModesZeroFree testCoefficient
      temporalWeight temporalCeilingNonneg temporalContinuous temporalBound
      pathContinuous pathTransverse gradientSummableAE massBoundAE
      gradientIntegrable
  have radiusInvLe : (inputRadius : Real)⁻¹ ≤ scale / errorBand := by
    apply (le_div_iff₀ errorBandPos).2
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ radiusCastPos).2 (by
      simpa [mul_comm] using errorBandLeRadius)
  have gradientIntegralNonneg :
      0 ≤ ∫ time in start..finish,
        wholeStateVorticityGradientMass (path time) := by
    apply intervalIntegral.integral_nonneg_of_forall startLeFinish
    intro time
    unfold wholeStateVorticityGradientMass
    exact tsum_nonneg fun wave =>
      mul_nonneg (integerWaveNormSq_nonneg wave)
        (complexCoordinateAmplitudeSq_nonneg _)
  have gradientIntegralLe :
      (∫ time in start..finish,
        wholeStateVorticityGradientMass (path time)) ≤
        gradientCeiling / scale :=
    (le_div_iff₀ scalePos).2 (by simpa [mul_comm] using gradientPayment)
  have testEnergyNonneg : 0 ≤ testEnergy := by
    dsimp only [testEnergy]
    exact Finset.sum_nonneg fun wave _ =>
      mul_nonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)))
        (complexCoordinateAmplitudeSq_nonneg _)
  have massCeilingNonneg : 0 ≤ normalizedMass / scale :=
    div_nonneg normalizedMassNonneg scalePos.le
  have coefficientNonneg :
      0 ≤ 728 * biotSavartSerrinConstant :=
    mul_nonneg (by norm_num) biotSavartSerrinConstant_nonneg
  have sourceFactorNonneg :
      0 ≤ 728 * biotSavartSerrinConstant *
        (inputRadius : Real)⁻¹ * (normalizedMass / scale) :=
    mul_nonneg
      (mul_nonneg coefficientNonneg (inv_nonneg.mpr radiusCastPos.le))
      massCeilingNonneg
  have sourceFactorLe :
      728 * biotSavartSerrinConstant *
          (inputRadius : Real)⁻¹ * (normalizedMass / scale) ≤
        728 * biotSavartSerrinConstant *
          (scale / errorBand) * (normalizedMass / scale) := by
    gcongr
  have rawScaled :
      (∫ time in start..finish, pairing time) ^ 2 ≤
        (scale ^ 2 * timeLength) *
          (temporalCeiling ^ 2 * testEnergy *
            (728 * biotSavartSerrinConstant *
              (scale / errorBand) * (normalizedMass / scale))) *
          (gradientCeiling / scale) := by
    calc
      (∫ time in start..finish, pairing time) ^ 2 ≤
          (finish - start) *
            (temporalCeiling ^ 2 * testEnergy *
              (728 * biotSavartSerrinConstant *
                (inputRadius : Real)⁻¹ * (normalizedMass / scale))) *
            ∫ time in start..finish,
              wholeStateVorticityGradientMass (path time) := by
        simpa only [pairing, testEnergy] using raw
      _ ≤ (scale ^ 2 * timeLength) *
          (temporalCeiling ^ 2 * testEnergy *
            (728 * biotSavartSerrinConstant *
              (scale / errorBand) * (normalizedMass / scale))) *
          (gradientCeiling / scale) := by
        gcongr
  have simplified :
      (∫ time in start..finish, pairing time) ^ 2 ≤
        scale *
          (temporalCeiling ^ 2 *
            (timeLength * testEnergy *
              (728 * biotSavartSerrinConstant * normalizedMass *
                gradientCeiling / errorBand))) := by
    calc
      _ ≤ (scale ^ 2 * timeLength) *
          (temporalCeiling ^ 2 * testEnergy *
            (728 * biotSavartSerrinConstant *
              (scale / errorBand) * (normalizedMass / scale))) *
          (gradientCeiling / scale) := rawScaled
      _ = scale *
          (temporalCeiling ^ 2 *
            (timeLength * testEnergy *
              (728 * biotSavartSerrinConstant * normalizedMass *
                gradientCeiling / errorBand))) := by
        field_simp [scalePos.ne', errorBandPos.ne']
  calc
    (scale ^ 2 * ∫ time in start..finish, pairing time) ^ 2 =
        scale ^ 4 * (∫ time in start..finish, pairing time) ^ 2 := by
      ring
    _ ≤ scale ^ 4 *
        (scale *
          (temporalCeiling ^ 2 *
            (timeLength * testEnergy *
              (728 * biotSavartSerrinConstant * normalizedMass *
                gradientCeiling / errorBand))) ) :=
      mul_le_mul_of_nonneg_left simplified (pow_nonneg scalePos.le 4)
    _ = _ := by ring

theorem auxiliaryProjectionRadius_bounds
    (scale errorBand : Real)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (errorBandPos : 0 < errorBand) :
    let inputRadius : Nat := Nat.ceil (errorBand / scale)
    0 < inputRadius ∧
      errorBand ≤ scale * (inputRadius : Real) ∧
      scale * (inputRadius : Real) ≤ errorBand + 1 := by
  dsimp only
  have ratioPos : 0 < errorBand / scale := div_pos errorBandPos scalePos
  have inputRadiusPos : 0 < Nat.ceil (errorBand / scale) :=
    Nat.ceil_pos.mpr ratioPos
  have ratioLe :
      errorBand / scale ≤ (Nat.ceil (errorBand / scale) : Real) :=
    Nat.le_ceil _
  have errorBandLe :
      errorBand ≤ scale * (Nat.ceil (errorBand / scale) : Real) := by
    simpa only [mul_comm] using (div_le_iff₀ scalePos).mp ratioLe
  have ceilLt :
      (Nat.ceil (errorBand / scale) : Real) <
        errorBand / scale + 1 :=
    Nat.ceil_lt_add_one ratioPos.le
  have scaledLt := mul_lt_mul_of_pos_left ceilLt scalePos
  have scaledRadiusLt :
      scale * (Nat.ceil (errorBand / scale) : Real) < errorBand + scale := by
    calc
      scale * (Nat.ceil (errorBand / scale) : Real) <
          scale * (errorBand / scale + 1) := scaledLt
      _ = errorBand + scale := by field_simp [scalePos.ne']
  exact ⟨inputRadiusPos, errorBandLe,
    scaledRadiusLt.le.trans (add_le_add_right scaleLeOne errorBand)⟩

theorem finiteProjectionComplexTemporalPairing_eq_intervalIntegral
    (path : Real → ComplexVorticityHilbertState)
    (start finish : Real)
    (startLeFinish : start ≤ finish)
    (inputRadius : Nat)
    (testModes : Finset IntegerWavevector)
    (testCoefficient : IntegerWavevector → ComplexCoordinateVector)
    (temporalWeight : Real → Complex)
    (temporalContinuous : ContinuousOn temporalWeight (Icc start finish))
    (pathContinuous : ContinuousOn path (Icc start finish))
    (pathTransverse : ∀ time ∈ Icc start finish,
      WholeStateTransverse (path time)) :
    (∑ wave ∈ testModes,
      complexCoordinateRealInner (testCoefficient wave)
        (∫ time in start..finish,
          temporalWeight time •
            (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube inputRadius) (path time)) wave -
              wholeStateVorticityNonlinearCoefficientAt
                (path time) wave))) =
      ∫ time in start..finish,
        ∑ wave ∈ testModes,
          complexCoordinateRealInner (testCoefficient wave)
            (temporalWeight time •
              (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection
                    (integerWaveFrequencyCube inputRadius) (path time)) wave -
                wholeStateVorticityNonlinearCoefficientAt
                  (path time) wave)) := by
  have projectedPathContinuous : ContinuousOn
      (fun time => complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time))
      (Icc start finish) := by
    rw [show (fun time => complexSharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)) =
      (sharpSupportProjectionCLM (integerWaveFrequencyCube inputRadius)) ∘
        path by
      funext time
      exact (sharpSupportProjectionCLM_apply
        (integerWaveFrequencyCube inputRadius) (path time)).symm]
    exact (sharpSupportProjectionCLM
      (integerWaveFrequencyCube inputRadius)).continuous.comp_continuousOn
        pathContinuous
  have rowContinuous (wave : IntegerWavevector) : ContinuousOn
      (fun time => temporalWeight time •
        (wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time)) wave -
          wholeStateVorticityNonlinearCoefficientAt (path time) wave))
      (Icc start finish) := by
    have projectedNonlinearContinuous : ContinuousOn
        (fun time => wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection
            (integerWaveFrequencyCube inputRadius) (path time)) wave)
        (Icc start finish) := by
      apply wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        (fun time => complexSharpSupportProjection
          (integerWaveFrequencyCube inputRadius) (path time))
        wave start finish projectedPathContinuous
      intro time timeMem
      exact wholeStateTransverse_sharpSupportProjection
        (integerWaveFrequencyCube inputRadius) (path time)
        (pathTransverse time timeMem)
    have fullNonlinearContinuous : ContinuousOn
        (fun time => wholeStateVorticityNonlinearCoefficientAt
          (path time) wave) (Icc start finish) :=
      wholeStateVorticityNonlinearCoefficientAt_comp_continuousOn
        path wave start finish pathContinuous pathTransverse
    exact temporalContinuous.smul
      (projectedNonlinearContinuous.sub fullNonlinearContinuous)
  have rowIntegrable (wave : IntegerWavevector) : IntervalIntegrable
      (fun time => temporalWeight time •
        (wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection
              (integerWaveFrequencyCube inputRadius) (path time)) wave -
          wholeStateVorticityNonlinearCoefficientAt (path time) wave))
      volume start finish :=
    ContinuousOn.intervalIntegrable_of_Icc startLeFinish
      (rowContinuous wave)
  have scalarIntegrable (wave : IntegerWavevector) : IntervalIntegrable
      (fun time =>
        complexCoordinateRealInner (testCoefficient wave)
          (temporalWeight time •
            (wholeStateVorticityNonlinearCoefficientAt
                (complexSharpSupportProjection
                  (integerWaveFrequencyCube inputRadius) (path time)) wave -
              wholeStateVorticityNonlinearCoefficientAt (path time) wave)))
      volume start finish := by
    apply ContinuousOn.intervalIntegrable_of_Icc startLeFinish
    refine ((complexCoordinateRealInnerRightCLM
      (testCoefficient wave)).continuous.comp_continuousOn
        (rowContinuous wave)).congr ?_
    intro time _timeMem
    simpa only [Function.comp_apply] using
      (complexCoordinateRealInnerRightCLM_apply
        (testCoefficient wave)
        (temporalWeight time •
          (wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection
                (integerWaveFrequencyCube inputRadius) (path time)) wave -
            wholeStateVorticityNonlinearCoefficientAt
              (path time) wave))).symm
  calc
    _ = ∑ wave ∈ testModes,
        ∫ time in start..finish,
          complexCoordinateRealInner (testCoefficient wave)
            (temporalWeight time •
              (wholeStateVorticityNonlinearCoefficientAt
                  (complexSharpSupportProjection
                    (integerWaveFrequencyCube inputRadius) (path time)) wave -
                wholeStateVorticityNonlinearCoefficientAt
                  (path time) wave)) := by
      apply Finset.sum_congr rfl
      intro wave _waveMem
      symm
      exact (complexCoordinateRealInnerRightCLM
        (testCoefficient wave)).intervalIntegral_comp_comm
          (rowIntegrable wave)
    _ = _ := (intervalIntegral.integral_finsetSum
      (fun wave _waveMem => scalarIntegrable wave)).symm


set_option maxHeartbeats 800000 in
private theorem receipt_fastWindow_generates_actual_scaled_localMass
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (level radiusConstant peakConstant : Real)
    (levelFour : 4 ≤ level)
    (radiusConstantNonneg : 0 ≤ radiusConstant)
    (peakConstantPos : 0 < peakConstant)
    (radiusLe : (radius : Real) ≤ radiusConstant * level)
    (wholeMassUpper : ∀ time,
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ level)
    (rateLower :
      peakConstant * level ^ 3 * requestedTime <
        ∫ time,
          finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime)) :
    let gradientConstant : Real :=
      (16 * 24336) / (nu.coeff * (2 * Real.pi) ^ 2) ^ 4
    let lipschitzConstant : Real :=
      Real.sqrt
        ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          gradientConstant)
    ∃ time : Icc (0 : Real) requestedTime,
    ∃ center ∈ physicalUnitCell,
      FiniteStateFourierReality (receipt.wholePath time) ∧
      finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius)
            (receipt.wholePath time)) ≤
        gradientConstant * level ^ 3 ∧
      peakConstant * level ^ 3 <
        finiteStateVorticityStretchingWork (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius)
            (receipt.wholePath time)) ∧
      peakConstant ^ 5 * (Real.pi * 4 / 3) /
          (32 * lipschitzConstant ^ 3) ≤
        ∫ x in Metric.closedBall (0 : PhysicalSpace)
            (peakConstant / (2 * lipschitzConstant)),
          ‖((level⁻¹) ^ 2 : Real) •
            finiteRealComplexFourierField (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time))
              (center + level⁻¹ • x)‖ ^ 2 := by
  dsimp only
  let modes := wholeRestartModes radius
  let projected : Icc (0 : Real) requestedTime →
      ComplexVorticityHilbertState := fun time =>
    complexSharpSupportProjection modes (receipt.wholePath time)
  let stretching : Icc (0 : Real) requestedTime → Real := fun time =>
    finiteStateVorticityStretchingWork modes (projected time)
  let gradient : Icc (0 : Real) requestedTime → Real := fun time =>
    finiteStateVorticityEnstrophyMass modes (projected time)
  let viscousRate : Real := nu.coeff * (2 * Real.pi) ^ 2 / 2
  let gradientConstant : Real :=
    (16 * 24336) / (nu.coeff * (2 * Real.pi) ^ 2) ^ 4
  let lipschitzConstant : Real :=
    Real.sqrt
      ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        gradientConstant)
  have levelPos : 0 < level := lt_of_lt_of_le (by norm_num) levelFour
  have requestedTimePos : 0 < requestedTime := receipt.requestedTimePos
  have viscousBasePos : 0 < nu.coeff * (2 * Real.pi) ^ 2 := by
    exact mul_pos nu.coeff_pos
      (sq_pos_of_pos (mul_pos zero_lt_two Real.pi_pos))
  have viscousRateNonneg : 0 ≤ viscousRate := by
    dsimp only [viscousRate]
    positivity
  have gradientConstantPos : 0 < gradientConstant := by
    dsimp only [gradientConstant]
    positivity
  have cardConstantNonneg : 0 ≤ (2 * radiusConstant + 1) ^ 3 := by
    positivity
  have lipschitzArgumentPos :
      0 < (2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        gradientConstant := by positivity
  have lipschitzConstantPos : 0 < lipschitzConstant := by
    dsimp only [lipschitzConstant]
    exact Real.sqrt_pos.2 lipschitzArgumentPos
  have zeroNotMem : (0 : IntegerWavevector) ∉ modes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
  have projectedContinuous : Continuous projected := by
    rw [show projected =
        (sharpSupportProjectionCLM modes) ∘ receipt.wholePath by
      funext time
      exact (sharpSupportProjectionCLM_apply modes
        (receipt.wholePath time)).symm]
    exact (sharpSupportProjectionCLM modes).continuous.comp
      receipt.wholePath.continuous
  have stretchingContinuous : Continuous stretching := by
    unfold stretching finiteStateVorticityStretchingWork
    apply continuous_finsetSum
    intro occurrence _occurrenceMem
    unfold finiteStateVorticityStretchingOccurrenceWork
    have outputContinuous : Continuous (fun time =>
        projected time (finiteVorticityInteractionOutput occurrence)) :=
      (lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 (finiteVorticityInteractionOutput occurrence)).continuous.comp
        projectedContinuous
    have pairContinuous : Continuous (fun time =>
        finiteStateVorticityStretchingPairContribution
          (projected time)
          (finiteVorticityInteractionFirst occurrence,
            finiteVorticityInteractionSecond occurrence)) := by
      have firstContinuous : Continuous (fun time =>
          projected time (finiteVorticityInteractionFirst occurrence)) :=
        (lp.evalCLM ℂ
          (fun _ : IntegerWavevector => ComplexCoordinateVector)
          2 (finiteVorticityInteractionFirst occurrence)).continuous.comp
          projectedContinuous
      have derivativeContinuous : Continuous (fun time =>
          complexWavevector (finiteVorticityInteractionSecond occurrence) ⬝ᵥ
            projected time (finiteVorticityInteractionFirst occurrence)) :=
        continuous_const.dotProduct firstContinuous
      have velocityContinuous : Continuous (fun time =>
          finiteStateVelocityCoefficient (projected time)
            (finiteVorticityInteractionSecond occurrence)) :=
        (finiteStateVelocityCoefficient_contDiff
          (finiteVorticityInteractionSecond occurrence)).continuous.comp
            projectedContinuous
      unfold finiteStateVorticityStretchingPairContribution
      exact (continuous_const.mul derivativeContinuous).smul
        velocityContinuous
    exact complexCoordinateRealInner_prod_continuous.comp
      (outputContinuous.prodMk pairContinuous)
  have gradientContinuous : Continuous gradient := by
    unfold gradient finiteStateVorticityEnstrophyMass
    apply continuous_finsetSum
    intro wave _waveMem
    exact continuous_const.mul
      (complexCoordinateAmplitudeSq_continuous.comp
        ((lp.evalCLM ℂ
          (fun _ : IntegerWavevector => ComplexCoordinateVector)
          2 wave).continuous.comp projectedContinuous))
  have rateIntegrable :
      Integrable (fun time => stretching time - viscousRate * gradient time)
        (commonTimeMeasure requestedTime) := by
    have generated : IntegrableOn
        (fun time => stretching time - viscousRate * gradient time)
        Set.univ (commonTimeMeasure requestedTime) :=
      (stretchingContinuous.sub
        (continuous_const.mul gradientContinuous)).continuousOn
        |>.integrableOn_compact isCompact_univ
    simpa only [MeasureTheory.integrableOn_univ, viscousRate] using generated
  have measureDuration :
      (commonTimeMeasure requestedTime).real Set.univ = requestedTime := by
    let terminal : Set.Icc (0 : Real) requestedTime :=
      ⟨requestedTime, requestedTimePos.le, le_rfl⟩
    have payment :=
      ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation.commonTimeMeasure_Iic_real
        requestedTime requestedTimePos.le terminal
    have terminalIic : Set.Iic terminal = Set.univ := by
      ext current
      simp only [Set.mem_Iic, Set.mem_univ, iff_true]
      exact current.2.2
    simpa only [terminalIic, Measure.restrict_univ] using payment
  have validAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        FiniteStateFourierReality (receipt.wholePath time) :=
    wholePath_fourierReality_ae receipt
  have gradientNonneg :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime), 0 ≤ gradient time :=
    Filter.Eventually.of_forall fun time =>
      finiteStateVorticityEnstrophyMass_nonneg modes (projected time)
  have projectedMassUpper (time : Icc (0 : Real) requestedTime) :
      finiteStateVorticityCoefficientEnstrophy modes (projected time) ≤
        level := by
    have projectedSupported : ∀ wave, wave ∉ modes →
        projected time wave = 0 :=
      complexSharpSupportProjection_supported modes (receipt.wholePath time)
    calc
      finiteStateVorticityCoefficientEnstrophy modes (projected time) =
          wholeVorticityEuclideanMass (projected time) :=
        (wholeVorticityEuclideanMass_eq_finite_of_supported
          modes (projected time) projectedSupported).symm
      _ ≤ wholeVorticityEuclideanMass (receipt.wholePath time) :=
        wholeVorticityEuclideanMass_sharpSupportProjection_le
          modes (receipt.wholePath time)
      _ ≤ level := wholeMassUpper time
  have badRateNonpos (time : Icc (0 : Real) requestedTime)
      (gradientLarge : gradientConstant * level ^ 3 < gradient time) :
      stretching time - viscousRate * gradient time ≤ 0 := by
    apply finite_stretching_rate_nonpos_of_gradient_large
      modes (projected time) zeroNotMem
      (complexSharpSupportProjection_transverse modes
        (receipt.wholePath time) (wholePath_transverse receipt time))
      nu.coeff level nu.coeff_pos levelPos.le (projectedMassUpper time)
    change 16 * 24336 * level ^ 3 <
      (nu.coeff * (2 * Real.pi) ^ 2) ^ 4 * gradient time
    calc
      16 * 24336 * level ^ 3 =
          (gradientConstant * level ^ 3) *
            (nu.coeff * (2 * Real.pi) ^ 2) ^ 4 := by
        dsimp only [gradientConstant]
        field_simp [nu.coeff_pos.ne', Real.pi_ne_zero]
      _ < gradient time * (nu.coeff * (2 * Real.pi) ^ 2) ^ 4 :=
        mul_lt_mul_of_pos_right gradientLarge (pow_pos viscousBasePos 4)
      _ = (nu.coeff * (2 * Real.pi) ^ 2) ^ 4 * gradient time := by ring
  have rateLower' :
      peakConstant * level ^ 3 * requestedTime <
        ∫ time, stretching time - viscousRate * gradient time
          ∂(commonTimeMeasure requestedTime) := by
    simpa only [stretching, gradient, projected, modes, viscousRate] using
      rateLower
  obtain ⟨time, timeReality, gradientGood, stretchingGood⟩ :=
    finiteMeasure_exists_valid_good_stretching_state
      (commonTimeMeasure requestedTime)
      (fun time => FiniteStateFourierReality (receipt.wholePath time))
      stretching gradient viscousRate (gradientConstant * level ^ 3)
      (peakConstant * level ^ 3 * requestedTime) requestedTime
      requestedTimePos viscousRateNonneg
      (mul_pos
        (mul_pos peakConstantPos (pow_pos levelPos 3)) requestedTimePos)
      measureDuration validAE gradientNonneg rateIntegrable badRateNonpos
      rateLower'
  have stretchingScaleCritical :
      peakConstant * level ^ 3 < stretching time := by
    convert stretchingGood using 1
    field_simp [requestedTimePos.ne']
  have cardBound : ((modes.card : Nat) : Real) ≤
      (2 * radiusConstant + 1) ^ 3 * level ^ 3 := by
    simpa only [modes] using
      wholeRestartModes_card_cast_le_scaled_cube radius level radiusConstant
        (by linarith) radiusConstantNonneg radiusLe
  have gradientArgumentBound :
      ((modes.card : Real) * (2 * Real.pi) ^ 2 * gradient time) ≤
        ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          gradientConstant) * level ^ 6 := by
    have gradientAtNonneg : 0 ≤ gradient time :=
      finiteStateVorticityEnstrophyMass_nonneg modes (projected time)
    calc
      (modes.card : Real) * (2 * Real.pi) ^ 2 * gradient time ≤
          ((2 * radiusConstant + 1) ^ 3 * level ^ 3) *
            (2 * Real.pi) ^ 2 * (gradientConstant * level ^ 3) := by
        gcongr
      _ = ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          gradientConstant) * level ^ 6 := by ring
  have lipschitzUpper :
      Real.sqrt ((modes.card : Real) * (2 * Real.pi) ^ 2 * gradient time) ≤
        lipschitzConstant * level ^ 3 := by
    calc
      Real.sqrt ((modes.card : Real) * (2 * Real.pi) ^ 2 * gradient time) ≤
          Real.sqrt (((2 * radiusConstant + 1) ^ 3 *
            (2 * Real.pi) ^ 2 * gradientConstant) * level ^ 6) :=
        Real.sqrt_le_sqrt gradientArgumentBound
      _ = lipschitzConstant * level ^ 3 := by
        dsimp only [lipschitzConstant]
        rw [show level ^ 6 = (level ^ 3) ^ 2 by ring,
          Real.sqrt_mul lipschitzArgumentPos.le, Real.sqrt_sq_eq_abs,
          abs_of_pos (pow_pos levelPos 3)]
  have projectedSupported : ∀ wave, wave ∉ modes →
      projected time wave = 0 :=
    complexSharpSupportProjection_supported modes (receipt.wholePath time)
  have projectedTransverse : ∀ wave ∈ modes,
      complexWavevector wave ⬝ᵥ projected time wave = 0 :=
    complexSharpSupportProjection_transverse modes (receipt.wholePath time)
      (wholePath_transverse receipt time)
  have projectedReality : FiniteStateFourierReality (projected time) :=
    complexSharpSupportProjection_reality modes (receipt.wholePath time)
      (fun _wave waveMem => negClosed waveMem) timeReality
  obtain ⟨center, centerMem, localMass⟩ :=
    finiteStretching_generates_scaled_closedBall_mass
      modes zeroNotMem negClosed (projected time) projectedSupported
      projectedTransverse projectedReality
      (peakConstant * level ^ 3) level (lipschitzConstant * level ^ 3)
      level⁻¹
      (mul_pos peakConstantPos (pow_pos levelPos 3)) levelPos
      (mul_pos lipschitzConstantPos (pow_pos levelPos 3))
      (inv_pos.mpr levelPos)
      (by
        have stretchingPos : 0 < stretching time :=
          (mul_pos peakConstantPos (pow_pos levelPos 3)).trans
            stretchingScaleCritical
        rw [abs_of_pos stretchingPos]
        exact stretchingScaleCritical.le)
      (projectedMassUpper time)
      (by simpa only [gradient] using lipschitzUpper)
  exact ⟨time, center, centerMem, timeReality, gradientGood,
    stretchingScaleCritical, by
      have radiusEq :
          (((peakConstant * level ^ 3 / level) /
              (2 * (lipschitzConstant * level ^ 3))) / level⁻¹) =
            peakConstant / (2 * lipschitzConstant) := by
        field_simp [levelPos.ne', lipschitzConstantPos.ne']
      rw [← radiusEq]
      rw [← scaleCritical_closedBall_lower_constant center
        peakConstant lipschitzConstant level peakConstantPos
        lipschitzConstantPos levelPos]
      simpa only [modes, projected] using localMass⟩

private theorem receipt_sourceAverage_fast_generates_uniform_localMass
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (radius : Nat)
    (level normalizedDuration durationCeiling
      sourceGradientConstant errorSlope : Real)
    (levelFour : 4 ≤ level)
    (normalizedDurationPos : 0 < normalizedDuration)
    (durationCeilingPos : 0 < durationCeiling)
    (durationFast : normalizedDuration ≤ durationCeiling)
    (sourceGradientConstantNonneg : 0 ≤ sourceGradientConstant)
    (errorSlopeNonneg : 0 ≤ errorSlope)
    (radiusUpper : (radius : Real) ≤
      8 * (sourceGradientConstant +
          errorSlope * normalizedDuration / 8 + 1) * level + 2)
    (wholeMassUpper : ∀ time,
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ level)
    (rateLower :
      (7 / (512 * normalizedDuration)) * level ^ 3 * requestedTime <
        ∫ time,
          finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime)) :
    let radiusConstant : Real :=
      8 * (sourceGradientConstant +
          errorSlope * durationCeiling / 8 + 1) + 1 / 2
    let peakConstant : Real := 7 / (512 * durationCeiling)
    let selectorGradientConstant : Real :=
      (16 * 24336) / (nu.coeff * (2 * Real.pi) ^ 2) ^ 4
    let lipschitzConstant : Real :=
      Real.sqrt
        ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          selectorGradientConstant)
    ∃ time : Icc (0 : Real) requestedTime,
    ∃ center ∈ physicalUnitCell,
      FiniteStateFourierReality (receipt.wholePath time) ∧
      finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius)
            (receipt.wholePath time)) ≤
        selectorGradientConstant * level ^ 3 ∧
      peakConstant * level ^ 3 <
        finiteStateVorticityStretchingWork (wholeRestartModes radius)
          (complexSharpSupportProjection (wholeRestartModes radius)
            (receipt.wholePath time)) ∧
      peakConstant ^ 5 * (Real.pi * 4 / 3) /
          (32 * lipschitzConstant ^ 3) ≤
        ∫ x in Metric.closedBall (0 : PhysicalSpace)
            (peakConstant / (2 * lipschitzConstant)),
          ‖((level⁻¹) ^ 2 : Real) •
            finiteRealComplexFourierField (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time))
              (center + level⁻¹ • x)‖ ^ 2 := by
  dsimp only
  let radiusConstant : Real :=
    8 * (sourceGradientConstant +
        errorSlope * durationCeiling / 8 + 1) + 1 / 2
  let peakConstant : Real := 7 / (512 * durationCeiling)
  have levelPos : 0 < level := lt_of_lt_of_le (by norm_num) levelFour
  have sourceRadiusMonotone :
      8 * (sourceGradientConstant +
          errorSlope * normalizedDuration / 8 + 1) ≤
        8 * (sourceGradientConstant +
          errorSlope * durationCeiling / 8 + 1) := by
    gcongr
  have radiusConstantNonneg : 0 ≤ radiusConstant := by
    dsimp only [radiusConstant]
    positivity
  have uniformRadius : (radius : Real) ≤ radiusConstant * level := by
    calc
      (radius : Real) ≤
          8 * (sourceGradientConstant +
            errorSlope * normalizedDuration / 8 + 1) * level + 2 :=
        radiusUpper
      _ ≤ 8 * (sourceGradientConstant +
            errorSlope * durationCeiling / 8 + 1) * level + 2 := by
        gcongr
      _ ≤ radiusConstant * level := by
        dsimp only [radiusConstant]
        nlinarith
  have peakConstantPos : 0 < peakConstant := by
    dsimp only [peakConstant]
    positivity
  have peakLe :
      peakConstant ≤ 7 / (512 * normalizedDuration) := by
    dsimp only [peakConstant]
    gcongr
  have uniformRate :
      peakConstant * level ^ 3 * requestedTime <
        ∫ time,
          finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (receipt.wholePath time)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (receipt.wholePath time))
          ∂(commonTimeMeasure requestedTime) := by
    apply lt_of_le_of_lt _ rateLower
    have requestedTimeNonneg : 0 ≤ requestedTime :=
      receipt.requestedTimePos.le
    gcongr
  simpa only [radiusConstant, peakConstant] using
    receipt_fastWindow_generates_actual_scaled_localMass
      receipt radius level radiusConstant peakConstant levelFour
      radiusConstantNonneg peakConstantPos uniformRadius wholeMassUpper
      uniformRate

/--
The actual scale-critical stretching receipt has an exhaustive normalized-time
disposition.  If its source-generated normalized duration is below the chosen
ceiling, the same receipt generates one translated, fixed scaled ball with a
uniform nonzero vorticity-mass quantum.  Otherwise the very same source
witness exposes the slow normalized window for the downstream compactness
consumer.
-/
theorem
    sourceGeneratedNativeAccumulationScaleCriticalActualLocalMassOrSlowWindow
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (level durationCeiling : Real)
    (levelFour : 4 ≤ level)
    (durationCeilingPos : 0 < durationCeiling)
    (initialLeHalf :
      restartPhysicalVorticityMass initial 0 ≤ level / 2) :
    let viscousConstant : Real :=
      nu.coeff ^ 2 * (2 * Real.pi) ^ 2
    let cubicConstant : Real :=
      (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * viscousConstant)
    let sourceGradientConstant : Real :=
      (2 * cubicConstant) / viscousConstant
    let errorSlope : Real :=
      (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
        (7 * nu.coeff * viscousConstant)
    let radiusConstant : Real :=
      8 * (sourceGradientConstant +
          errorSlope * durationCeiling / 8 + 1) + 1 / 2
    let peakConstant : Real := 7 / (512 * durationCeiling)
    let selectorGradientConstant : Real :=
      (16 * 24336) / (nu.coeff * (2 * Real.pi) ^ 2) ^ 4
    let lipschitzConstant : Real :=
      Real.sqrt
        ((2 * radiusConstant + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          selectorGradientConstant)
    ∃ length edge radius : Nat,
    ∃ lowerTime upperTime normalizedDuration : Real,
    ∃ segmentInitial : ComplexVorticityHilbertState,
    ∃ segmentTime : Real,
    ∃ _segmentTimePos : 0 < segmentTime,
    ∃ segmentReceipt :
      WholeContinuousMildSerrinReceipt nu segmentInitial segmentTime,
    ∃ absoluteTime : Icc (0 : Real) segmentTime → Real,
      0 ≤ lowerTime ∧
      lowerTime < upperTime ∧
      upperTime ≤ elapsedTime initial length ∧
      (∀ time ∈
          Icc (elapsedTime initial 1) (elapsedTime initial length),
        wholeVorticityEuclideanMass
            (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
          level + 2) ∧
      normalizedDuration = level ^ 2 * (upperTime - lowerTime) ∧
      0 < normalizedDuration ∧
      nu.coeff / (8 * cubicConstant) ≤ normalizedDuration ∧
      edge < length ∧
      0 < radius ∧
      8 * (sourceGradientConstant +
          errorSlope * normalizedDuration / 8 + 1) * level ≤
        (radius : Real) ∧
      segmentTime ≤ normalizedDuration / level ^ 2 ∧
      (radius : Real) ≤
        8 * (sourceGradientConstant +
          errorSlope * normalizedDuration / 8 + 1) * level + 2 ∧
      (∀ localTime,
        absoluteTime localTime ∈ Icc lowerTime upperTime ∧
        segmentReceipt.wholePath localTime =
          wholeRestartPrefixPhysicalTrajectory initial length
            (absoluteTime localTime)) ∧
      (∀ time ∈ Icc lowerTime upperTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
          wholeVorticityEuclideanMass
              (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
            level) ∧
      (∀ localTime,
        level / 2 ≤
            wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ∧
          wholeVorticityEuclideanMass
              (segmentReceipt.wholePath localTime) ≤ level) ∧
      (7 / (512 * normalizedDuration)) * level ^ 3 * segmentTime <
        ∫ localTime,
          (finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (segmentReceipt.wholePath localTime)) -
            (nu.coeff * (2 * Real.pi) ^ 2 / 2) *
              finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
                (complexSharpSupportProjection (wholeRestartModes radius)
                  (segmentReceipt.wholePath localTime)))
          ∂(commonTimeMeasure segmentTime) ∧
      ((normalizedDuration ≤ durationCeiling ∧
        ∃ localTime : Icc (0 : Real) segmentTime,
        ∃ center ∈ physicalUnitCell,
          FiniteStateFourierReality
            (segmentReceipt.wholePath localTime) ∧
          finiteStateVorticityEnstrophyMass (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (segmentReceipt.wholePath localTime)) ≤
            selectorGradientConstant * level ^ 3 ∧
          peakConstant * level ^ 3 <
            finiteStateVorticityStretchingWork (wholeRestartModes radius)
              (complexSharpSupportProjection (wholeRestartModes radius)
                (segmentReceipt.wholePath localTime)) ∧
          peakConstant ^ 5 * (Real.pi * 4 / 3) /
              (32 * lipschitzConstant ^ 3) ≤
            ∫ x in Metric.closedBall (0 : PhysicalSpace)
                (peakConstant / (2 * lipschitzConstant)),
              ‖((level⁻¹) ^ 2 : Real) •
                finiteRealComplexFourierField (wholeRestartModes radius)
                  (complexSharpSupportProjection (wholeRestartModes radius)
                    (segmentReceipt.wholePath localTime))
                  (center + level⁻¹ • x)‖ ^ 2 ∧
          ∃ startTime finishTime : Real,
            startTime ∈ Icc lowerTime upperTime ∧
            finishTime ∈ Icc lowerTime upperTime ∧
            startTime < finishTime ∧
            level ^ 2 * (finishTime - startTime) =
              nu.coeff / (16 * cubicConstant) ∧
            (absoluteTime localTime = startTime ∨
              absoluteTime localTime = finishTime) ∧
            ( ∀ time ∈ Icc startTime finishTime,
              level / 2 ≤
                  wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time) ∧
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time) ≤
                  level) ∧
            (∀ time ∈ Icc startTime finishTime,
              ∃ actualTime :
                  Ico (0 : Real)
                    (wholeRestartVelocityAccumulationTime initial),
                actualTime.1 = time ∧
                wholeRestartBoundedPreAccumulationPhysicalTrajectory
                    initial elapsedBounded actualTime =
                  wholeRestartPrefixPhysicalTrajectory initial length time) ∧
            IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time))
                volume startTime finishTime ∧
            (viscousConstant / 2) *
                (level⁻¹ *
                  ∫ time in startTime..finishTime,
                    wholeStateVorticityGradientMass
                      (wholeRestartPrefixPhysicalTrajectory initial length
                        time)) ≤
              cubicConstant * (nu.coeff / (16 * cubicConstant)) +
                nu.coeff / 2 ∧
            ∀ (observed : Finset IntegerWavevector)
              (_zeroFree : ∀ wave ∈ observed, wave ≠ 0)
              (multiplier : Real)
              (_multiplierNonneg : 0 ≤ multiplier)
              (_multiplierLe : ∀ wave ∈ observed,
                integerWaveViscousMultiplier wave ≤ multiplier)
              (windowStart windowFinish : Real),
              windowStart ∈ Icc startTime finishTime →
              windowFinish ∈ Icc startTime finishTime →
              windowStart < windowFinish →
              level⁻¹ *
                  (∑ wave ∈ observed,
                    complexCoordinateAmplitudeSq
                      (wholeRestartPrefixPhysicalTrajectory initial length
                            windowFinish wave -
                        wholeRestartPrefixPhysicalTrajectory initial length
                            windowStart wave)) ≤
                3 * (level ^ 2 * (windowFinish - windowStart)) *
                  ((level ^ 2)⁻¹ * multiplier) *
                  (cubicConstant *
                      (level ^ 2 * (windowFinish - windowStart)) +
                    nu.coeff / 2)) ∨
        (durationCeiling < normalizedDuration ∧
          ∃ slowStart slowFinish : Real,
            lowerTime < slowStart ∧
            slowFinish = upperTime ∧
            0 ≤ slowStart ∧
            slowStart < slowFinish ∧
            slowFinish ≤ elapsedTime initial length ∧
            level ^ 2 * (slowFinish - slowStart) = durationCeiling ∧
            (∀ time ∈ Icc slowStart slowFinish,
              level / 2 ≤
                  wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time) ∧
                wholeVorticityEuclideanMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time) ≤
                  level) ∧
            (∀ time ∈ Icc slowStart slowFinish,
              ∃ actualTime :
                  Ico (0 : Real)
                    (wholeRestartVelocityAccumulationTime initial),
                actualTime.1 = time ∧
                wholeRestartBoundedPreAccumulationPhysicalTrajectory
                    initial elapsedBounded actualTime =
                  wholeRestartPrefixPhysicalTrajectory initial length time) ∧
            IntervalIntegrable
                (fun time =>
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time))
                volume slowStart slowFinish ∧
            (viscousConstant / 2) *
                (level⁻¹ *
                  ∫ time in slowStart..slowFinish,
                    wholeStateVorticityGradientMass
                      (wholeRestartPrefixPhysicalTrajectory initial length
                        time)) ≤
              cubicConstant * durationCeiling + nu.coeff / 2 ∧
            ∀ (observed : Finset IntegerWavevector)
              (_zeroFree : ∀ wave ∈ observed, wave ≠ 0)
              (multiplier : Real)
              (_multiplierNonneg : 0 ≤ multiplier)
              (_multiplierLe : ∀ wave ∈ observed,
                integerWaveViscousMultiplier wave ≤ multiplier)
              (startTime finishTime : Real),
              startTime ∈ Icc slowStart slowFinish →
              finishTime ∈ Icc slowStart slowFinish →
              startTime < finishTime →
              level⁻¹ *
                  (∑ wave ∈ observed,
                    complexCoordinateAmplitudeSq
                      (wholeRestartPrefixPhysicalTrajectory initial length
                            finishTime wave -
                        wholeRestartPrefixPhysicalTrajectory initial length
                            startTime wave)) ≤
                3 * (level ^ 2 * (finishTime - startTime)) *
                  ((level ^ 2)⁻¹ * multiplier) *
                  (cubicConstant *
                      (level ^ 2 * (finishTime - startTime)) +
                    nu.coeff / 2))) := by
  dsimp only
  let viscousConstant : Real :=
    nu.coeff ^ 2 * (2 * Real.pi) ^ 2
  let cubicConstant : Real :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * viscousConstant)
  let sourceGradientConstant : Real :=
    (2 * cubicConstant) / viscousConstant
  let errorSlope : Real :=
    (128 * 4368 * biotSavartSerrinConstant * cubicConstant) /
      (7 * nu.coeff * viscousConstant)
  let radiusConstant : Real :=
    8 * (sourceGradientConstant +
        errorSlope * durationCeiling / 8 + 1) + 1 / 2
  let peakConstant : Real := 7 / (512 * durationCeiling)
  have levelPos : 0 < level := lt_of_lt_of_le (by norm_num) levelFour
  obtain ⟨length, edge, radius, lowerTime, upperTime, normalizedDuration,
      segmentInitial, segmentTime, segmentTimePos, segmentReceipt,
      absoluteTime, lowerNonneg, lowerLtUpper, upperLeElapsed,
      prehistoryCeiling, normalizedDurationEq, normalizedDurationPos,
      normalizedDurationLower, edgeLt, radiusPos, radiusLower,
      segmentDuration, radiusUpper, pathChart, sourceMassBand, massBand,
      rateLower⟩ :=
    sourceGeneratedNativeAccumulationScaleCriticalActualStretchingRate
      initial elapsedBounded level levelPos initialLeHalf
  refine ⟨length, edge, radius, lowerTime, upperTime, normalizedDuration,
    segmentInitial, segmentTime, segmentTimePos, segmentReceipt, absoluteTime,
    lowerNonneg, lowerLtUpper, upperLeElapsed, prehistoryCeiling,
    normalizedDurationEq, normalizedDurationPos, ?_, edgeLt, radiusPos, ?_,
    segmentDuration, ?_, pathChart, sourceMassBand, massBand, rateLower, ?_⟩
  · simpa only [cubicConstant, viscousConstant] using
      normalizedDurationLower
  · simpa only [sourceGradientConstant, cubicConstant, viscousConstant,
      errorSlope] using radiusLower
  · simpa only [sourceGradientConstant, cubicConstant, viscousConstant,
      errorSlope] using radiusUpper
  · by_cases durationFast : normalizedDuration ≤ durationCeiling
    · left
      refine ⟨durationFast, ?_⟩
      have sourceGradientConstantNonneg :
          0 ≤ sourceGradientConstant := by
        have biotPos : 0 < biotSavartSerrinConstant :=
          biotSavartSerrinConstant_pos
        dsimp only [sourceGradientConstant, cubicConstant, viscousConstant]
        positivity
      have errorSlopeNonneg : 0 ≤ errorSlope := by
        have biotPos : 0 < biotSavartSerrinConstant :=
          biotSavartSerrinConstant_pos
        have viscousConstantPos : 0 < viscousConstant := by
          dsimp only [viscousConstant]
          exact mul_pos (sq_pos_of_pos nu.coeff_pos)
            (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
        have cubicConstantPos : 0 < cubicConstant := by
          dsimp only [cubicConstant]
          exact div_pos
            (mul_pos (mul_pos (by norm_num) (by norm_num))
              (sq_pos_of_pos biotPos))
            (mul_pos (by norm_num) viscousConstantPos)
        dsimp only [errorSlope]
        exact (div_pos
          (mul_pos (mul_pos (mul_pos (by norm_num) (by norm_num)) biotPos)
            cubicConstantPos)
          (mul_pos (mul_pos (by norm_num) nu.coeff_pos)
            viscousConstantPos)).le
      obtain ⟨localTime, center, centerMem, reality, gradientBound,
          stretchingBound, localMass⟩ :=
        receipt_sourceAverage_fast_generates_uniform_localMass
          segmentReceipt radius level normalizedDuration durationCeiling
          sourceGradientConstant errorSlope levelFour normalizedDurationPos
          durationCeilingPos durationFast sourceGradientConstantNonneg
          errorSlopeNonneg
          (by simpa only [sourceGradientConstant, cubicConstant,
            viscousConstant, errorSlope] using radiusUpper)
          (fun time => (massBand time).2) rateLower
      have viscousConstantPos : 0 < viscousConstant := by
        dsimp only [viscousConstant]
        exact mul_pos (sq_pos_of_pos nu.coeff_pos)
          (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
      have cubicConstantPos : 0 < cubicConstant := by
        dsimp only [cubicConstant]
        exact div_pos
          (mul_pos (mul_pos (by norm_num) (by norm_num))
            (sq_pos_of_pos biotSavartSerrinConstant_pos))
          (mul_pos (by norm_num) viscousConstantPos)
      let durationFloor : Real := nu.coeff / (8 * cubicConstant)
      have durationFloorPos : 0 < durationFloor := by
        dsimp only [durationFloor]
        exact div_pos nu.coeff_pos
          (mul_pos (by norm_num) cubicConstantPos)
      have durationFloorLe : durationFloor ≤ normalizedDuration := by
        simpa only [durationFloor] using normalizedDurationLower
      let window : Real := durationFloor / (2 * level ^ 2)
      have levelSqPos : 0 < level ^ 2 := sq_pos_of_pos levelPos
      have windowPos : 0 < window := by
        dsimp only [window]
        positivity
      have spanLower : 2 * window ≤ upperTime - lowerTime := by
        rw [normalizedDurationEq] at durationFloorLe
        calc
          2 * window = durationFloor / level ^ 2 := by
            dsimp only [window]
            field_simp [levelPos.ne']
          _ ≤ upperTime - lowerTime :=
            (div_le_iff₀ levelSqPos).2 (by
              simpa only [mul_comm] using durationFloorLe)
      have oneSided :
          ∃ startTime finishTime : Real,
            startTime ∈ Icc lowerTime upperTime ∧
            finishTime ∈ Icc lowerTime upperTime ∧
            startTime < finishTime ∧
            level ^ 2 * (finishTime - startTime) = durationFloor / 2 ∧
            (absoluteTime localTime = startTime ∨
              absoluteTime localTime = finishTime) := by
        by_cases leftRoom : lowerTime + window ≤ absoluteTime localTime
        · refine ⟨absoluteTime localTime - window, absoluteTime localTime,
            ?_, (pathChart localTime).1, ?_, ?_, Or.inr rfl⟩
          · exact ⟨by linarith, by linarith [(pathChart localTime).1.2]⟩
          · linarith
          · dsimp only [window]
            field_simp [levelPos.ne']
            ring
        · have anchorLt :
              absoluteTime localTime < lowerTime + window :=
            lt_of_not_ge leftRoom
          have forwardRoom :
              absoluteTime localTime + window ≤ upperTime := by
            linarith [(pathChart localTime).1.1, spanLower]
          refine ⟨absoluteTime localTime,
            absoluteTime localTime + window, (pathChart localTime).1,
            ?_, ?_, ?_, Or.inl rfl⟩
          · exact ⟨by linarith [(pathChart localTime).1.1, windowPos],
              forwardRoom⟩
          · linarith
          · dsimp only [window]
            field_simp [levelPos.ne']
            ring
      obtain ⟨startTime, finishTime, startMem, finishMem,
          startLtFinish, durationEq, anchorEndpoint⟩ := oneSided
      have fixedBand :
          ∀ time ∈ Icc startTime finishTime,
            level / 2 ≤
                wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length
                    time) ∧
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length
                    time) ≤
                level := by
        intro time timeMem
        exact sourceMassBand time
          ⟨startMem.1.trans timeMem.1, timeMem.2.trans finishMem.2⟩
      have actualChart :
          ∀ time ∈ Icc startTime finishTime,
            ∃ actualTime :
                Ico (0 : Real)
                  (wholeRestartVelocityAccumulationTime initial),
              actualTime.1 = time ∧
              wholeRestartBoundedPreAccumulationPhysicalTrajectory
                  initial elapsedBounded actualTime =
                wholeRestartPrefixPhysicalTrajectory initial length time := by
        intro time timeMem
        let actualTime :
            Ico (0 : Real)
              (wholeRestartVelocityAccumulationTime initial) :=
          ⟨time,
            ⟨lowerNonneg.trans (startMem.1.trans timeMem.1),
              (timeMem.2.trans finishMem.2 |>.trans upperLeElapsed).trans_lt
                (elapsedTime_lt_wholeRestartVelocityAccumulationTime
                  initial elapsedBounded length)⟩⟩
        refine ⟨actualTime, rfl, ?_⟩
        exact
          wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
            initial elapsedBounded actualTime length
              (timeMem.2.trans finishMem.2 |>.trans upperLeElapsed)
      have startNonneg : 0 ≤ startTime :=
        lowerNonneg.trans startMem.1
      have finishLeElapsed :
          finishTime ≤ elapsedTime initial length :=
        finishMem.2.trans upperLeElapsed
      rcases wholeRestartPrefixScaleCriticalWindowBudget initial length
          levelPos startNonneg startLtFinish finishLeElapsed fixedBand with
        ⟨gradientIntegrable, normalizedGradientLe, fixedModulus⟩
      have fixedGradientLe :
          (viscousConstant / 2) *
              (level⁻¹ *
                ∫ time in startTime..finishTime,
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time)) ≤
            cubicConstant * (nu.coeff / (16 * cubicConstant)) +
              nu.coeff / 2 := by
        rw [durationEq] at normalizedGradientLe
        dsimp only [durationFloor] at normalizedGradientLe
        have halfFloor :
            nu.coeff / (8 * cubicConstant) / 2 =
              nu.coeff / (16 * cubicConstant) := by
          ring
        rw [halfFloor] at normalizedGradientLe
        simpa only [viscousConstant, cubicConstant] using
          normalizedGradientLe
      refine ⟨localTime, center, centerMem, reality, gradientBound,
        stretchingBound, ?_, startTime, finishTime, startMem, finishMem,
        startLtFinish, ?_, anchorEndpoint, fixedBand, actualChart,
        gradientIntegrable, fixedGradientLe, fixedModulus⟩
      · simpa only [radiusConstant, peakConstant,
          sourceGradientConstant, cubicConstant, viscousConstant,
          errorSlope] using localMass
      · rw [durationEq]
        dsimp only [durationFloor, cubicConstant, viscousConstant]
        ring
    · right
      have slow : durationCeiling < normalizedDuration :=
        lt_of_not_ge durationFast
      let slowStart : Real :=
        upperTime - durationCeiling / level ^ 2
      let slowFinish : Real := upperTime
      have levelSqPos : 0 < level ^ 2 := sq_pos_of_pos levelPos
      have windowLtSpan :
          durationCeiling / level ^ 2 < upperTime - lowerTime := by
        apply (div_lt_iff₀ levelSqPos).2
        calc
          durationCeiling < normalizedDuration := slow
          _ = (upperTime - lowerTime) * level ^ 2 := by
            rw [normalizedDurationEq]
            ring
      have lowerLtSlowStart : lowerTime < slowStart := by
        dsimp only [slowStart]
        linarith
      have slowStartNonneg : 0 ≤ slowStart :=
        lowerNonneg.trans lowerLtSlowStart.le
      have slowStartLtFinish : slowStart < slowFinish := by
        dsimp only [slowStart, slowFinish]
        exact sub_lt_self upperTime
          (div_pos durationCeilingPos levelSqPos)
      have slowFinishLeElapsed :
          slowFinish ≤ elapsedTime initial length := by
        simpa only [slowFinish] using upperLeElapsed
      have slowDuration :
          level ^ 2 * (slowFinish - slowStart) = durationCeiling := by
        dsimp only [slowStart, slowFinish]
        field_simp [levelPos.ne']
        ring
      have slowMassBand :
          ∀ time ∈ Icc slowStart slowFinish,
            level / 2 ≤
                wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ∧
              wholeVorticityEuclideanMass
                  (wholeRestartPrefixPhysicalTrajectory initial length time) ≤
                level := by
        intro time timeMem
        exact sourceMassBand time
          ⟨lowerLtSlowStart.le.trans timeMem.1, by
            simpa only [slowFinish] using timeMem.2⟩
      have slowActualChart :
          ∀ time ∈ Icc slowStart slowFinish,
            ∃ actualTime :
                Ico (0 : Real)
                  (wholeRestartVelocityAccumulationTime initial),
              actualTime.1 = time ∧
              wholeRestartBoundedPreAccumulationPhysicalTrajectory
                  initial elapsedBounded actualTime =
                wholeRestartPrefixPhysicalTrajectory initial length time := by
        intro time timeMem
        let actualTime :
            Ico (0 : Real)
              (wholeRestartVelocityAccumulationTime initial) :=
          ⟨time,
            ⟨slowStartNonneg.trans timeMem.1,
              (timeMem.2.trans slowFinishLeElapsed).trans_lt
                (elapsedTime_lt_wholeRestartVelocityAccumulationTime
                  initial elapsedBounded length)⟩⟩
        refine ⟨actualTime, rfl, ?_⟩
        exact
          wholeRestartBoundedPreAccumulationPhysicalTrajectory_eq_prefix
            initial elapsedBounded actualTime length
              (timeMem.2.trans slowFinishLeElapsed)
      rcases wholeRestartPrefixScaleCriticalWindowBudget initial length
          levelPos slowStartNonneg slowStartLtFinish slowFinishLeElapsed
          slowMassBand with
        ⟨gradientIntegrable, rawGradientLe, rawModulus⟩
      have normalizedGradientLe :
          (viscousConstant / 2) *
              (level⁻¹ *
                ∫ time in slowStart..slowFinish,
                  wholeStateVorticityGradientMass
                    (wholeRestartPrefixPhysicalTrajectory initial length
                      time)) ≤
            cubicConstant * durationCeiling + nu.coeff / 2 := by
        rw [slowDuration] at rawGradientLe
        simpa only [viscousConstant, cubicConstant] using rawGradientLe
      have slowModulus := by
        simpa only [cubicConstant, viscousConstant] using rawModulus
      exact ⟨slow, slowStart, slowFinish, lowerLtSlowStart, rfl,
        slowStartNonneg, slowStartLtFinish, slowFinishLeElapsed,
        slowDuration, slowMassBand, slowActualChart, gradientIntegrable,
        normalizedGradientLe, slowModulus⟩

/-!
## Source-indexed finite-band compactness at the accumulation time

The following private Fourier/Arzelà kernel is consumed immediately by the
source theorem at the end of this section.  It keeps the actual prefix chart,
the physical recentering, and the normalized time orientation in one lineage.
-/

abbrev ScaledPhysicalCylinder
    (timeLength spatialRadius : Real) :=
  Icc (0 : Real) timeLength ×
    Metric.closedBall (0 : PhysicalSpace) spatialRadius

private theorem wholeRestartModes_scaled_card_le
    (scale bandRadius : Real)
    (radius : Nat)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (_bandRadiusNonneg : 0 ≤ bandRadius)
    (radiusLe : scale * (radius : Real) ≤ bandRadius) :
    scale ^ 3 * ((wholeRestartModes radius).card : Real) ≤
      (2 * bandRadius + 1) ^ 3 := by
  have cardLe := wholeRestartModes_card_cast_le_radius_cube radius
  have scaleNonneg : 0 ≤ scale := scalePos.le
  have radiusNonneg : 0 ≤ (radius : Real) := by positivity
  calc
    scale ^ 3 * ((wholeRestartModes radius).card : Real) ≤
        scale ^ 3 * (2 * (radius : Real) + 1) ^ 3 := by
      gcongr
    _ = (scale * (2 * (radius : Real) + 1)) ^ 3 := by ring
    _ ≤ (2 * bandRadius + 1) ^ 3 := by
      gcongr
      nlinarith

private theorem finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
    (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector)
    (x : PhysicalSpace) :
    ‖finiteRealComplexFourierField modes coefficient x‖ ^ 2 ≤
      (modes.card : Real) *
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (coefficient wave) := by
  calc
    ‖finiteRealComplexFourierField modes coefficient x‖ ^ 2 ≤
        finiteVelocityFourierMajorant modes coefficient ^ 2 :=
      finiteRealComplexFourierField_norm_sq_le_velocityMajorant_sq
        modes coefficient x
    _ ≤
        (modes.card : Real) *
          ∑ wave ∈ modes,
            (Real.sqrt
              (complexCoordinateAmplitudeSq (coefficient wave))) ^ 2 := by
      unfold finiteVelocityFourierMajorant
      exact sq_sum_le_card_mul_sum_sq
    _ =
        (modes.card : Real) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (coefficient wave) := by
      congr 1
      apply Finset.sum_congr rfl
      intro wave _
      rw [Real.sq_sqrt (complexCoordinateAmplitudeSq_nonneg _)]

private theorem finiteRealComplexFourierField_sub
    (modes : Finset IntegerWavevector)
    (left right : IntegerWavevector → ComplexCoordinateVector)
    (x : PhysicalSpace) :
    finiteRealComplexFourierField modes left x -
        finiteRealComplexFourierField modes right x =
      finiteRealComplexFourierField modes (fun wave => left wave - right wave)
        x := by
  unfold finiteRealComplexFourierField
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  ext coordinate
  simp [realComplexFourierMode, coefficientReal, coefficientImag]
  ring

theorem integerWaveNormSq_le_three_mul_radius_sq_of_mem
    (radius : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ wholeRestartModes radius) :
    integerWaveNormSq wave ≤ 3 * (radius : Real) ^ 2 := by
  have cubeMem : wave ∈ integerWaveFrequencyCube radius :=
    (Finset.mem_erase.mp waveMem).2
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at cubeMem
  have h0 := cubeMem (0 : Fin 3)
  have h1 := cubeMem (1 : Fin 3)
  have h2 := cubeMem (2 : Fin 3)
  rw [Finset.mem_Icc] at h0 h1 h2
  have h0r :
      -((radius : Nat) : Real) ≤ (wave (0 : Fin 3) : Real) ∧
        (wave (0 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h0
  have h1r :
      -((radius : Nat) : Real) ≤ (wave (1 : Fin 3) : Real) ∧
        (wave (1 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h1
  have h2r :
      -((radius : Nat) : Real) ≤ (wave (2 : Fin 3) : Real) ∧
        (wave (2 : Fin 3) : Real) ≤ radius := by
    exact_mod_cast h2
  have h0sq : (wave (0 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h1sq : (wave (1 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  have h2sq : (wave (2 : Fin 3) : Real) ^ 2 ≤ (radius : Real) ^ 2 := by
    nlinarith
  rw [integerWaveNormSq]
  norm_num [Fin.sum_univ_succ]
  linarith

private theorem finiteBandGradientMass_le_radiusSq_mul_mass
    (radius : Nat)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityEnstrophyMass (wholeRestartModes radius) state ≤
      3 * (radius : Real) ^ 2 *
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) state := by
  unfold finiteStateVorticityEnstrophyMass
    finiteStateVorticityCoefficientEnstrophy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro wave waveMem
  exact mul_le_mul_of_nonneg_right
    (integerWaveNormSq_le_three_mul_radius_sq_of_mem radius wave waveMem)
    (complexCoordinateAmplitudeSq_nonneg _)

def scaledFiniteBandField
    (timeLength spatialRadius scale : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (point : ScaledPhysicalCylinder timeLength spatialRadius) :
    PhysicalSpace :=
  (scale ^ 2 : Real) •
    finiteRealComplexFourierField (wholeRestartModes radius)
      (path point.1) (center + scale • point.2.1)

theorem scaledFiniteBandField_norm_sq_le
    (timeLength spatialRadius scale bandRadius massCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (point : ScaledPhysicalCylinder timeLength spatialRadius)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (_massCeilingNonneg : 0 ≤ massCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe :
      scale * wholeVorticityEuclideanMass (path point.1) ≤ massCeiling) :
    ‖scaledFiniteBandField timeLength spatialRadius scale radius center path
        point‖ ^ 2 ≤
      (2 * bandRadius + 1) ^ 3 * massCeiling := by
  let modes := wholeRestartModes radius
  have scaleNonneg : 0 ≤ scale := scalePos.le
  have finiteMassLe :
      finiteStateVorticityCoefficientEnstrophy modes (path point.1) ≤
        wholeVorticityEuclideanMass (path point.1) :=
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes (path point.1)
  have fieldBound :=
    finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
      modes (path point.1) (center + scale • point.2.1)
  have scaledCard :=
    wholeRestartModes_scaled_card_le scale bandRadius radius scalePos
      scaleLeOne bandRadiusNonneg radiusLe
  calc
    ‖scaledFiniteBandField timeLength spatialRadius scale radius center path
        point‖ ^ 2 =
        scale ^ 4 *
          ‖finiteRealComplexFourierField modes (path point.1)
            (center + scale • point.2.1)‖ ^ 2 := by
      rw [scaledFiniteBandField, norm_smul,
        Real.norm_of_nonneg (sq_nonneg scale)]
      ring
    _ ≤ scale ^ 4 *
        ((modes.card : Real) *
          finiteStateVorticityCoefficientEnstrophy modes (path point.1)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [finiteStateVorticityCoefficientEnstrophy] using
          fieldBound)
        (by positivity)
    _ ≤ scale ^ 4 *
        ((modes.card : Real) *
          wholeVorticityEuclideanMass (path point.1)) := by
      gcongr
    _ =
        (scale ^ 3 * (modes.card : Real)) *
          (scale * wholeVorticityEuclideanMass (path point.1)) := by ring
    _ ≤ (2 * bandRadius + 1) ^ 3 * massCeiling := by
      exact mul_le_mul scaledCard massLe
        (mul_nonneg scaleNonneg
          (by
            unfold wholeVorticityEuclideanMass
            exact tsum_nonneg fun _ => sq_nonneg _))
        (by positivity)

private theorem scaledFiniteBandField_time_dist_sq_le
    (timeLength spatialRadius scale bandRadius timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (position : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (first second : Icc (0 : Real) timeLength)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (_timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (timeIncrement :
      scale *
          (∑ wave ∈ wholeRestartModes radius,
            complexCoordinateAmplitudeSq
              (path first wave - path second wave)) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (first, position))
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (second, position)) ^ 2 ≤
      (2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second := by
  let modes := wholeRestartModes radius
  let difference : IntegerWavevector → ComplexCoordinateVector :=
    fun wave => path first wave - path second wave
  have scaleNonneg : 0 ≤ scale := scalePos.le
  have fieldBound :=
    finiteRealComplexFourierField_norm_sq_le_card_mul_amplitude
      modes difference (center + scale • position.1)
  have scaledCard :=
    wholeRestartModes_scaled_card_le scale bandRadius radius scalePos
      scaleLeOne bandRadiusNonneg radiusLe
  rw [dist_eq_norm]
  calc
    ‖scaledFiniteBandField timeLength spatialRadius scale radius center path
          (first, position) -
        scaledFiniteBandField timeLength spatialRadius scale radius center path
          (second, position)‖ ^ 2 =
        scale ^ 4 *
          ‖finiteRealComplexFourierField modes difference
            (center + scale • position.1)‖ ^ 2 := by
      rw [scaledFiniteBandField, scaledFiniteBandField, ← smul_sub,
        finiteRealComplexFourierField_sub]
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg scale)]
      ring
    _ ≤ scale ^ 4 *
        ((modes.card : Real) *
          ∑ wave ∈ modes,
            complexCoordinateAmplitudeSq (difference wave)) := by
      gcongr
    _ =
        (scale ^ 3 * (modes.card : Real)) *
          (scale *
            ∑ wave ∈ modes,
              complexCoordinateAmplitudeSq (difference wave)) := by ring
    _ ≤ (2 * bandRadius + 1) ^ 3 *
        (timeCeiling * dist first second) := by
      exact mul_le_mul scaledCard timeIncrement
        (mul_nonneg scaleNonneg
          (Finset.sum_nonneg fun wave _ =>
            complexCoordinateAmplitudeSq_nonneg (difference wave)))
        (by positivity)
    _ = (2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second := by
      ring

private theorem scaledFiniteBandField_space_dist_le
    (timeLength spatialRadius scale bandRadius massCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (time : Icc (0 : Real) timeLength)
    (first second : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe :
      scale * wholeVorticityEuclideanMass (path time) ≤ massCeiling) :
    dist
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (time, first))
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (time, second)) ≤
      Real.sqrt
          (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
            bandRadius ^ 2 * massCeiling) *
        dist first second := by
  let modes := wholeRestartModes radius
  have scaleNonneg : 0 ≤ scale := scalePos.le
  have radiusNonneg : 0 ≤ (radius : Real) := by positivity
  have finiteMassLe :
      finiteStateVorticityCoefficientEnstrophy modes (path time) ≤
        wholeVorticityEuclideanMass (path time) :=
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes (path time)
  have gradientLeFinite :=
    finiteBandGradientMass_le_radiusSq_mul_mass radius (path time)
  have gradientLeWhole :
      finiteStateVorticityEnstrophyMass modes (path time) ≤
        3 * (radius : Real) ^ 2 *
          wholeVorticityEuclideanMass (path time) :=
    gradientLeFinite.trans
      (mul_le_mul_of_nonneg_left finiteMassLe (by positivity))
  have scaledCard :=
    wholeRestartModes_scaled_card_le scale bandRadius radius scalePos
      scaleLeOne bandRadiusNonneg radiusLe
  have scaledRadiusSq :
      scale ^ 2 * (radius : Real) ^ 2 ≤ bandRadius ^ 2 := by
    have squared :=
      mul_self_le_mul_self
        (mul_nonneg scaleNonneg radiusNonneg) radiusLe
    nlinarith
  have scaledArgument :
      scale ^ 6 * ((modes.card : Real) * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (path time)) ≤
        3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          bandRadius ^ 2 * massCeiling := by
    calc
      scale ^ 6 * ((modes.card : Real) * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (path time)) ≤
          scale ^ 6 * ((modes.card : Real) * (2 * Real.pi) ^ 2 *
            (3 * (radius : Real) ^ 2 *
              wholeVorticityEuclideanMass (path time))) := by
        gcongr
      _ = 3 * (scale ^ 3 * (modes.card : Real)) *
          (2 * Real.pi) ^ 2 *
          (scale ^ 2 * (radius : Real) ^ 2) *
          (scale * wholeVorticityEuclideanMass (path time)) := by ring
      _ ≤ 3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          bandRadius ^ 2 * massCeiling := by
        have scaledMassNonneg :
            0 ≤ scale * wholeVorticityEuclideanMass (path time) := by
          exact mul_nonneg scaleNonneg (by
            unfold wholeVorticityEuclideanMass
            exact tsum_nonneg fun _ => sq_nonneg _)
        gcongr
  have argumentNonneg :
      0 ≤ (modes.card : Real) * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes (path time) := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (sq_nonneg _))
      (finiteStateVorticityEnstrophyMass_nonneg modes (path time))
  have ceilingNonneg :
      0 ≤ 3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        bandRadius ^ 2 * massCeiling := by
    have : 0 ≤ 2 * bandRadius + 1 := by linarith
    positivity
  have coefficientLe :
      scale ^ 3 *
          Real.sqrt
            ((modes.card : Real) * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes (path time)) ≤
        Real.sqrt
          (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
            bandRadius ^ 2 * massCeiling) := by
    rw [← sq_le_sq₀ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)]
    rw [mul_pow, Real.sq_sqrt argumentNonneg,
      Real.sq_sqrt ceilingNonneg]
    rw [show (scale ^ 3) ^ 2 = scale ^ 6 by ring]
    exact scaledArgument
  have spatial :=
    finiteRealComplexFourierField_parabolicScale_norm_sub_le
      modes (path time) scale scaleNonneg center second.1 first.1
  simpa only [scaledFiniteBandField, Subtype.dist_eq, dist_eq_norm] using
    spatial.trans
      (mul_le_mul_of_nonneg_right coefficientLe (norm_nonneg _))

private theorem scaledFiniteBandField_time_dist_le
    (timeLength spatialRadius scale bandRadius timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (position : Metric.closedBall (0 : PhysicalSpace) spatialRadius)
    (first second : Icc (0 : Real) timeLength)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (timeIncrement :
      scale *
          (∑ wave ∈ wholeRestartModes radius,
            complexCoordinateAmplitudeSq
              (path first wave - path second wave)) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (first, position))
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          (second, position)) ≤
      Real.sqrt
        ((2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second) := by
  have squared :=
    scaledFiniteBandField_time_dist_sq_le timeLength spatialRadius scale
      bandRadius timeCeiling radius center path position first second scalePos
      scaleLeOne bandRadiusNonneg timeCeilingNonneg radiusLe timeIncrement
  have baseNonneg : 0 ≤ 2 * bandRadius + 1 := by linarith
  have argumentNonneg :
      0 ≤ (2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second := by
    positivity
  rw [← sq_le_sq₀ dist_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sq_sqrt argumentNonneg]
  exact squared

private theorem scaledFiniteBandField_joint_dist_le
    (timeLength spatialRadius scale bandRadius massCeiling timeCeiling : Real)
    (radius : Nat)
    (center : PhysicalSpace)
    (path : Icc (0 : Real) timeLength → ComplexVorticityHilbertState)
    (first second : ScaledPhysicalCylinder timeLength spatialRadius)
    (scalePos : 0 < scale)
    (scaleLeOne : scale ≤ 1)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (radiusLe : scale * (radius : Real) ≤ bandRadius)
    (massLe : ∀ time,
      scale * wholeVorticityEuclideanMass (path time) ≤ massCeiling)
    (timeIncrement : ∀ first second,
      scale *
          (∑ wave ∈ wholeRestartModes radius,
            complexCoordinateAmplitudeSq
              (path first wave - path second wave)) ≤
        timeCeiling * dist first second) :
    dist
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          first)
        (scaledFiniteBandField timeLength spatialRadius scale radius center path
          second) ≤
      Real.sqrt
          (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
            bandRadius ^ 2 * massCeiling) * dist first second +
        Real.sqrt
          ((2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second) := by
  let middle : ScaledPhysicalCylinder timeLength spatialRadius :=
    (first.1, second.2)
  have spatial :=
    scaledFiniteBandField_space_dist_le timeLength spatialRadius scale
      bandRadius massCeiling radius center path first.1 first.2 second.2
      scalePos scaleLeOne bandRadiusNonneg massCeilingNonneg radiusLe
      (massLe first.1)
  have temporal :=
    scaledFiniteBandField_time_dist_le timeLength spatialRadius scale
      bandRadius timeCeiling radius center path second.2 first.1 second.1
      scalePos scaleLeOne bandRadiusNonneg timeCeilingNonneg radiusLe
      (timeIncrement first.1 second.1)
  have firstComponentLe : dist first.1 second.1 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have secondComponentLe : dist first.2 second.2 ≤ dist first second := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have spatialConstantNonneg :
      0 ≤ Real.sqrt
        (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          bandRadius ^ 2 * massCeiling) := Real.sqrt_nonneg _
  have spatial' :
      dist
          (scaledFiniteBandField timeLength spatialRadius scale radius center
            path first)
          (scaledFiniteBandField timeLength spatialRadius scale radius center
            path middle) ≤
        Real.sqrt
            (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
              bandRadius ^ 2 * massCeiling) * dist first second := by
    calc
      _ ≤ Real.sqrt
            (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
              bandRadius ^ 2 * massCeiling) * dist first.2 second.2 :=
        spatial
      _ ≤ _ := mul_le_mul_of_nonneg_left secondComponentLe
        spatialConstantNonneg
  have timeCoefficientNonneg :
      0 ≤ (2 * bandRadius + 1) ^ 3 * timeCeiling := by
    have : 0 ≤ 2 * bandRadius + 1 := by linarith
    positivity
  have temporal' :
      dist
          (scaledFiniteBandField timeLength spatialRadius scale radius center
            path middle)
          (scaledFiniteBandField timeLength spatialRadius scale radius center
            path second) ≤
        Real.sqrt
          ((2 * bandRadius + 1) ^ 3 * timeCeiling * dist first second) := by
    calc
      _ ≤ Real.sqrt
          ((2 * bandRadius + 1) ^ 3 * timeCeiling * dist first.1 second.1) :=
        temporal
      _ ≤ _ := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left firstComponentLe timeCoefficientNonneg)
  exact (dist_triangle _
      (scaledFiniteBandField timeLength spatialRadius scale radius center path
        middle) _).trans
    (add_le_add spatial' temporal')

private theorem scaledFiniteBandField_family_equicontinuous
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * wholeVorticityEuclideanMass (path index time) ≤
        massCeiling)
    (timeIncrement : ∀ index first second,
      scale index *
          (∑ wave ∈ wholeRestartModes (radius index),
            complexCoordinateAmplitudeSq
              (path index first wave - path index second wave)) ≤
        timeCeiling * dist first second) :
    Equicontinuous fun index point =>
      scaledFiniteBandField timeLength spatialRadius (scale index)
        (radius index) (center index) (path index) point := by
  let spatialConstant : Real :=
    Real.sqrt
      (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
        bandRadius ^ 2 * massCeiling)
  let timeCoefficient : Real :=
    (2 * bandRadius + 1) ^ 3 * timeCeiling
  let modulus : Real → Real := fun distance =>
    spatialConstant * |distance| +
      Real.sqrt (timeCoefficient * |distance|)
  have modulusContinuous : Continuous modulus := by
    exact (continuous_const.mul continuous_abs).add
      (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
  have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
    have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
    have modulusZero : modulus 0 = 0 := by simp [modulus]
    nth_rewrite 2 [← modulusZero]
    exact atZero
  apply Metric.equicontinuous_of_continuity_modulus modulus
    modulusTendsToZero
  intro first second index
  simpa only [modulus, spatialConstant, timeCoefficient,
    abs_of_nonneg dist_nonneg] using
    scaledFiniteBandField_joint_dist_le timeLength spatialRadius
      (scale index) bandRadius massCeiling timeCeiling (radius index)
      (center index) (path index) first second (scalePos index)
      (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
      timeCeilingNonneg (radiusLe index) (massLe index)
      (timeIncrement index)

def scaledFiniteBandBoundedPath
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * wholeVorticityEuclideanMass (path index time) ≤
        massCeiling)
    (timeIncrement : ∀ index first second,
      scale index *
          (∑ wave ∈ wholeRestartModes (radius index),
            complexCoordinateAmplitudeSq
              (path index first wave - path index second wave)) ≤
        timeCeiling * dist first second)
    (index : Nat) :
    BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace :=
  BoundedContinuousFunction.mkOfCompact
    ⟨scaledFiniteBandField timeLength spatialRadius (scale index)
        (radius index) (center index) (path index),
      (scaledFiniteBandField_family_equicontinuous timeLength spatialRadius
        bandRadius massCeiling timeCeiling scale radius center path
        bandRadiusNonneg massCeilingNonneg timeCeilingNonneg scalePos
        scaleLeOne radiusLe massLe timeIncrement).continuous index⟩

theorem scaledFiniteBandBoundedPath_apply
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * wholeVorticityEuclideanMass (path index time) ≤
        massCeiling)
    (timeIncrement : ∀ index first second,
      scale index *
          (∑ wave ∈ wholeRestartModes (radius index),
            complexCoordinateAmplitudeSq
              (path index first wave - path index second wave)) ≤
        timeCeiling * dist first second)
    (index : Nat)
    (point : ScaledPhysicalCylinder timeLength spatialRadius) :
    scaledFiniteBandBoundedPath timeLength spatialRadius bandRadius
        massCeiling timeCeiling scale radius center path bandRadiusNonneg
        massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe
        massLe timeIncrement index point =
      scaledFiniteBandField timeLength spatialRadius (scale index)
        (radius index) (center index) (path index) point := rfl

theorem scaledFiniteBandBoundedPath_compactRange
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * wholeVorticityEuclideanMass (path index time) ≤
        massCeiling)
    (timeIncrement : ∀ index first second,
      scale index *
          (∑ wave ∈ wholeRestartModes (radius index),
            complexCoordinateAmplitudeSq
              (path index first wave - path index second wave)) ≤
        timeCeiling * dist first second) :
    ∃ compactSet : Set (BoundedContinuousFunction
        (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace),
      IsCompact compactSet ∧
      ∀ index,
        scaledFiniteBandBoundedPath timeLength spatialRadius bandRadius
            massCeiling timeCeiling scale radius center path bandRadiusNonneg
            massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe
            massLe timeIncrement index ∈ compactSet := by
  let sequence : Nat → BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace :=
    scaledFiniteBandBoundedPath timeLength spatialRadius bandRadius
      massCeiling timeCeiling scale radius center path bandRadiusNonneg
      massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe massLe
      timeIncrement
  let family : Set (BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace) :=
    Set.range sequence
  let valueBall : Set PhysicalSpace :=
    Metric.closedBall 0
      (Real.sqrt ((2 * bandRadius + 1) ^ 3 * massCeiling))
  have baseNonneg : 0 ≤ 2 * bandRadius + 1 := by linarith
  have valueCeilingNonneg :
      0 ≤ (2 * bandRadius + 1) ^ 3 * massCeiling := by positivity
  have familyEquicontinuous :
      Equicontinuous
        (fun member : family =>
          (member.1 :
            ScaledPhysicalCylinder timeLength spatialRadius →
              PhysicalSpace)) := by
    let spatialConstant : Real :=
      Real.sqrt
        (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          bandRadius ^ 2 * massCeiling)
    let timeCoefficient : Real :=
      (2 * bandRadius + 1) ^ 3 * timeCeiling
    let modulus : Real → Real := fun distance =>
      spatialConstant * |distance| +
        Real.sqrt (timeCoefficient * |distance|)
    have modulusContinuous : Continuous modulus := by
      exact (continuous_const.mul continuous_abs).add
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
    have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
      have modulusZero : modulus 0 = 0 := by simp [modulus]
      nth_rewrite 2 [← modulusZero]
      exact atZero
    apply Metric.equicontinuous_of_continuity_modulus modulus
      modulusTendsToZero
    intro first second member
    rcases member with ⟨function, ⟨index, functionEq⟩⟩
    subst function
    change dist
        (scaledFiniteBandField timeLength spatialRadius (scale index)
          (radius index) (center index) (path index) first)
        (scaledFiniteBandField timeLength spatialRadius (scale index)
          (radius index) (center index) (path index) second) ≤
      modulus (dist first second)
    simpa only [modulus, spatialConstant, timeCoefficient,
      abs_of_nonneg dist_nonneg] using
      scaledFiniteBandField_joint_dist_le timeLength spatialRadius
        (scale index) bandRadius massCeiling timeCeiling (radius index)
        (center index) (path index) first second (scalePos index)
        (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
        timeCeilingNonneg (radiusLe index) (massLe index)
        (timeIncrement index)
  have compactFamily : IsCompact (closure family) := by
    apply BoundedContinuousFunction.arzela_ascoli valueBall
      (isCompact_closedBall _ _)
    · intro function point functionMem
      rcases functionMem with ⟨index, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt valueCeilingNonneg]
      exact scaledFiniteBandField_norm_sq_le timeLength spatialRadius
        (scale index) bandRadius massCeiling (radius index) (center index)
        (path index) point (scalePos index) (scaleLeOne index)
        bandRadiusNonneg massCeilingNonneg (radiusLe index)
        (massLe index point.1)
    · exact familyEquicontinuous
  refine ⟨closure family, compactFamily, ?_⟩
  intro index
  apply subset_closure
  exact ⟨index, rfl⟩

theorem scaledFiniteBandBoundedPath_tendsto_subseq
    (timeLength spatialRadius bandRadius massCeiling timeCeiling : Real)
    (scale : Nat → Real)
    (radius : Nat → Nat)
    (center : Nat → PhysicalSpace)
    (path : Nat → Icc (0 : Real) timeLength →
      ComplexVorticityHilbertState)
    (bandRadiusNonneg : 0 ≤ bandRadius)
    (massCeilingNonneg : 0 ≤ massCeiling)
    (timeCeilingNonneg : 0 ≤ timeCeiling)
    (scalePos : ∀ index, 0 < scale index)
    (scaleLeOne : ∀ index, scale index ≤ 1)
    (radiusLe : ∀ index,
      scale index * (radius index : Real) ≤ bandRadius)
    (massLe : ∀ index time,
      scale index * wholeVorticityEuclideanMass (path index time) ≤
        massCeiling)
    (timeIncrement : ∀ index first second,
      scale index *
          (∑ wave ∈ wholeRestartModes (radius index),
            complexCoordinateAmplitudeSq
              (path index first wave - path index second wave)) ≤
        timeCeiling * dist first second) :
    ∃ limit : BoundedContinuousFunction
        (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace,
    ∃ subsequence : Nat → Nat,
      StrictMono subsequence ∧
      Tendsto
        (fun index =>
          scaledFiniteBandBoundedPath timeLength spatialRadius bandRadius
            massCeiling timeCeiling scale radius center path bandRadiusNonneg
            massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe
            massLe timeIncrement (subsequence index))
        atTop (𝓝 limit) := by
  let sequence : Nat → BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace :=
    scaledFiniteBandBoundedPath timeLength spatialRadius bandRadius
      massCeiling timeCeiling scale radius center path bandRadiusNonneg
      massCeilingNonneg timeCeilingNonneg scalePos scaleLeOne radiusLe massLe
      timeIncrement
  let family : Set (BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace) :=
    Set.range sequence
  let valueBall : Set PhysicalSpace :=
    Metric.closedBall 0
      (Real.sqrt ((2 * bandRadius + 1) ^ 3 * massCeiling))
  have baseNonneg : 0 ≤ 2 * bandRadius + 1 := by linarith
  have valueCeilingNonneg :
      0 ≤ (2 * bandRadius + 1) ^ 3 * massCeiling := by positivity
  have familyEquicontinuous :
      Equicontinuous
        (fun member : family =>
          (member.1 :
            ScaledPhysicalCylinder timeLength spatialRadius →
              PhysicalSpace)) := by
    let spatialConstant : Real :=
      Real.sqrt
        (3 * (2 * bandRadius + 1) ^ 3 * (2 * Real.pi) ^ 2 *
          bandRadius ^ 2 * massCeiling)
    let timeCoefficient : Real :=
      (2 * bandRadius + 1) ^ 3 * timeCeiling
    let modulus : Real → Real := fun distance =>
      spatialConstant * |distance| +
        Real.sqrt (timeCoefficient * |distance|)
    have modulusContinuous : Continuous modulus := by
      exact (continuous_const.mul continuous_abs).add
        (Real.continuous_sqrt.comp (continuous_const.mul continuous_abs))
    have modulusTendsToZero : Tendsto modulus (𝓝 0) (𝓝 0) := by
      have atZero : ContinuousAt modulus 0 := modulusContinuous.continuousAt
      have modulusZero : modulus 0 = 0 := by simp [modulus]
      nth_rewrite 2 [← modulusZero]
      exact atZero
    apply Metric.equicontinuous_of_continuity_modulus modulus
      modulusTendsToZero
    intro first second member
    rcases member with ⟨function, ⟨index, functionEq⟩⟩
    subst function
    change dist
        (scaledFiniteBandField timeLength spatialRadius (scale index)
          (radius index) (center index) (path index) first)
        (scaledFiniteBandField timeLength spatialRadius (scale index)
          (radius index) (center index) (path index) second) ≤
      modulus (dist first second)
    simpa only [modulus, spatialConstant, timeCoefficient,
      abs_of_nonneg dist_nonneg] using
      scaledFiniteBandField_joint_dist_le timeLength spatialRadius
        (scale index) bandRadius massCeiling timeCeiling (radius index)
        (center index) (path index) first second (scalePos index)
        (scaleLeOne index) bandRadiusNonneg massCeilingNonneg
        timeCeilingNonneg (radiusLe index) (massLe index)
        (timeIncrement index)
  have compactFamily : IsCompact (closure family) := by
    apply BoundedContinuousFunction.arzela_ascoli valueBall
      (isCompact_closedBall _ _)
    · intro function point functionMem
      rcases functionMem with ⟨index, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)]
      rw [Real.sq_sqrt valueCeilingNonneg]
      exact scaledFiniteBandField_norm_sq_le timeLength spatialRadius
        (scale index) bandRadius massCeiling (radius index) (center index)
        (path index) point (scalePos index) (scaleLeOne index)
        bandRadiusNonneg massCeilingNonneg (radiusLe index)
        (massLe index point.1)
    · exact familyEquicontinuous
  have sequenceMem (index : Nat) : sequence index ∈ closure family := by
    apply subset_closure
    exact ⟨index, rfl⟩
  obtain ⟨limit, _limitMem, subsequence, subsequenceMono,
      subsequenceTendsto⟩ := compactFamily.tendsto_subseq sequenceMem
  exact ⟨limit, subsequence, subsequenceMono, by
    simpa only [sequence, Function.comp_def] using subsequenceTendsto⟩

private theorem boundedContinuousFunction_toLp_sub_norm_sq_eq_integral
    {X E : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (left right : BoundedContinuousFunction X E) :
    ‖BoundedContinuousFunction.toLp 2 μ Real left -
        BoundedContinuousFunction.toLp 2 μ Real right‖ ^ 2 =
      ∫ point, ‖left point - right point‖ ^ 2 ∂μ := by
  let difference : ↥(Lp E 2 μ) :=
    BoundedContinuousFunction.toLp 2 μ Real left -
      BoundedContinuousFunction.toLp 2 μ Real right
  have differenceAE :
      ∀ᵐ point ∂μ, difference point = left point - right point := by
    have subAE := Lp.coeFn_sub
      (BoundedContinuousFunction.toLp 2 μ Real left)
      (BoundedContinuousFunction.toLp 2 μ Real right)
    have leftAE := BoundedContinuousFunction.coeFn_toLp 2 μ Real left
    have rightAE := BoundedContinuousFunction.coeFn_toLp 2 μ Real right
    filter_upwards [subAE, leftAE, rightAE] with point subEq leftEq rightEq
    dsimp only [difference]
    rw [subEq]
    simp only [Pi.sub_apply]
    rw [leftEq, rightEq]
  change ‖difference‖ ^ 2 = _
  rw [Lp.norm_def]
  rw [toReal_eLpNorm (Lp.aestronglyMeasurable difference)]
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (p := (2 : ℝ≥0∞)) (by norm_num) (by simp)
    (Lp.aestronglyMeasurable difference)]
  norm_num
  have integralEq :
      (∫ point, ‖difference point‖ ^ 2 ∂μ) =
        ∫ point, ‖left point - right point‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [differenceAE] with point pointEq
    rw [pointEq]
  rw [integralEq]
  have powerIdentity :
      ((∫ point, ‖left point - right point‖ ^ 2 ∂μ) ^
          ((2 : Real)⁻¹)) ^ 2 =
        ∫ point, ‖left point - right point‖ ^ 2 ∂μ :=
    Real.rpow_inv_natCast_pow (n := 2)
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)
  simpa only [one_div] using powerIdentity

theorem
    boundedContinuousFunction_toLp_tendsto_subseq_of_compact_approximation
    {X E : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (value : Nat → BoundedContinuousFunction X E)
    (approximation : Nat → Nat → BoundedContinuousFunction X E)
    (error : Nat → Real)
    (errorTendsto : Tendsto error atTop (nhds 0))
    (uniformClose : ∀ cutoff index,
      ‖BoundedContinuousFunction.toLp 2 μ Real (value index) -
        BoundedContinuousFunction.toLp 2 μ Real
          (approximation cutoff index)‖ ≤ error cutoff)
    (compactApproximation : ∀ cutoff,
      ∃ compactSet : Set (BoundedContinuousFunction X E),
        IsCompact compactSet ∧
        ∀ index, approximation cutoff index ∈ compactSet) :
    ∃ limit : ↥(Lp E 2 μ), ∃ subsequence : Nat → Nat,
      StrictMono subsequence ∧
      Tendsto
        (fun index =>
          BoundedContinuousFunction.toLp 2 μ Real
            (value (subsequence index)))
        atTop (nhds limit) := by
  let toLpMap :
      BoundedContinuousFunction X E →L[Real] ↥(Lp E 2 μ) :=
    BoundedContinuousFunction.toLp 2 μ Real
  let lpValue : Nat → ↥(Lp E 2 μ) := fun index =>
    toLpMap (value index)
  let lpApproximation : Nat → Nat → ↥(Lp E 2 μ) :=
    fun cutoff index => toLpMap (approximation cutoff index)
  have compactLpApproximation (cutoff : Nat) :
      ∃ compactSet : Set (↥(Lp E 2 μ)),
        IsCompact compactSet ∧
        ∀ index, lpApproximation cutoff index ∈ compactSet := by
    obtain ⟨compactSet, compactSetCompact, approximationMem⟩ :=
      compactApproximation cutoff
    refine ⟨toLpMap '' compactSet,
      compactSetCompact.image toLpMap.continuous, ?_⟩
    intro index
    exact ⟨approximation cutoff index, approximationMem index, rfl⟩
  have familyTotallyBounded : TotallyBounded (Set.range lpValue) := by
    rw [Metric.totallyBounded_iff]
    intro epsilon epsilonPos
    have halfPos : 0 < epsilon / 2 := by linarith
    have eventuallyError : ∀ᶠ cutoff : Nat in atTop,
        error cutoff < epsilon / 2 :=
      errorTendsto.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨cutoff, errorSmall⟩ := eventuallyError.exists
    obtain ⟨compactSet, compactSetCompact, approximationMem⟩ :=
      compactLpApproximation cutoff
    obtain ⟨centers, centersFinite, centersCover⟩ :=
      (Metric.totallyBounded_iff.mp compactSetCompact.totallyBounded)
        (epsilon / 2) halfPos
    refine ⟨centers, centersFinite, ?_⟩
    intro member memberMem
    rcases memberMem with ⟨index, rfl⟩
    have projectedMem := approximationMem index
    rcases Set.mem_iUnion.mp (centersCover projectedMem) with
      ⟨center, centerCover⟩
    rcases Set.mem_iUnion.mp centerCover with
      ⟨centerMem, projectionInBall⟩
    refine Set.mem_iUnion.mpr ⟨center, ?_⟩
    refine Set.mem_iUnion.mpr ⟨centerMem, ?_⟩
    rw [Metric.mem_ball] at projectionInBall ⊢
    calc
      dist (lpValue index) center ≤
          dist (lpValue index) (lpApproximation cutoff index) +
            dist (lpApproximation cutoff index) center :=
        dist_triangle _ _ _
      _ < epsilon := by
        dsimp only [lpValue, lpApproximation, toLpMap]
        rw [dist_eq_norm]
        linarith [uniformClose cutoff index]
  have compactClosure : IsCompact (closure (Set.range lpValue)) :=
    familyTotallyBounded.closure.isCompact_of_isClosed isClosed_closure
  have sequenceMem (index : Nat) :
      lpValue index ∈ closure (Set.range lpValue) :=
    subset_closure (Set.mem_range_self index)
  obtain ⟨limit, _limitMem, subsequence, subsequenceMono, convergence⟩ :=
    compactClosure.tendsto_subseq sequenceMem
  refine ⟨limit, subsequence, subsequenceMono, ?_⟩
  simpa only [Function.comp_def, lpValue, toLpMap] using convergence

attribute [local instance] Measure.Subtype.measureSpace

noncomputable instance scaledPhysicalCylinder_isFiniteMeasure
    (timeLength spatialRadius : Real) :
    IsFiniteMeasure
      (volume : Measure
        (ScaledPhysicalCylinder timeLength spatialRadius)) := by
  letI : IsFiniteMeasure
      (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        isCompact_Icc.measurableSet.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure
        (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  infer_instance

private theorem scaledPhysicalCylinder_bcf_sub_integral_eq_subtype
    (timeLength spatialRadius : Real)
    (left right : BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace) :
    (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
        ‖left point - right point‖ ^ 2) =
      ∫ time : Icc (0 : Real) timeLength,
        ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          ‖left ⟨time, x⟩ - right ⟨time, x⟩‖ ^ 2 := by
  letI : IsFiniteMeasure
      (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        isCompact_Icc.measurableSet.nullMeasurableSet]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure
        (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  let density : ScaledPhysicalCylinder timeLength spatialRadius → Real :=
    fun point => ‖left point - right point‖ ^ 2
  have densityContinuous : Continuous density := by
    dsimp only [density]
    fun_prop
  let bounded : BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) Real :=
    BoundedContinuousFunction.mkOfCompact ⟨density, densityContinuous⟩
  have densityIntegrable :
      Integrable density
        ((volume : Measure (Icc (0 : Real) timeLength)).prod
          (volume : Measure
            (Metric.closedBall (0 : PhysicalSpace) spatialRadius))) := by
    change Integrable
      (bounded : ScaledPhysicalCylinder timeLength spatialRadius → Real)
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius)))
    exact BoundedContinuousFunction.integrable _ bounded
  change (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
    density point) = _
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ densityIntegrable]

private theorem scaledPhysicalCylinder_integral_eq_interval_setIntegral
    (timeLength spatialRadius : Real)
    (timeLengthNonneg : 0 ≤ timeLength)
    (g : Real → PhysicalSpace → Real)
    (gContinuous : Continuous (Function.uncurry g)) :
    (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
        g point.1.1 point.2.1) =
      ∫ time in (0 : Real)..timeLength,
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time x := by
  letI : IsFiniteMeasure
      (volume : Measure (Icc (0 : Real) timeLength)) :=
    ⟨by
      have intervalMeasurable :
          NullMeasurableSet (Icc (0 : Real) timeLength)
            (volume : Measure Real) :=
        isCompact_Icc.measurableSet.nullMeasurableSet
      rw [Measure.Subtype.volume_univ intervalMeasurable]
      exact isCompact_Icc.measure_lt_top⟩
  letI : IsFiniteMeasure
      (volume : Measure (Metric.closedBall (0 : PhysicalSpace) spatialRadius)) :=
    ⟨by
      have ballMeasurable :
          NullMeasurableSet (Metric.closedBall (0 : PhysicalSpace) spatialRadius)
            (volume : Measure PhysicalSpace) :=
        (isCompact_closedBall _ _).measurableSet.nullMeasurableSet
      rw [Measure.Subtype.volume_univ ballMeasurable]
      exact (isCompact_closedBall _ _).measure_lt_top⟩
  let cylinderFunction : ScaledPhysicalCylinder timeLength spatialRadius →
      Real := fun point => g point.1.1 point.2.1
  have cylinderContinuous : Continuous cylinderFunction := by
    fun_prop
  let bounded : BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) Real :=
    BoundedContinuousFunction.mkOfCompact
      ⟨cylinderFunction, cylinderContinuous⟩
  have cylinderIntegrable :
      Integrable cylinderFunction
        ((volume : Measure (Icc (0 : Real) timeLength)).prod
          (volume : Measure
            (Metric.closedBall (0 : PhysicalSpace) spatialRadius))) := by
    change Integrable
      (bounded : ScaledPhysicalCylinder timeLength spatialRadius → Real)
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius)))
    exact BoundedContinuousFunction.integrable
      ((volume : Measure (Icc (0 : Real) timeLength)).prod
        (volume : Measure
          (Metric.closedBall (0 : PhysicalSpace) spatialRadius))) bounded
  change (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
    cylinderFunction point) = _
  rw [Measure.volume_eq_prod]
  rw [integral_prod _ cylinderIntegrable]
  simp only [cylinderFunction]
  have inner (time : Icc (0 : Real) timeLength) :
      (∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time.1 x.1) =
        ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
          g time.1 x := by
    rw [MeasureTheory.integral_subtype
      (isCompact_closedBall _ _).measurableSet]
  simp_rw [inner]
  rw [MeasureTheory.integral_subtype measurableSet_Icc
    (fun time =>
      ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
        g time x)]
  rw [intervalIntegral.integral_of_le timeLengthNonneg]
  exact MeasureTheory.integral_Icc_eq_integral_Ioc

theorem wholeRestartPrefixPhysicalTrajectory_zero_row
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ (length : Nat) (time : Real),
      wholeRestartPrefixPhysicalTrajectory initial length time 0 = 0
  | 0, _time => by
      rw [wholeRestartPrefixPhysicalTrajectory_zero]
      simpa only [initial.receipt.wholePath_initial] using
        initial.receipt.wholePath_zero_row
          ⟨0, ⟨le_rfl, initial.receipt.requestedTimePos.le⟩⟩
  | length + 1, time => by
      by_cases timeLe : time ≤ elapsedTime initial length
      · rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_le _ _ _ _ timeLe]
        exact wholeRestartPrefixPhysicalTrajectory_zero_row initial length time
      · have timeGt : elapsedTime initial length < time := lt_of_not_ge timeLe
        rw [wholeRestartPrefixPhysicalTrajectory,
          endpointSplice_of_lt _ _ _ _ timeGt]
        exact (run initial length).contact.prefixReceipt.wholePath_zero_row _

theorem finiteCoefficientMass_cube_eq_punctured_of_zero
    (radius : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    finiteStateVorticityCoefficientEnstrophy
        (integerWaveFrequencyCube radius) state =
      finiteStateVorticityCoefficientEnstrophy
        (wholeRestartModes radius) state := by
  let modes := integerWaveFrequencyCube radius
  let summand : IntegerWavevector → Real := fun wave =>
    complexCoordinateAmplitudeSq (state wave)
  have zeroMem : (0 : IntegerWavevector) ∈ modes := by
    dsimp only [modes]
    simp [integerWaveFrequencyCube, Fintype.mem_piFinset]
  have zeroSummand : summand 0 = 0 := by
    dsimp only [summand]
    rw [zeroRow]
    simp [complexCoordinateAmplitudeSq]
  have erased := Finset.sum_erase_add (s := modes) (f := summand) zeroMem
  rw [zeroSummand, add_zero] at erased
  unfold finiteStateVorticityCoefficientEnstrophy
  change (∑ wave ∈ modes, summand wave) =
    ∑ wave ∈ modes.erase 0, summand wave
  exact erased.symm

theorem finiteRealComplexFourierField_cube_eq_punctured_of_zero
    (radius : Nat)
    (state : IntegerWavevector → ComplexCoordinateVector)
    (zeroRow : state 0 = 0)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField
        (integerWaveFrequencyCube radius) state point =
      finiteRealComplexFourierField (wholeRestartModes radius) state point := by
  let modes := integerWaveFrequencyCube radius
  let term : IntegerWavevector → PhysicalSpace := fun wave =>
    realComplexFourierMode wave (state wave) point
  have zeroMem : (0 : IntegerWavevector) ∈ modes := by
    dsimp only [modes]
    simp [integerWaveFrequencyCube, Fintype.mem_piFinset]
  have zeroTerm : term 0 = 0 := by
    dsimp only [term]
    rw [zeroRow]
    simp [realComplexFourierMode]
  have erased := Finset.sum_erase_add (s := modes) (f := term) zeroMem
  rw [zeroTerm, add_zero] at erased
  unfold finiteRealComplexFourierField
  change (∑ wave ∈ modes, term wave) =
    ∑ wave ∈ modes.erase 0, term wave
  exact erased.symm

private def detectorPlateauOuter (sigma limitRadius : Real) : Real :=
  (sigma + limitRadius) / 2

private noncomputable def detectorPlateauWeight
    (limitRadius : Real)
    (level : Nat → Real)
    (sigma : Real)
    (index : Nat)
    (wave : IntegerWavevector) : Real :=
  if valid : 0 ≤ sigma ∧ sigma < limitRadius then
    ∏ coordinate : Coordinate,
      (realFrequencyPlateauSchwartz sigma
          (detectorPlateauOuter sigma limitRadius)
          valid.1 (by dsimp only [detectorPlateauOuter]; linarith)
          ((level index)⁻¹ * (wave coordinate : Real))).re
  else 1

private theorem scaledCoordinate_abs_le_of_cube_floor_mem
    (level sigma : Real)
    (levelPos : 0 < level)
    (sigmaNonneg : 0 ≤ sigma)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube ⌊sigma * level⌋₊)
    (coordinate : Coordinate) :
    |level⁻¹ * (wave coordinate : Real)| ≤ sigma := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem
  have coordinateMem := waveMem coordinate
  rw [Finset.mem_Icc] at coordinateMem
  have floorLe : (⌊sigma * level⌋₊ : Real) ≤ sigma * level :=
    Nat.floor_le (mul_nonneg sigmaNonneg levelPos.le)
  have lower : -(sigma * level) ≤ (wave coordinate : Real) := by
    have raw : -((⌊sigma * level⌋₊ : Nat) : Real) ≤
        (wave coordinate : Real) := by
      exact_mod_cast coordinateMem.1
    linarith
  have upper : (wave coordinate : Real) ≤ sigma * level := by
    have raw : (wave coordinate : Real) ≤
        ((⌊sigma * level⌋₊ : Nat) : Real) := by
      exact_mod_cast coordinateMem.2
    linarith
  rw [abs_mul, abs_of_pos (inv_pos.mpr levelPos)]
  have waveAbs : |(wave coordinate : Real)| ≤ sigma * level :=
    abs_le.mpr ⟨lower, upper⟩
  calc
    level⁻¹ * |(wave coordinate : Real)| ≤
        level⁻¹ * (sigma * level) :=
      mul_le_mul_of_nonneg_left waveAbs (inv_nonneg.mpr levelPos.le)
    _ = sigma := by field_simp [levelPos.ne']

private theorem detectorPlateauWeight_one
    (limitRadius : Real)
    (level : Nat → Real)
    (levelPos : ∀ index, 0 < level index)
    (sigma : Real)
    (index : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ integerWaveFrequencyCube ⌊sigma * level index⌋₊) :
    detectorPlateauWeight limitRadius level sigma index wave = 1 := by
  unfold detectorPlateauWeight
  by_cases valid : 0 ≤ sigma ∧ sigma < limitRadius
  · rw [dif_pos valid]
    apply Finset.prod_eq_one
    intro coordinate _coordinateMem
    rw [realFrequencyPlateauSchwartz_eq_one _ _ _ _ _
      (scaledCoordinate_abs_le_of_cube_floor_mem
        (level index) sigma (levelPos index) valid.1 wave waveMem coordinate)]
    simp
  · rw [dif_neg valid]

private theorem detectorPlateauWeight_unit
    (limitRadius : Real)
    (level : Nat → Real)
    (sigma : Real)
    (index : Nat)
    (wave : IntegerWavevector) :
    0 ≤ detectorPlateauWeight limitRadius level sigma index wave ∧
      detectorPlateauWeight limitRadius level sigma index wave ≤ 1 := by
  unfold detectorPlateauWeight
  by_cases valid : 0 ≤ sigma ∧ sigma < limitRadius
  · rw [dif_pos valid]
    have sampleUnit (coordinate : Coordinate) :
        ∃ value : Real, value ∈ Icc 0 1 ∧
          realFrequencyPlateauSchwartz sigma
              (detectorPlateauOuter sigma limitRadius)
              valid.1 (by dsimp only [detectorPlateauOuter]; linarith)
              ((level index)⁻¹ * (wave coordinate : Real)) =
            (value : Complex) :=
      realFrequencyPlateauSchwartz_real_unit sigma
        (detectorPlateauOuter sigma limitRadius) valid.1
        (by dsimp only [detectorPlateauOuter]; linarith) _
    obtain ⟨value0, value0Mem, value0Eq⟩ := sampleUnit 0
    obtain ⟨value1, value1Mem, value1Eq⟩ := sampleUnit 1
    obtain ⟨value2, value2Mem, value2Eq⟩ := sampleUnit 2
    rw [Fin.prod_univ_three, value0Eq, value1Eq, value2Eq]
    simp only [Complex.ofReal_re]
    constructor
    · exact mul_nonneg (mul_nonneg value0Mem.1 value1Mem.1) value2Mem.1
    · have value01Le : value0 * value1 ≤ 1 :=
        mul_le_one₀ value0Mem.2 value1Mem.1 value1Mem.2
      exact mul_le_one₀ value01Le value2Mem.1 value2Mem.2
  · rw [dif_neg valid]
    exact ⟨zero_le_one, le_rfl⟩

private theorem detectorPlateauWeight_frequencyReal
    (limitRadius : Real)
    (level : Nat → Real)
    (sigma : Real)
    (sigmaValid : 0 ≤ sigma ∧ sigma < limitRadius)
    (index : Nat)
    (wave : IntegerWavevector)
    (coordinate : Coordinate) :
    realFrequencyPlateauSchwartz sigma
        (detectorPlateauOuter sigma limitRadius)
        sigmaValid.1 (by dsimp only [detectorPlateauOuter]; linarith)
        ((level index)⁻¹ * (wave coordinate : Real)) =
      (((realFrequencyPlateauSchwartz sigma
          (detectorPlateauOuter sigma limitRadius)
          sigmaValid.1 (by dsimp only [detectorPlateauOuter]; linarith)
          ((level index)⁻¹ * (wave coordinate : Real))).re : Real) :
            Complex) := by
  obtain ⟨value, _valueMem, valueEq⟩ :=
    realFrequencyPlateauSchwartz_real_unit sigma
      (detectorPlateauOuter sigma limitRadius) sigmaValid.1
      (by dsimp only [detectorPlateauOuter]; linarith)
      ((level index)⁻¹ * (wave coordinate : Real))
  rw [valueEq]
  simp

theorem finiteBandVorticity_tensorSchwartzCoordinate_lowerBound
    (level : Nat → Real)
    (radius : Nat → Nat)
    (coefficient : Nat → IntegerWavevector → ComplexCoordinateVector)
    (point : Nat → PhysicalSpace)
    (limitRadius massCeiling : Real)
    (limitValue : PhysicalSpace)
    (limitRadiusPos : 0 < limitRadius)
    (limitValueNe : limitValue ≠ 0)
    (levelPos : ∀ index, 0 < level index)
    (levelTendsto : Tendsto level atTop atTop)
    (ratioTendsto : Tendsto
      (fun index => (radius index : Real) / level index) atTop
        (nhds limitRadius))
    (massBound : ∀ index,
      (level index)⁻¹ *
          ∑ wave ∈ integerWaveFrequencyCube (radius index),
            complexCoordinateAmplitudeSq (coefficient index wave) ≤
        massCeiling)
    (outerTendsto : Tendsto
      (fun index =>
        ((level index)⁻¹ ^ 2 : Real) •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (coefficient index) (point index))
      atTop (nhds limitValue)) :
    ∃ testCoordinate : Coordinate,
      ∃ innerRadius outerRadius lowerBound : Real,
      ∃ frequencyTest : Coordinate → 𝓢(Real, Complex),
        0 ≤ innerRadius ∧ innerRadius < outerRadius ∧
          outerRadius < limitRadius ∧ 0 < lowerBound ∧
          (∀ coordinate frequency, |frequency| ≤ innerRadius →
            frequencyTest coordinate frequency = 1) ∧
          (∀ coordinate frequency, outerRadius ≤ |frequency| →
            frequencyTest coordinate frequency = 0) ∧
          (∀ coordinate frequency,
            ∃ value : Real, value ∈ Icc 0 1 ∧
              frequencyTest coordinate frequency = (value : Complex)) ∧
          ∀ᶠ index in atTop,
              lowerBound ≤
                |level index *
                  ∑ wave ∈ integerWaveFrequencyCube (radius index),
                    complexCoordinateRealInner
                      (Pi.single testCoordinate
                        (recenteredTensorSchwartzFourierCoefficient
                          (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
                          (level index)⁻¹ (inv_ne_zero (levelPos index).ne')
                          (point index) wave))
                      (coefficient index wave)| := by
  let weight : Real → Nat → IntegerWavevector → Real :=
    detectorPlateauWeight limitRadius level
  obtain ⟨testCoordinate, innerRadius, lowerBound,
      innerRadiusNonneg, innerRadiusLt, lowerBoundPos,
      detectorEventually⟩ :=
    finiteBandVorticity_parabolicScale_weightedCoordinate_lowerBound
      level radius coefficient weight point limitRadius massCeiling
      limitValue limitRadiusPos limitValueNe levelPos levelTendsto
      ratioTendsto
      (detectorPlateauWeight_one limitRadius level levelPos)
      (fun sigma index wave _waveMem =>
        detectorPlateauWeight_unit limitRadius level sigma index wave)
      massBound outerTendsto
  let outerRadius := detectorPlateauOuter innerRadius limitRadius
  have innerRadiusLtOuter : innerRadius < outerRadius := by
    dsimp only [outerRadius, detectorPlateauOuter]
    linarith
  have outerRadiusLt : outerRadius < limitRadius := by
    dsimp only [outerRadius, detectorPlateauOuter]
    linarith
  let frequencyTest : Coordinate → 𝓢(Real, Complex) := fun _ =>
    realFrequencyPlateauSchwartz innerRadius outerRadius
      innerRadiusNonneg innerRadiusLtOuter
  refine ⟨testCoordinate, innerRadius, outerRadius, lowerBound,
    frequencyTest, innerRadiusNonneg, innerRadiusLtOuter, outerRadiusLt,
    lowerBoundPos, ?_, ?_, ?_, ?_⟩
  · intro coordinate frequency frequencyMem
    exact realFrequencyPlateauSchwartz_eq_one innerRadius outerRadius
      innerRadiusNonneg innerRadiusLtOuter frequency frequencyMem
  · intro coordinate frequency frequencyOutside
    exact realFrequencyPlateauSchwartz_eq_zero innerRadius outerRadius
      innerRadiusNonneg innerRadiusLtOuter frequency frequencyOutside
  · intro coordinate frequency
    exact realFrequencyPlateauSchwartz_real_unit innerRadius outerRadius
      innerRadiusNonneg innerRadiusLtOuter frequency
  filter_upwards [detectorEventually] with index fieldLower
  have scalePos : 0 < (level index)⁻¹ := inv_pos.mpr (levelPos index)
  have frequencyReal (wave : IntegerWavevector)
      (_waveMem : wave ∈ integerWaveFrequencyCube (radius index))
      (coordinate : Coordinate) :
      frequencyTest coordinate
          ((level index)⁻¹ * (wave coordinate : Real)) =
        ((((frequencyTest coordinate
          ((level index)⁻¹ * (wave coordinate : Real))).re : Real)) :
            Complex) := by
    exact detectorPlateauWeight_frequencyReal limitRadius level innerRadius
      ⟨innerRadiusNonneg, innerRadiusLt⟩ index wave coordinate
  have pairingEq :=
    finiteRecenteredInverseFourierRealTensorPairing_eq_weightedField
      frequencyTest
      (fun wave coordinate =>
        (frequencyTest coordinate
          ((level index)⁻¹ * (wave coordinate : Real))).re)
      (level index)⁻¹ scalePos (point index)
      (integerWaveFrequencyCube (radius index)) (coefficient index)
      testCoordinate frequencyReal
  have weightEq :
      (fun wave =>
        (((∏ coordinate : Coordinate,
          (frequencyTest coordinate
            ((level index)⁻¹ * (wave coordinate : Real))).re : Real) :
              Complex) • coefficient index wave)) =
        (fun wave =>
          detectorPlateauWeight limitRadius level innerRadius index wave •
            coefficient index wave) := by
    funext wave coordinate
    dsimp only [frequencyTest, outerRadius]
    rw [show detectorPlateauWeight limitRadius level innerRadius index wave =
        ∏ coordinate : Coordinate,
          (realFrequencyPlateauSchwartz innerRadius
            (detectorPlateauOuter innerRadius limitRadius)
            innerRadiusNonneg innerRadiusLtOuter
            ((level index)⁻¹ * (wave coordinate : Real))).re by
      unfold detectorPlateauWeight
      rw [dif_pos ⟨innerRadiusNonneg, innerRadiusLt⟩]]
    simp
  rw [weightEq] at pairingEq
  have normalizedPairingEq :
      level index *
          (∑ wave ∈ integerWaveFrequencyCube (radius index),
            complexCoordinateRealInner
              (Pi.single testCoordinate
                (recenteredTensorSchwartzFourierCoefficient
                  (fun coordinate => 𝓕⁻ (frequencyTest coordinate))
                  (level index)⁻¹ (inv_ne_zero (levelPos index).ne')
                  (point index) wave))
              (coefficient index wave)) =
        (((level index)⁻¹ ^ 2 : Real) •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube (radius index))
            (fun wave =>
              detectorPlateauWeight limitRadius level innerRadius index wave •
                coefficient index wave)
            (point index)) testCoordinate := by
    have scalarEq :
        level index * (level index)⁻¹ ^ 3 = (level index)⁻¹ ^ 2 := by
      field_simp [(levelPos index).ne']
    rw [pairingEq]
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, scalarEq]
  rw [normalizedPairingEq]
  rw [← Real.norm_eq_abs]
  exact fieldLower

private theorem wholeRestartModes_mono
    {small large : Nat}
    (smallLe : small ≤ large) :
    wholeRestartModes small ⊆ wholeRestartModes large := by
  intro wave waveMem
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube] at waveMem ⊢
  rw [Finset.mem_erase] at waveMem ⊢
  exact ⟨waveMem.1, integerWaveFrequencyCube_mono smallLe waveMem.2⟩

private theorem finiteRealComplexFourierField_projection_subset
    {small large : Finset IntegerWavevector}
    (subset : small ⊆ large)
    (state : ComplexVorticityHilbertState)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField large
        (complexSharpSupportProjection small state) point =
      finiteRealComplexFourierField small state point := by
  unfold finiteRealComplexFourierField
  rw [← Finset.sum_subset subset]
  · apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  · intro wave waveLarge waveNotSmall
    rw [complexSharpSupportProjection_apply, if_neg waveNotSmall]
    simp [realComplexFourierMode]

private theorem finiteRealComplexFourierField_nested_sub_eq
    {small large : Finset IntegerWavevector}
    (subset : small ⊆ large)
    (state : ComplexVorticityHilbertState)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField large state point -
        finiteRealComplexFourierField small state point =
      finiteRealComplexFourierField large
        (state - complexSharpSupportProjection small state) point := by
  rw [← finiteRealComplexFourierField_projection_subset subset state point]
  exact finiteRealComplexFourierField_sub large state
    (complexSharpSupportProjection small state) point

private theorem finiteRealComplexFourierVelocityField_projection_subset
    {small large : Finset IntegerWavevector}
    (subset : small ⊆ large)
    (state : ComplexVorticityHilbertState)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField large
        (finiteStateVelocityCoefficient
          (complexSharpSupportProjection small state)) point =
      finiteRealComplexFourierField small
        (finiteStateVelocityCoefficient state) point := by
  unfold finiteRealComplexFourierField
  rw [← Finset.sum_subset subset]
  · apply Finset.sum_congr rfl
    intro wave waveMem
    unfold finiteStateVelocityCoefficient
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  · intro wave _waveLarge waveNotSmall
    unfold finiteStateVelocityCoefficient
    rw [complexSharpSupportProjection_apply, if_neg waveNotSmall]
    simp [realComplexFourierMode,
      biotSavartVelocityCoefficient_zero_vorticity]

private theorem finiteRealComplexFourierVelocityField_nested_sub_eq
    {small large : Finset IntegerWavevector}
    (subset : small ⊆ large)
    (state : ComplexVorticityHilbertState)
    (point : PhysicalSpace) :
    finiteRealComplexFourierField large
          (finiteStateVelocityCoefficient state) point -
        finiteRealComplexFourierField small
          (finiteStateVelocityCoefficient state) point =
      finiteRealComplexFourierField large
        (finiteStateVelocityCoefficient
          (state - complexSharpSupportProjection small state)) point := by
  rw [← finiteRealComplexFourierVelocityField_projection_subset
    subset state point]
  unfold finiteRealComplexFourierField
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  rw [finiteStateVelocityCoefficient_sub]
  ext coordinate
  simp [realComplexFourierMode, coefficientReal, coefficientImag]
  ring

private theorem integerWave_mem_frequencyCube_of_norm_lt
    (radius : ℕ) (wave : IntegerWavevector)
    (normLt : integerWaveNormSq wave <
      (((radius + 1 : ℕ) : ℝ) ^ 2)) :
    wave ∈ integerWaveFrequencyCube radius := by
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset]
  intro coordinate
  rw [Finset.mem_Icc]
  have coordinateSqLe :
      ((wave coordinate : ℝ) ^ 2) ≤ integerWaveNormSq wave := by
    unfold integerWaveNormSq
    exact Finset.single_le_sum
      (fun other _otherMem => sq_nonneg (wave other : ℝ))
      (Finset.mem_univ coordinate)
  constructor
  · by_contra notLower
    have lowerInt :
        ((radius + 1 : ℕ) : ℤ) ≤ -(wave coordinate) := by omega
    have lowerReal :
        ((radius + 1 : ℕ) : ℝ) ≤ -(wave coordinate : ℝ) := by
      exact_mod_cast lowerInt
    have negNonneg : 0 ≤ -(wave coordinate : ℝ) :=
      (Nat.cast_nonneg (radius + 1)).trans lowerReal
    have squareLe :
        (((radius + 1 : ℕ) : ℝ) ^ 2) ≤
          (-(wave coordinate : ℝ)) ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg (radius + 1)) negNonneg).2 lowerReal
    rw [neg_sq] at squareLe
    linarith
  · by_contra notUpper
    have upperInt : ((radius + 1 : ℕ) : ℤ) ≤ wave coordinate := by omega
    have upperReal :
        ((radius + 1 : ℕ) : ℝ) ≤ (wave coordinate : ℝ) := by
      exact_mod_cast upperInt
    have waveNonneg : 0 ≤ (wave coordinate : ℝ) :=
      (Nat.cast_nonneg (radius + 1)).trans upperReal
    have squareLe :
        (((radius + 1 : ℕ) : ℝ) ^ 2) ≤
          (wave coordinate : ℝ) ^ 2 :=
      (sq_le_sq₀ (Nat.cast_nonneg (radius + 1)) waveNonneg).2 upperReal
    linarith

private theorem finiteVelocityProjectionDifferenceMass_eq_high
    (modes : Finset IntegerWavevector)
    (radius : ℕ)
    (state : ComplexVorticityHilbertState) :
    let difference :=
      state - complexSharpSupportProjection
        (integerWaveFrequencyCube radius) state
    finiteStateVorticityCoefficientEnstrophy modes
        (finiteComplexVorticityState modes
          (finiteStateVelocityCoefficient difference)) =
      finiteStateVelocityHighFrequencySquare modes radius difference := by
  dsimp only
  rw [finiteStateVelocityHighFrequencySquare_eq_sum]
  unfold finiteStateVorticityCoefficientEnstrophy
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have fullEq :
      (∑ wave ∈ modes,
        complexCoordinateVectorNormSq
          (finiteStateVelocityCoefficient
            (state - complexSharpSupportProjection
              (integerWaveFrequencyCube radius) state) wave)) =
      ∑ wave ∈ finiteStateVelocityHighFrequencyModes modes radius,
        complexCoordinateVectorNormSq
          (finiteStateVelocityCoefficient
            (state - complexSharpSupportProjection
              (integerWaveFrequencyCube radius) state) wave) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro wave waveMem waveNotHigh
    have notFloor :
        ¬((((radius + 1 : ℕ) : ℝ) ^ 2) ≤ integerWaveNormSq wave) := by
      intro floor
      exact waveNotHigh (Finset.mem_filter.mpr ⟨waveMem, floor⟩)
    have waveLow : wave ∈ integerWaveFrequencyCube radius :=
      integerWave_mem_frequencyCube_of_norm_lt radius wave
        (lt_of_not_ge notFloor)
    have rowZero :
        (state - complexSharpSupportProjection
            (integerWaveFrequencyCube radius) state) wave = 0 := by
      simp [complexSharpSupportProjection_apply, waveLow]
    unfold finiteStateVelocityCoefficient
    rw [rowZero, biotSavartVelocityCoefficient_zero_vorticity]
    simp [complexCoordinateVectorNormSq]
  rw [← fullEq]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [finiteComplexVorticityState_apply, if_pos waveMem]

private theorem finiteVelocityProjectionDifferenceMass_weighted_le
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (transverse : ∀ wave,
      complexWavevector wave ⬝ᵥ state wave = 0) :
    let difference :=
      state - complexSharpSupportProjection
        (integerWaveFrequencyCube radius) state
    (2 * Real.pi) ^ 2 * (((radius + 1 : ℕ) : ℝ) ^ 2) *
        finiteStateVorticityCoefficientEnstrophy modes
          (finiteComplexVorticityState modes
            (finiteStateVelocityCoefficient difference)) ≤
      finiteStateVorticityCoefficientEnstrophy modes difference := by
  dsimp only
  rw [finiteVelocityProjectionDifferenceMass_eq_high]
  have paid :=
    finiteStateVelocityHighFrequencySquare_weighted_le_vorticityMass
      modes zeroNotMem radius
      (state - complexSharpSupportProjection
        (integerWaveFrequencyCube radius) state) (by
        intro wave _waveMem
        change complexWavevector wave ⬝ᵥ
            (state wave -
              complexSharpSupportProjection
                (integerWaveFrequencyCube radius) state wave) = 0
        have projectedTransverse :
            complexWavevector wave ⬝ᵥ
              complexSharpSupportProjection
                (integerWaveFrequencyCube radius) state wave = 0 := by
          by_cases waveLow : wave ∈ integerWaveFrequencyCube radius
          · rw [complexSharpSupportProjection_apply, if_pos waveLow]
            exact transverse wave
          · rw [complexSharpSupportProjection_apply, if_neg waveLow]
            simp [dotProduct]
        rw [dotProduct_sub, transverse wave, projectedTransverse, sub_self])
  simpa only [finiteStateVorticityMass,
    finiteStateVorticityCoefficientEnstrophy,
    complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq] using paid

private theorem finiteStateFourierReality_sub_projection
    (modes : Finset IntegerWavevector)
    (negClosed : ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (state - complexSharpSupportProjection modes state) := by
  have projectedReality :
      FiniteStateFourierReality
        (complexSharpSupportProjection modes state) := by
    intro wave
    have negMemIff : waveNeg wave ∈ modes ↔ wave ∈ modes := by
      constructor
      · intro negMem
        simpa using negClosed negMem
      · exact negClosed
    rw [complexSharpSupportProjection_apply,
      complexSharpSupportProjection_apply]
    by_cases waveMem : wave ∈ modes
    · rw [if_pos waveMem, if_pos (negMemIff.mpr waveMem), reality]
    · rw [if_neg waveMem, if_neg (not_congr negMemIff |>.mpr waveMem)]
      exact vectorConj_zero.symm
  intro wave
  change state (waveNeg wave) -
      complexSharpSupportProjection modes state (waveNeg wave) =
    vectorConj
      (state wave - complexSharpSupportProjection modes state wave)
  rw [reality wave, projectedReality wave]
  funext coordinate
  simp [vectorConj]

private theorem finiteProjectionDifferenceMass_le_cubeComplement
    (small large : Nat)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    finiteStateVorticityCoefficientEnstrophy (wholeRestartModes large)
        (state - complexSharpSupportProjection (wholeRestartModes small) state) ≤
      wholeVorticityEuclideanMass
        (complexSharpSupportProjection (integerWaveFrequencyCube small) state -
          state) := by
  have projectionEq :
      complexSharpSupportProjection (integerWaveFrequencyCube small) state =
        complexSharpSupportProjection (wholeRestartModes small) state := by
    dsimp only [wholeRestartModes, puncturedIntegerWaveFrequencyCube]
    exact (complexSharpSupportProjection_erase_zero_eq
      (integerWaveFrequencyCube small) state zeroRow).symm
  calc
    finiteStateVorticityCoefficientEnstrophy (wholeRestartModes large)
        (state - complexSharpSupportProjection (wholeRestartModes small) state) ≤
      wholeVorticityEuclideanMass
        (state - complexSharpSupportProjection (wholeRestartModes small) state) :=
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        _ _
    _ = wholeVorticityEuclideanMass
        (complexSharpSupportProjection (wholeRestartModes small) state -
          state) := by
      unfold wholeVorticityEuclideanMass
      apply tsum_congr
      intro wave
      rw [vorticityRowAmplitude_sq, vorticityRowAmplitude_sq]
      rw [← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      unfold complexCoordinateAmplitudeSq
      apply Finset.sum_congr rfl
      intro coordinate _coordinateMem
      change Complex.normSq
          (state wave coordinate -
            complexSharpSupportProjection (wholeRestartModes small) state wave
              coordinate) =
        Complex.normSq
          (complexSharpSupportProjection (wholeRestartModes small) state wave
              coordinate - state wave coordinate)
      rw [show state wave coordinate -
          complexSharpSupportProjection (wholeRestartModes small) state wave
              coordinate =
        -(complexSharpSupportProjection (wholeRestartModes small) state wave
              coordinate - state wave coordinate) by ring,
        Complex.normSq_neg]
    _ = wholeVorticityEuclideanMass
        (complexSharpSupportProjection (integerWaveFrequencyCube small) state -
          state) := by rw [projectionEq]

theorem sourcePrefixWindow_nestedBand_toLp_error_sq_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (level windowStart windowFinish timeLength spatialRadius : Real)
    (center : PhysicalSpace)
    (smallBand largeBand gradientCeiling : Real)
    (coverRadius : Nat)
    (largeProfile smallProfile : BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace)
    (levelPos : 0 < level)
    (levelOne : 1 ≤ level)
    (windowStartNonneg : 0 ≤ windowStart)
    (windowStartLeFinish : windowStart ≤ windowFinish)
    (windowFinishLe : windowFinish ≤ elapsedTime initial length)
    (durationEq :
      level ^ 2 * (windowFinish - windowStart) = timeLength)
    (timeLengthNonneg : 0 ≤ timeLength)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (centerMem : center ∈ physicalUnitCell)
    (smallBandPos : 0 < smallBand)
    (smallBandLeLarge : smallBand ≤ largeBand)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real))
    (gradientIntegrable :
      IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume windowStart windowFinish)
    (gradientPayment :
      level⁻¹ *
          (∫ time in windowStart..windowFinish,
            wholeStateVorticityGradientMass
              (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        gradientCeiling)
    (largeProfileEq : ∀ point,
      largeProfile point =
        level⁻¹ ^ 2 •
          finiteRealComplexFourierField
            (wholeRestartModes (Nat.ceil (largeBand / level⁻¹)))
            (wholeRestartPrefixPhysicalTrajectory initial length
              (windowStart + level⁻¹ ^ 2 * point.1.1))
            (center + level⁻¹ • point.2.1))
    (smallProfileEq : ∀ point,
      smallProfile point =
        level⁻¹ ^ 2 •
          finiteRealComplexFourierField
            (wholeRestartModes (Nat.ceil (smallBand / level⁻¹)))
            (wholeRestartPrefixPhysicalTrajectory initial length
              (windowStart + level⁻¹ ^ 2 * point.1.1))
            (center + level⁻¹ • point.2.1)) :
    ‖BoundedContinuousFunction.toLp 2 volume Real largeProfile -
        BoundedContinuousFunction.toLp 2 volume Real smallProfile‖ ^ 2 ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) *
        gradientCeiling / smallBand ^ 2 := by
  let scale : Real := level⁻¹
  let smallRadius : Nat := Nat.ceil (smallBand / scale)
  let largeRadius : Nat := Nat.ceil (largeBand / scale)
  let originalPath : Real → ComplexVorticityHilbertState :=
    wholeRestartPrefixPhysicalTrajectory initial length
  let differencePath : Real → ComplexVorticityHilbertState := fun time =>
    originalPath time -
      complexSharpSupportProjection (wholeRestartModes smallRadius)
        (originalPath time)
  have scalePos : 0 < scale := inv_pos.mpr levelPos
  have scaleLeOne : scale ≤ 1 :=
    (inv_le_one₀ levelPos).2 levelOne
  have smallRadiusLeLarge : smallRadius ≤ largeRadius := by
    dsimp only [smallRadius, largeRadius]
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right smallBandLeLarge scalePos.le
  have modesSubset :
      wholeRestartModes smallRadius ⊆ wholeRestartModes largeRadius :=
    wholeRestartModes_mono smallRadiusLeLarge
  have largeNegClosed : ∀ {wave},
      wave ∈ wholeRestartModes largeRadius →
        waveNeg wave ∈ wholeRestartModes largeRadius := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem largeRadius waveMem
  have smallNegClosed : ∀ {wave},
      wave ∈ wholeRestartModes smallRadius →
        waveNeg wave ∈ wholeRestartModes smallRadius := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem smallRadius waveMem
  have finishEq : windowFinish = windowStart + scale ^ 2 * timeLength := by
    dsimp only [scale]
    rw [show level⁻¹ ^ 2 = (level ^ 2)⁻¹ by rw [inv_pow]]
    field_simp [levelPos.ne']
    nlinarith [durationEq]
  have originalContinuous : ContinuousOn originalPath
      (Icc windowStart windowFinish) :=
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial length).mono
      (Icc_subset_Icc windowStartNonneg windowFinishLe)
  have differenceContinuous : ContinuousOn differencePath
      (Icc windowStart windowFinish) := by
    dsimp only [differencePath, originalPath]
    exact originalContinuous.sub
      ((complexSharpSupportProjection_continuous_local
        (wholeRestartModes smallRadius)).comp_continuousOn
          originalContinuous)
  have fieldIntegrable :=
    finiteFieldBallMass_intervalIntegrable_of_continuousOn differencePath
      (wholeRestartModes largeRadius) center scale spatialRadius
      windowStart windowFinish windowStartLeFinish differenceContinuous
  have coefficientIntegrable :=
    finiteCoefficientMass_intervalIntegrable_of_continuousOn differencePath
      (wholeRestartModes largeRadius) windowStart windowFinish
      windowStartLeFinish differenceContinuous
  have originalRealityAE :=
    wholeRestartPrefixPhysicalTrajectory_fourierReality_ae initial length
  have windowSubset :
      Icc windowStart windowFinish ⊆ Icc 0 (elapsedTime initial length) :=
    Icc_subset_Icc windowStartNonneg windowFinishLe
  have differenceRealityAE : ∀ᵐ time : Real
      ∂volume.restrict (Icc windowStart windowFinish),
        FiniteStateFourierReality (differencePath time) := by
    have windowReality :=
      ae_mono (Measure.restrict_mono windowSubset le_rfl) originalRealityAE
    filter_upwards [windowReality] with time timeReality
    dsimp only [differencePath, originalPath]
    exact finiteStateFourierReality_sub_projection
      (wholeRestartModes smallRadius) smallNegClosed _ timeReality
  have physicalCover :=
    scaledFiniteField_spacetime_ball_mass_le_cellCover_originalReality
      (wholeRestartModes largeRadius) largeNegClosed differencePath center
      centerMem windowStart windowFinish scale timeLength spatialRadius
      scalePos scaleLeOne timeLengthNonneg spatialRadiusNonneg finishEq
      coverRadius coverRadiusLarge differenceRealityAE fieldIntegrable
      coefficientIntegrable
  have tailIntegrable :=
    wholeRestartPrefix_cubeComplementMass_intervalIntegrable initial length
      smallRadius windowStart windowFinish windowStartNonneg
      windowStartLeFinish windowFinishLe
  have coefficientLeTail :
      (∫ time in windowStart..windowFinish,
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes largeRadius) (differencePath time)) ≤
        ∫ time in windowStart..windowFinish,
          wholeVorticityEuclideanMass
            (complexSharpSupportProjection
                (integerWaveFrequencyCube smallRadius)
                (originalPath time) - originalPath time) := by
    apply intervalIntegral.integral_mono_ae_restrict windowStartLeFinish
      coefficientIntegrable tailIntegrable
    filter_upwards with time
    exact finiteProjectionDifferenceMass_le_cubeComplement
      smallRadius largeRadius (originalPath time)
        (wholeRestartPrefixPhysicalTrajectory_zero_row initial length time)
  have tailPayment :=
    wholeRestartPrefix_scaledCubeComplement_spacetimeTail_le_gradientCeiling
      initial length windowStart windowFinish level smallBand gradientCeiling
      windowStartNonneg windowStartLeFinish windowFinishLe levelPos
      smallBandPos gradientIntegrable gradientPayment
  have coefficientPayment :
      scale⁻¹ *
          (∫ time in windowStart..windowFinish,
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes largeRadius) (differencePath time)) ≤
        gradientCeiling / smallBand ^ 2 := by
    calc
      _ ≤ scale⁻¹ *
          (∫ time in windowStart..windowFinish,
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                  (integerWaveFrequencyCube smallRadius)
                  (originalPath time) - originalPath time)) :=
        mul_le_mul_of_nonneg_left coefficientLeTail
          (inv_nonneg.mpr scalePos.le)
      _ = level *
          (∫ time in windowStart..windowFinish,
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                  (integerWaveFrequencyCube smallRadius)
                  (originalPath time) - originalPath time)) := by
        dsimp only [scale]
        rw [inv_inv]
      _ ≤ gradientCeiling / smallBand ^ 2 := by
        simpa only [smallRadius, originalPath, scale] using tailPayment
  have cylinderEq :
      (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
          ‖largeProfile point - smallProfile point‖ ^ 2) =
        ∫ scaledTime in (0 : Real)..timeLength,
          ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            ‖scale ^ 2 •
              finiteRealComplexFourierField
                (wholeRestartModes largeRadius)
                (differencePath
                  (windowStart + scale ^ 2 * scaledTime))
                (center + scale • x)‖ ^ 2 := by
    let g : Real → PhysicalSpace → Real := fun scaledTime x =>
      ‖scale ^ 2 •
        finiteRealComplexFourierField
          (wholeRestartModes largeRadius)
          (differencePath (windowStart + scale ^ 2 * scaledTime))
          (center + scale • x)‖ ^ 2
    calc
      (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
          ‖largeProfile point - smallProfile point‖ ^ 2) =
          ∫ scaledTime : Icc (0 : Real) timeLength,
            ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              ‖largeProfile ⟨scaledTime, x⟩ -
                smallProfile ⟨scaledTime, x⟩‖ ^ 2 :=
        scaledPhysicalCylinder_bcf_sub_integral_eq_subtype
          timeLength spatialRadius largeProfile smallProfile
      _ = ∫ scaledTime : Icc (0 : Real) timeLength,
            ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime.1 x.1 := by
        apply integral_congr_ae
        filter_upwards with scaledTime
        apply integral_congr_ae
        filter_upwards with x
        let point : ScaledPhysicalCylinder timeLength spatialRadius :=
          ⟨scaledTime, x⟩
        rw [show largeProfile point =
              scale ^ 2 • finiteRealComplexFourierField
                (wholeRestartModes largeRadius)
                (originalPath
                  (windowStart + scale ^ 2 * scaledTime.1))
                (center + scale • x.1) by
              simpa only [scale, largeRadius, originalPath, point] using
                largeProfileEq point,
            show smallProfile point =
              scale ^ 2 • finiteRealComplexFourierField
                (wholeRestartModes smallRadius)
                (originalPath
                  (windowStart + scale ^ 2 * scaledTime.1))
                (center + scale • x.1) by
              simpa only [scale, smallRadius, originalPath, point] using
                smallProfileEq point]
        rw [← smul_sub]
        rw [finiteRealComplexFourierField_nested_sub_eq modesSubset]
        rfl
      _ = ∫ scaledTime in (0 : Real)..timeLength,
            ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime x := by
        have inner (scaledTime : Icc (0 : Real) timeLength) :
            (∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
                g scaledTime.1 x.1) =
              ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
                g scaledTime.1 x := by
          rw [MeasureTheory.integral_subtype
            (isCompact_closedBall _ _).measurableSet]
        simp_rw [inner]
        rw [MeasureTheory.integral_subtype measurableSet_Icc
          (fun scaledTime =>
            ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime x)]
        rw [intervalIntegral.integral_of_le timeLengthNonneg]
        exact MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = _ := by rfl
  rw [boundedContinuousFunction_toLp_sub_norm_sq_eq_integral volume]
  rw [cylinderEq]
  calc
    _ ≤ ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ *
        (∫ time in windowStart..windowFinish,
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes largeRadius) (differencePath time)) :=
      physicalCover
    _ ≤ ((integerWaveFrequencyCube coverRadius).card : Real) *
        (gradientCeiling / smallBand ^ 2) := by
      have coverNonneg :
          0 ≤ ((integerWaveFrequencyCube coverRadius).card : Real) := by
        exact_mod_cast Nat.zero_le
          (integerWaveFrequencyCube coverRadius).card
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left coefficientPayment coverNonneg
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) *
        gradientCeiling / smallBand ^ 2 := by ring

/-- On one actual normalized prefix window, nested physical velocity bands
have a local space-time `L²` gap paid directly by the source whole-gradient
budget.  The extra Hodge frequency weight improves the vorticity `B⁻²` tail
to the velocity `B⁻⁴` tail without introducing a whole-velocity carrier. -/
theorem wholeRestartPrefix_nestedBandVelocity_toLp_error_sq_le
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (length : Nat)
    (level windowStart windowFinish timeLength spatialRadius : Real)
    (center : PhysicalSpace)
    (smallBand largeBand gradientCeiling : Real)
    (coverRadius : Nat)
    (largeProfile smallProfile : BoundedContinuousFunction
      (ScaledPhysicalCylinder timeLength spatialRadius) PhysicalSpace)
    (levelPos : 0 < level)
    (levelOne : 1 ≤ level)
    (windowStartNonneg : 0 ≤ windowStart)
    (windowStartLeFinish : windowStart ≤ windowFinish)
    (windowFinishLe : windowFinish ≤ elapsedTime initial length)
    (durationEq :
      level ^ 2 * (windowFinish - windowStart) = timeLength)
    (timeLengthNonneg : 0 ≤ timeLength)
    (spatialRadiusNonneg : 0 ≤ spatialRadius)
    (centerMem : center ∈ physicalUnitCell)
    (smallBandPos : 0 < smallBand)
    (smallBandLeLarge : smallBand ≤ largeBand)
    (coverRadiusLarge : spatialRadius + 2 ≤ (coverRadius : Real))
    (gradientIntegrable :
      IntervalIntegrable
        (fun time =>
          wholeStateVorticityGradientMass
            (wholeRestartPrefixPhysicalTrajectory initial length time))
        volume windowStart windowFinish)
    (gradientPayment :
      level⁻¹ *
          (∫ time in windowStart..windowFinish,
            wholeStateVorticityGradientMass
              (wholeRestartPrefixPhysicalTrajectory initial length time)) ≤
        gradientCeiling)
    (largeProfileEq : ∀ point,
      largeProfile point =
        level⁻¹ •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube
              (Nat.ceil (largeBand / level⁻¹)))
            (finiteStateVelocityCoefficient
              (wholeRestartPrefixPhysicalTrajectory initial length
                (windowStart + level⁻¹ ^ 2 * point.1.1)))
            (center + level⁻¹ • point.2.1))
    (smallProfileEq : ∀ point,
      smallProfile point =
        level⁻¹ •
          finiteRealComplexFourierField
            (integerWaveFrequencyCube
              (Nat.ceil (smallBand / level⁻¹)))
            (finiteStateVelocityCoefficient
              (wholeRestartPrefixPhysicalTrajectory initial length
                (windowStart + level⁻¹ ^ 2 * point.1.1)))
            (center + level⁻¹ • point.2.1)) :
    ‖BoundedContinuousFunction.toLp 2 volume Real largeProfile -
        BoundedContinuousFunction.toLp 2 volume Real smallProfile‖ ^ 2 ≤
      ((integerWaveFrequencyCube coverRadius).card : Real) *
        gradientCeiling /
          ((2 * Real.pi) ^ 2 * smallBand ^ 4) := by
  let scale : Real := level⁻¹
  let smallRadius : Nat := Nat.ceil (smallBand / scale)
  let largeRadius : Nat := Nat.ceil (largeBand / scale)
  let originalPath : Real → ComplexVorticityHilbertState :=
    wholeRestartPrefixPhysicalTrajectory initial length
  let differencePath : Real → ComplexVorticityHilbertState := fun time =>
    originalPath time -
      complexSharpSupportProjection (integerWaveFrequencyCube smallRadius)
        (originalPath time)
  let velocityMass : Real → Real := fun time =>
    finiteStateVorticityCoefficientEnstrophy
      (wholeRestartModes largeRadius)
      (finiteComplexVorticityState (wholeRestartModes largeRadius)
        (finiteStateVelocityCoefficient (differencePath time)))
  let tailMass : Real → Real := fun time =>
    wholeVorticityEuclideanMass
      (complexSharpSupportProjection
          (integerWaveFrequencyCube smallRadius) (originalPath time) -
        originalPath time)
  have scalePos : 0 < scale := inv_pos.mpr levelPos
  have scaleLeOne : scale ≤ 1 :=
    (inv_le_one₀ levelPos).2 levelOne
  have smallRadiusLeLarge : smallRadius ≤ largeRadius := by
    dsimp only [smallRadius, largeRadius]
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right smallBandLeLarge scalePos.le
  have cubeSubset :
      integerWaveFrequencyCube smallRadius ⊆
        integerWaveFrequencyCube largeRadius :=
    integerWaveFrequencyCube_mono smallRadiusLeLarge
  have largeNegClosed : ∀ {wave},
      wave ∈ wholeRestartModes largeRadius →
        waveNeg wave ∈ wholeRestartModes largeRadius := by
    intro wave waveMem
    exact puncturedIntegerWaveFrequencyCube_waveNeg_mem largeRadius waveMem
  have smallCubeNegClosed : ∀ {wave},
      wave ∈ integerWaveFrequencyCube smallRadius →
        waveNeg wave ∈ integerWaveFrequencyCube smallRadius := by
    intro wave waveMem
    rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem ⊢
    intro coordinate
    have coordinateMem := Finset.mem_Icc.mp (waveMem coordinate)
    apply Finset.mem_Icc.mpr
    constructor
    · simpa [waveNeg] using neg_le_neg coordinateMem.2
    · simpa [waveNeg] using neg_le_neg coordinateMem.1
  have finishEq : windowFinish = windowStart + scale ^ 2 * timeLength := by
    dsimp only [scale]
    rw [show level⁻¹ ^ 2 = (level ^ 2)⁻¹ by rw [inv_pow]]
    field_simp [levelPos.ne']
    nlinarith [durationEq]
  have originalContinuous : ContinuousOn originalPath
      (Icc windowStart windowFinish) :=
    (wholeRestartPrefixPhysicalTrajectory_continuousOn initial length).mono
      (Icc_subset_Icc windowStartNonneg windowFinishLe)
  have differenceContinuous : ContinuousOn differencePath
      (Icc windowStart windowFinish) := by
    dsimp only [differencePath, originalPath]
    exact originalContinuous.sub
      ((complexSharpSupportProjection_continuous_local
        (integerWaveFrequencyCube smallRadius)).comp_continuousOn
          originalContinuous)
  have fieldIntegrable :=
    finiteVelocityFieldBallMass_intervalIntegrable_of_continuousOn
      differencePath (wholeRestartModes largeRadius) center scale
      spatialRadius windowStart windowFinish windowStartLeFinish
      differenceContinuous
  have coefficientIntegrable :=
    finiteVelocityCoefficientMass_intervalIntegrable_of_continuousOn
      differencePath (wholeRestartModes largeRadius) windowStart windowFinish
      windowStartLeFinish differenceContinuous
  have originalRealityAE :=
    wholeRestartPrefixPhysicalTrajectory_fourierReality_ae initial length
  have windowSubset :
      Icc windowStart windowFinish ⊆ Icc 0 (elapsedTime initial length) :=
    Icc_subset_Icc windowStartNonneg windowFinishLe
  have differenceRealityAE : ∀ᵐ time : Real
      ∂volume.restrict (Icc windowStart windowFinish),
        FiniteStateFourierReality (differencePath time) := by
    have windowReality :=
      ae_mono (Measure.restrict_mono windowSubset le_rfl) originalRealityAE
    filter_upwards [windowReality] with time timeReality
    dsimp only [differencePath, originalPath]
    exact finiteStateFourierReality_sub_projection
      (integerWaveFrequencyCube smallRadius) smallCubeNegClosed _ timeReality
  have physicalCover :=
    scaledFiniteVelocityField_spacetime_ball_mass_le_cellCover_originalReality
      (wholeRestartModes largeRadius) largeNegClosed differencePath center
      centerMem windowStart windowFinish scale timeLength spatialRadius
      scalePos scaleLeOne timeLengthNonneg spatialRadiusNonneg finishEq
      coverRadius coverRadiusLarge differenceRealityAE fieldIntegrable
      coefficientIntegrable
  have tailIntegrable :=
    wholeRestartPrefix_cubeComplementMass_intervalIntegrable initial length
      smallRadius windowStart windowFinish windowStartNonneg
      windowStartLeFinish windowFinishLe
  have weightedLeTail :
      (2 * Real.pi) ^ 2 * (((smallRadius + 1 : Nat) : Real) ^ 2) *
          (∫ time in windowStart..windowFinish, velocityMass time) ≤
        ∫ time in windowStart..windowFinish, tailMass time := by
    have leftIntegrable : IntervalIntegrable
        (fun time =>
          ((2 * Real.pi) ^ 2 *
            (((smallRadius + 1 : Nat) : Real) ^ 2)) *
              velocityMass time)
        volume windowStart windowFinish :=
      coefficientIntegrable.const_mul
        ((2 * Real.pi) ^ 2 *
          (((smallRadius + 1 : Nat) : Real) ^ 2))
    have pointwise : ∀ᵐ time
        ∂volume.restrict (Icc windowStart windowFinish),
        ((2 * Real.pi) ^ 2 *
          (((smallRadius + 1 : Nat) : Real) ^ 2)) *
            velocityMass time ≤ tailMass time := by
      filter_upwards with time
      have hodge := finiteVelocityProjectionDifferenceMass_weighted_le
        (wholeRestartModes largeRadius)
        (zero_not_mem_puncturedIntegerWaveFrequencyCube largeRadius)
        smallRadius (originalPath time)
        (wholeRestartPrefixPhysicalTrajectory_transverse
          initial length time)
      have stateZero :=
        wholeRestartPrefixPhysicalTrajectory_zero_row initial length time
      have projectionEq :
          complexSharpSupportProjection
              (integerWaveFrequencyCube smallRadius) (originalPath time) =
            complexSharpSupportProjection
              (wholeRestartModes smallRadius) (originalPath time) := by
        dsimp only [wholeRestartModes, puncturedIntegerWaveFrequencyCube]
        exact (complexSharpSupportProjection_erase_zero_eq
          (integerWaveFrequencyCube smallRadius) (originalPath time)
            stateZero).symm
      have finiteTail := finiteProjectionDifferenceMass_le_cubeComplement
        smallRadius largeRadius (originalPath time) stateZero
      calc
        ((2 * Real.pi) ^ 2 *
            (((smallRadius + 1 : Nat) : Real) ^ 2)) *
              velocityMass time ≤
            finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes largeRadius) (differencePath time) := by
          simpa only [velocityMass, differencePath] using hodge
        _ = finiteStateVorticityCoefficientEnstrophy
              (wholeRestartModes largeRadius)
              (originalPath time -
                complexSharpSupportProjection
                  (wholeRestartModes smallRadius) (originalPath time)) := by
          dsimp only [differencePath]
          rw [projectionEq]
        _ ≤ tailMass time := by
          simpa only [tailMass] using finiteTail
    have integrated := intervalIntegral.integral_mono_ae_restrict
      windowStartLeFinish leftIntegrable tailIntegrable pointwise
    rw [intervalIntegral.integral_const_mul] at integrated
    exact integrated
  have tailPayment :=
    wholeRestartPrefix_scaledCubeComplement_spacetimeTail_le_gradientCeiling
      initial length windowStart windowFinish level smallBand gradientCeiling
      windowStartNonneg windowStartLeFinish windowFinishLe levelPos
      smallBandPos gradientIntegrable gradientPayment
  have ratioLeRadius : smallBand / scale ≤ (smallRadius : Real) := by
    dsimp only [smallRadius]
    exact Nat.le_ceil _
  have smallBandLeRadius : smallBand ≤ scale * (smallRadius : Real) := by
    simpa only [mul_comm] using (div_le_iff₀ scalePos).mp ratioLeRadius
  have smallBandLeFrequency :
      smallBand ≤ scale * (((smallRadius + 1 : Nat) : Real)) := by
    have radiusLeSucc :
        (smallRadius : Real) ≤ ((smallRadius + 1 : Nat) : Real) := by
      exact_mod_cast Nat.le_succ smallRadius
    exact smallBandLeRadius.trans
      (mul_le_mul_of_nonneg_left radiusLeSucc scalePos.le)
  have velocityIntegralNonneg :
      0 ≤ ∫ time in windowStart..windowFinish, velocityMass time := by
    apply intervalIntegral.integral_nonneg_of_forall windowStartLeFinish
    intro time
    dsimp only [velocityMass]
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg _
  have tailPaid :
      scale⁻¹ *
          (∫ time in windowStart..windowFinish, tailMass time) ≤
        gradientCeiling / smallBand ^ 2 := by
    simpa only [scale, tailMass, smallRadius, originalPath, inv_inv] using
      tailPayment
  have coefficientPayment :
      scale⁻¹ ^ 3 *
          (∫ time in windowStart..windowFinish, velocityMass time) ≤
        gradientCeiling / ((2 * Real.pi) ^ 2 * smallBand ^ 4) := by
    let frequencyConstant : Real := (2 * Real.pi) ^ 2
    let frequency : Real := ((smallRadius + 1 : Nat) : Real)
    let velocityIntegral : Real :=
      ∫ time in windowStart..windowFinish, velocityMass time
    let tailIntegral : Real :=
      ∫ time in windowStart..windowFinish, tailMass time
    have frequencyConstantPos : 0 < frequencyConstant := by
      dsimp only [frequencyConstant]
      positivity
    have frequencySq :
        smallBand ^ 2 ≤ scale ^ 2 * frequency ^ 2 := by
      dsimp only [frequency]
      nlinarith [smallBandLeFrequency]
    have first :
        frequencyConstant * smallBand ^ 2 * scale⁻¹ ^ 3 *
            velocityIntegral ≤
          scale⁻¹ *
            (frequencyConstant * frequency ^ 2 * velocityIntegral) := by
      have paid := mul_le_mul_of_nonneg_right frequencySq
        (mul_nonneg frequencyConstantPos.le velocityIntegralNonneg)
      field_simp [scalePos.ne'] at paid ⊢
      nlinarith
    have second :
        scale⁻¹ *
            (frequencyConstant * frequency ^ 2 * velocityIntegral) ≤
          scale⁻¹ * tailIntegral :=
      mul_le_mul_of_nonneg_left
        (by simpa only [frequencyConstant, frequency, velocityIntegral,
          tailIntegral] using weightedLeTail)
        (inv_nonneg.mpr scalePos.le)
    have combined :
        frequencyConstant * smallBand ^ 2 * scale⁻¹ ^ 3 *
            velocityIntegral ≤ gradientCeiling / smallBand ^ 2 :=
      first.trans (second.trans (by
        simpa only [velocityIntegral, tailIntegral] using tailPaid))
    have multiplied :=
      mul_le_mul_of_nonneg_left combined (sq_nonneg smallBand)
    field_simp [scalePos.ne', smallBandPos.ne', frequencyConstantPos.ne']
      at multiplied ⊢
    dsimp only [frequencyConstant, velocityIntegral] at multiplied ⊢
    ring_nf at multiplied ⊢
    exact multiplied
  have cylinderEq :
      (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
          ‖largeProfile point - smallProfile point‖ ^ 2) =
        ∫ scaledTime in (0 : Real)..timeLength,
          ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
            ‖scale •
              finiteRealComplexFourierField
                (wholeRestartModes largeRadius)
                (finiteStateVelocityCoefficient
                  (differencePath
                    (windowStart + scale ^ 2 * scaledTime)))
                (center + scale • x)‖ ^ 2 := by
    let g : Real → PhysicalSpace → Real := fun scaledTime x =>
      ‖scale •
        finiteRealComplexFourierField
          (wholeRestartModes largeRadius)
          (finiteStateVelocityCoefficient
            (differencePath (windowStart + scale ^ 2 * scaledTime)))
          (center + scale • x)‖ ^ 2
    calc
      (∫ point : ScaledPhysicalCylinder timeLength spatialRadius,
          ‖largeProfile point - smallProfile point‖ ^ 2) =
          ∫ scaledTime : Icc (0 : Real) timeLength,
            ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              ‖largeProfile ⟨scaledTime, x⟩ -
                smallProfile ⟨scaledTime, x⟩‖ ^ 2 :=
        scaledPhysicalCylinder_bcf_sub_integral_eq_subtype
          timeLength spatialRadius largeProfile smallProfile
      _ = ∫ scaledTime : Icc (0 : Real) timeLength,
            ∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime.1 x.1 := by
        apply integral_congr_ae
        filter_upwards with scaledTime
        apply integral_congr_ae
        filter_upwards with x
        let point : ScaledPhysicalCylinder timeLength spatialRadius :=
          ⟨scaledTime, x⟩
        rw [show largeProfile point =
              scale • finiteRealComplexFourierField
                (integerWaveFrequencyCube largeRadius)
                (finiteStateVelocityCoefficient
                  (originalPath
                    (windowStart + scale ^ 2 * scaledTime.1)))
                (center + scale • x.1) by
              simpa only [scale, largeRadius, originalPath, point] using
                largeProfileEq point,
            show smallProfile point =
              scale • finiteRealComplexFourierField
                (integerWaveFrequencyCube smallRadius)
                (finiteStateVelocityCoefficient
                  (originalPath
                    (windowStart + scale ^ 2 * scaledTime.1)))
                (center + scale • x.1) by
              simpa only [scale, smallRadius, originalPath, point] using
                smallProfileEq point]
        rw [← smul_sub]
        rw [finiteRealComplexFourierVelocityField_nested_sub_eq cubeSubset]
        have velocityZero :
            finiteStateVelocityCoefficient
              (differencePath
                (windowStart + scale ^ 2 * scaledTime.1)) 0 = 0 := by
          simp [finiteStateVelocityCoefficient]
        rw [finiteRealComplexFourierField_cube_eq_punctured_of_zero
          largeRadius _ velocityZero]
      _ = ∫ scaledTime in (0 : Real)..timeLength,
            ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime x := by
        have inner (scaledTime : Icc (0 : Real) timeLength) :
            (∫ x : Metric.closedBall (0 : PhysicalSpace) spatialRadius,
                g scaledTime.1 x.1) =
              ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
                g scaledTime.1 x := by
          rw [MeasureTheory.integral_subtype
            (isCompact_closedBall _ _).measurableSet]
        simp_rw [inner]
        rw [MeasureTheory.integral_subtype measurableSet_Icc
          (fun scaledTime =>
            ∫ x in Metric.closedBall (0 : PhysicalSpace) spatialRadius,
              g scaledTime x)]
        rw [intervalIntegral.integral_of_le timeLengthNonneg]
        exact MeasureTheory.integral_Icc_eq_integral_Ioc
      _ = _ := by rfl
  rw [boundedContinuousFunction_toLp_sub_norm_sq_eq_integral volume]
  rw [cylinderEq]
  calc
    _ ≤ ((integerWaveFrequencyCube coverRadius).card : Real) * scale⁻¹ ^ 3 *
        (∫ time in windowStart..windowFinish, velocityMass time) := by
      simpa only [velocityMass] using physicalCover
    _ ≤ ((integerWaveFrequencyCube coverRadius).card : Real) *
        (gradientCeiling /
          ((2 * Real.pi) ^ 2 * smallBand ^ 4)) := by
      have coverNonneg :
          0 ≤ ((integerWaveFrequencyCube coverRadius).card : Real) := by
        exact_mod_cast Nat.zero_le
          (integerWaveFrequencyCube coverRadius).card
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left coefficientPayment coverNonneg
    _ = ((integerWaveFrequencyCube coverRadius).card : Real) *
        gradientCeiling /
          ((2 * Real.pi) ^ 2 * smallBand ^ 4) := by ring

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
end NavierStokes
end SaturationMonoid
