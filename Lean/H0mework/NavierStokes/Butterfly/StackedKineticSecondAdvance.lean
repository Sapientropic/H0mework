import H0mework.NavierStokes.Butterfly.StackedKineticAdvance

/-!
# Second source-generated kinetic advance of the stacked butterfly

The first root transition leaves the actual compiler-owned successor with
the same two paying rows and a strict self-work margin.  This file feeds that
literal successor back through the canonical barrier and the same
standing-valued kinetic valuation.  No second current, contact or branch is
selected by a caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped BigOperators

namespace SaturationMonoid
namespace NavierStokes
namespace RationalVorticityEvaluator
namespace ButterflyStackedKineticSecondAdvance

open Set
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ButterflyStackedExpansionMaterial
open ButterflyStackedSourceCurrent
open ButterflyStackedKineticAdvance

noncomputable section

abbrev stackedStageOneCurrent :
    GeneratedWholeRestartCurrent butterflyGainViscosity :=
  run stackedShortCurrent 1

theorem stackedStageOneCurrent_eq_next :
    stackedStageOneCurrent = stackedShortCurrent.next := by
  change run stackedShortCurrent 1 = stackedShortCurrent.next
  rw [show (1 : Nat) = 0 + 1 by omega, run_succ]
  rfl

theorem stackedStageOneCurrent_ceiling_one_le :
    (1 : Real) ≤
      wholeRestartCoefficientCeiling stackedStageOneCurrent.contact := by
  have positive := wholeRestartCoefficientCeiling_pos
    stackedStageOneCurrent.contact
  have natPositive : 0 <
      wholeRestartCoefficientLevel stackedStageOneCurrent.contact := by
    unfold wholeRestartCoefficientCeiling at positive
    exact_mod_cast positive
  unfold wholeRestartCoefficientCeiling
  exact_mod_cast natPositive

theorem stackedStageOneCurrent_ceiling_le_eighty_nine :
    wholeRestartCoefficientCeiling stackedStageOneCurrent.contact ≤ 89 := by
  have massLe := nextContact_coefficientMass_le stackedShortCurrent
  have rawLe : wholeRestartRawCoefficientCeiling
      stackedStageOneCurrent.contact ≤ (89 : Real) := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    rw [stackedStageOneCurrent_eq_next]
    change wholeVorticityEuclideanMass
        stackedShortCurrent.nextContact.physicalState + 1 ≤ 89
    rw [stackedShortCurrent_ceiling_eq_eighty_eight] at massLe
    linarith
  unfold wholeRestartCoefficientCeiling wholeRestartCoefficientLevel
  exact_mod_cast Nat.ceil_le.mpr rawLe

theorem stackedStageOneCurrent_duration_lt_inverse_ten_pow_thirty :
    wholeRestartDuration stackedStageOneCurrent.contact <
      1 / (10 : Real) ^ 30 := by
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier
    stackedStageOneCurrent
  let ceiling := wholeRestartCoefficientCeiling
    stackedStageOneCurrent.contact
  have ceilingLower : (1 : Real) ≤ ceiling :=
    stackedStageOneCurrent_ceiling_one_le
  have seventhPos : 0 <
      sourceOwnedWholeStateBarrierSeventhCoefficient
        butterflyGainViscosity :=
    sourceOwnedWholeStateBarrierSeventhCoefficient_pos _
  have powerLower : (1 : Real) ^ 7 ≤ ceiling ^ 7 := by
    exact pow_le_pow_left₀ (by norm_num) ceilingLower 7
  have denominatorLower :
      2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * (1 : Real) ^ 7 + 1) ≤
        2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * ceiling ^ 7 + 1) := by
    gcongr
  have sourceDenominatorPos : 0 <
      2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * (1 : Real) ^ 7 + 1) := by
    positivity
  have reciprocalLe :
      1 / (2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * ceiling ^ 7 + 1)) ≤
        1 / (2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * (1 : Real) ^ 7 + 1)) :=
    one_div_le_one_div_of_le sourceDenominatorPos denominatorLower
  have numeric :
      1 / (2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
              butterflyGainViscosity * (1 : Real) ^ 7 + 1)) <
        1 / (10 : Real) ^ 30 := by
    rw [butterflyGainSeventhCoefficient_eq]
    norm_num
  dsimp only [ceiling] at reciprocalLe
  exact durationLe.trans_lt (reciprocalLe.trans_lt numeric)

theorem butterflyGain_viscosity_mul_eighty_nine_lt_one :
    butterflyGainViscosity.coeff * 89 < (1 : Real) := by
  unfold butterflyGainViscosity
  have piSq : (9 : Real) < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have denominatorPos : 0 < (2 * Real.pi) ^ 2 := by positivity
  rw [show ((1 / 100 : Real) / (2 * Real.pi) ^ 2) * 89 =
      (89 / 100 : Real) / (2 * Real.pi) ^ 2 by ring]
  apply (div_lt_iff₀ denominatorPos).2
  nlinarith

theorem stackedStageOneCurrent_wholeTangentSourceUpper_lt_two :
    fullReplayWholeTangentSquareSourceUpper stackedStageOneCurrent < 2 := by
  let ceiling := wholeRestartCoefficientCeiling
    stackedStageOneCurrent.contact
  have cubicLt := butterflyGain_cubicTangentConstant_lt_two_billion
  have durationLt :=
    stackedStageOneCurrent_duration_lt_inverse_ten_pow_thirty
  have ceilingLe : ceiling ≤ 89 :=
    stackedStageOneCurrent_ceiling_le_eighty_nine
  have viscosityLt : butterflyGainViscosity.coeff * ceiling < 1 :=
    (mul_le_mul_of_nonneg_left ceilingLe
      butterflyGainViscosity.coeff_pos.le).trans_lt
        butterflyGain_viscosity_mul_eighty_nine_lt_one
  unfold fullReplayWholeTangentSquareSourceUpper
  have cubicCoefficientNonneg :
      0 ≤ (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
        (2 * (butterflyGainViscosity.coeff ^ 2 *
          (2 * Real.pi) ^ 2)) := by positivity
  have durationNonneg :=
    (wholeRestartDuration_pos stackedStageOneCurrent.contact).le
  have ceilingNonneg : 0 ≤ ceiling :=
    (wholeRestartCoefficientCeiling_pos _).le
  have ceilingCubeLe : ceiling ^ 3 ≤ (89 : Real) ^ 3 := by
    exact pow_le_pow_left₀ ceilingNonneg ceilingLe 3
  have cubeDurationLt : ceiling ^ 3 *
      wholeRestartDuration stackedStageOneCurrent.contact <
        (89 : Real) ^ 3 * (1 / (10 : Real) ^ 30) := by
    calc
      ceiling ^ 3 * wholeRestartDuration stackedStageOneCurrent.contact ≤
          (89 : Real) ^ 3 *
            wholeRestartDuration stackedStageOneCurrent.contact :=
        mul_le_mul_of_nonneg_right ceilingCubeLe durationNonneg
      _ < (89 : Real) ^ 3 * (1 / (10 : Real) ^ 30) :=
        mul_lt_mul_of_pos_left durationLt (by norm_num)
  have cubicTermLt :
      ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
          (2 * (butterflyGainViscosity.coeff ^ 2 *
            (2 * Real.pi) ^ 2))) *
          (ceiling ^ 3 *
            wholeRestartDuration stackedStageOneCurrent.contact) < 1 := by
    calc
      _ ≤ (2000000000 : Real) *
          (ceiling ^ 3 *
            wholeRestartDuration stackedStageOneCurrent.contact) :=
        mul_le_mul_of_nonneg_right cubicLt.le
          (mul_nonneg (pow_nonneg ceilingNonneg 3) durationNonneg)
      _ < (2000000000 : Real) *
          ((89 : Real) ^ 3 * (1 / (10 : Real) ^ 30)) :=
        mul_lt_mul_of_pos_left cubeDurationLt (by norm_num)
      _ < 1 := by norm_num
  dsimp only [ceiling] at viscosityLt cubicTermLt ⊢
  linarith

theorem stackedStageOneCurrent_sourceKineticDrift_lt_inverse_ten_pow_fourteen :
    Real.sqrt
        (3 * wholeRestartDuration stackedStageOneCurrent.contact *
          fullReplayWholeTangentSquareSourceUpper stackedStageOneCurrent) <
      1 / (10 : Real) ^ 14 := by
  apply (Real.sqrt_lt' (by positivity)).2
  have durationLt :=
    stackedStageOneCurrent_duration_lt_inverse_ten_pow_thirty
  have tangentLt := stackedStageOneCurrent_wholeTangentSourceUpper_lt_two
  have tangentNonneg :
      0 ≤ fullReplayWholeTangentSquareSourceUpper stackedStageOneCurrent :=
    (fullReplayWholeTangentSquare_le_sourceUpper
      stackedStageOneCurrent).trans' (sq_nonneg _)
  have durationNonneg :=
    (wholeRestartDuration_pos stackedStageOneCurrent.contact).le
  nlinarith

theorem stackedStageOneCurrent_kineticVelocityRadius_lt_seventeen :
    fullReplayKineticVelocityRadius stackedStageOneCurrent < 17 := by
  unfold fullReplayKineticVelocityRadius
  apply (Real.sqrt_lt' (by norm_num)).2
  have ceilingLe := stackedStageOneCurrent_ceiling_le_eighty_nine
  nlinarith

theorem stackedStageOneSideband_kineticTangentSourceUpper_lt_one_hundredth
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    fullReplayKineticTangentSourceUpper stackedStageOneCurrent wave <
      1 / 100 := by
  have piLt : Real.pi < 4 := Real.pi_lt_four
  have sqrtLt := stackedSideband_sqrtNormSq_lt_five wave waveMem
  have radiusLt :=
    stackedStageOneCurrent_kineticVelocityRadius_lt_seventeen
  have dampingLt := stackedSideband_damping_lt_one wave waveMem
  have driftLt :=
    stackedStageOneCurrent_sourceKineticDrift_lt_inverse_ten_pow_fourteen
  have outerNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) := by
    positivity
  have radiusNonneg :=
    fullReplayKineticVelocityRadius_nonneg stackedStageOneCurrent
  have dampingNonneg :
      0 ≤ butterflyGainViscosity.coeff *
        integerWaveViscousMultiplier wave := by
    exact mul_nonneg butterflyGainViscosity.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have driftNonneg :
      0 ≤ Real.sqrt
        (3 * wholeRestartDuration stackedStageOneCurrent.contact *
          fullReplayWholeTangentSquareSourceUpper stackedStageOneCurrent) :=
    Real.sqrt_nonneg _
  unfold fullReplayKineticTangentSourceUpper
  let outer := (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)
  let radius := fullReplayKineticVelocityRadius stackedStageOneCurrent
  let damping := butterflyGainViscosity.coeff *
    integerWaveViscousMultiplier wave
  let drift := Real.sqrt
    (3 * wholeRestartDuration stackedStageOneCurrent.contact *
      fullReplayWholeTangentSquareSourceUpper stackedStageOneCurrent)
  change outer * ((outer * (2 * radius) + damping) * drift) < 1 / 100
  rw [← mul_assoc]
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
      (wholeRestartCoefficientCeiling_pos stackedStageOneCurrent.contact)
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
  have driftLt' : drift < 1 / (10 : Real) ^ 14 := by
    simpa only [drift] using driftLt
  have productNonneg :
      0 ≤ outer * (outer * (2 * radius) + damping) := by
    exact mul_nonneg outerNonneg coefficientNonneg
  calc
    outer * (outer * (2 * radius) + damping) * drift ≤
        (120 * 4081) * drift :=
      mul_le_mul_of_nonneg_right outerCoefficientLt.le driftNonneg
    _ < (120 * 4081) * (1 / (10 : Real) ^ 14) :=
      mul_lt_mul_of_pos_left driftLt' (by norm_num)
    _ < 1 / 100 := by norm_num

theorem stackedStageOneSideband_currentRow_norm_lt_eleven
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    ‖stackedStageOneCurrent.contact.physicalState wave‖ < 11 := by
  have displacement :=
    stackedSideband_nextContactRow_sub_current_norm_lt_inverse_ten_pow_seventeen
      wave waveMem
  have sourceLt := stackedSideband_currentRow_norm_lt_ten wave
  rw [stackedStageOneCurrent_eq_next]
  change ‖stackedShortCurrent.nextContact.physicalState wave‖ < 11
  calc
    ‖stackedShortCurrent.nextContact.physicalState wave‖ =
        ‖(stackedShortCurrent.nextContact.physicalState wave -
            stackedShortCurrent.contact.physicalState wave) +
          stackedShortCurrent.contact.physicalState wave‖ := by
      congr 1
      module
    _ ≤
        ‖stackedShortCurrent.nextContact.physicalState wave -
          stackedShortCurrent.contact.physicalState wave‖ +
        ‖stackedShortCurrent.contact.physicalState wave‖ := norm_add_le _ _
    _ < 1 / (10 : Real) ^ 17 + 10 := add_lt_add displacement sourceLt
    _ < 11 := by norm_num

/-- The second literal run edge again owns a positive kinetic density on
the same actual paying face. -/
theorem stackedStageOneSideband_kineticPaymentDensity_pos
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    0 < nextContactKineticEulerPaymentDensity
      stackedStageOneCurrent wave := by
  have workGt : 11 < complexCoordinateRealInner
      (stackedStageOneCurrent.contact.physicalState wave)
      (wholeLatticeVorticityFourierTangentAt
        butterflyGainViscosity.coeff
        stackedStageOneCurrent.contact.physicalState wave) := by
    rw [stackedStageOneCurrent_eq_next]
    exact stackedSideband_nextContact_selfTangentWork_gt_eleven
      wave waveMem
  have normLt := stackedStageOneSideband_currentRow_norm_lt_eleven
    wave waveMem
  have upperLt :=
    stackedStageOneSideband_kineticTangentSourceUpper_lt_one_hundredth
      wave waveMem
  have upperNonneg : 0 ≤
      fullReplayKineticTangentSourceUpper stackedStageOneCurrent wave :=
    (fullReplayKineticTangentDriftUpper_nonneg
      stackedStageOneCurrent wave).trans
        (fullReplayKineticTangentDriftUpper_le_sourceUpper
          stackedStageOneCurrent wave)
  have productLt :
      ‖stackedStageOneCurrent.contact.physicalState wave‖ *
          fullReplayKineticTangentSourceUpper stackedStageOneCurrent wave <
        11 / 100 := by
    calc
      ‖stackedStageOneCurrent.contact.physicalState wave‖ *
            fullReplayKineticTangentSourceUpper stackedStageOneCurrent wave ≤
          11 * fullReplayKineticTangentSourceUpper
            stackedStageOneCurrent wave :=
        mul_le_mul_of_nonneg_right normLt.le upperNonneg
      _ < 11 * (1 / 100 : Real) :=
        mul_lt_mul_of_pos_left upperLt (by norm_num)
      _ = 11 / 100 := by ring
  unfold nextContactKineticEulerPaymentDensity
  nlinarith

def stackedStageOneStanding := runCellStanding stackedShortCurrent 1

def stackedStageOneMaterial :=
  nativeRestartStandingValuedArithmeticMaterial
    (runStandingCellEffect stackedShortCurrent 1)

theorem stackedStageOneStanding_anchorLevel_ge_eighty_eight :
    88 ≤ stackedStageOneStanding.anchorLevel := by
  change 88 ≤ (runCellStanding stackedShortCurrent 1).anchorLevel
  rw [runCellStanding_anchorLevel_eq_initial_add_paymentCount]
  rw [stackedShortCurrent_level_eq_eighty_eight]
  omega

theorem stackedSideband_mem_stageOneAnchorCube
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    wave ∈ wholeRestartModes (stackedStageOneStanding.anchorLevel + 1) := by
  have anchorLower := stackedStageOneStanding_anchorLevel_ge_eighty_eight
  rw [wholeRestartModes, puncturedIntegerWaveFrequencyCube,
    Finset.mem_erase, integerWaveFrequencyCube, Fintype.mem_piFinset]
  constructor
  · exact fun waveZero => stackedSidebandCone.zeroNotMem (waveZero ▸ waveMem)
  · intro coordinate
    simp only [stackedSidebandModes, plusSideband, minusSideband,
      Finset.mem_insert, Finset.mem_singleton] at waveMem
    rcases waveMem with rfl | rfl <;>
      fin_cases coordinate <;>
      norm_num [axisWave, pumpY] at anchorLower ⊢ <;> omega

theorem stackedStageOneResidualExpansion_clock_mul_densitySum_le
    (residual : GeneratedParallelResidualAt stackedStageOneMaterial
      stackedStageOneMaterial.arithmeticMaterial) :
    stackedStageOneCurrent.nextContact.time.1 *
        (∑ wave ∈ stackedSidebandModes,
          nextContactKineticEulerPaymentDensity
            stackedStageOneCurrent wave) ≤
      (stackedStageOneMaterial.generatedResidualExpansion residual
        ).finiteNetEnstrophyDebit := by
  apply NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.clock_mul_sum_kineticDensity_le_finiteNetEnstrophyDebit
  · intro wave waveMem
    exact stackedSideband_mem_stageOneAnchorCube wave waveMem
  · intro wave waveMem
    exact stackedStageOneSideband_kineticPaymentDensity_pos wave waveMem

theorem stackedStageOneSideband_kineticPaymentDensity_sum_pos :
    0 < ∑ wave ∈ stackedSidebandModes,
      nextContactKineticEulerPaymentDensity stackedStageOneCurrent wave := by
  apply Finset.sum_pos'
  · intro wave waveMem
    exact (stackedStageOneSideband_kineticPaymentDensity_pos
      wave waveMem).le
  · refine ⟨plusSideband, by simp [stackedSidebandModes], ?_⟩
    exact stackedStageOneSideband_kineticPaymentDensity_pos plusSideband
      (by simp [stackedSidebandModes])

theorem stackedStageOneResidualExpansion_finiteDebit_pos
    (residual : GeneratedParallelResidualAt stackedStageOneMaterial
      stackedStageOneMaterial.arithmeticMaterial) :
    0 < (stackedStageOneMaterial.generatedResidualExpansion residual
      ).finiteNetEnstrophyDebit := by
  have paid :=
    stackedStageOneResidualExpansion_clock_mul_densitySum_le residual
  have clockPaymentPos : 0 < stackedStageOneCurrent.nextContact.time.1 *
      (∑ wave ∈ stackedSidebandModes,
        nextContactKineticEulerPaymentDensity stackedStageOneCurrent wave) :=
    mul_pos stackedStageOneCurrent.nextContact.time_pos
      stackedStageOneSideband_kineticPaymentDensity_sum_pos
  exact clockPaymentPos.trans_le paid

/-- Whether the first edge was exact or residual, the second root outcome
is paid by its own current material; a pending standing does not freeze the
old effect. -/
noncomputable def stackedStageOne_rootOutcome_isPaid :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    (nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter 1)).IsPaid := by
  dsimp only
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt
      (classicalWholeRestartMediumSource stackedShortCurrent)
      ((classicalWholeRestartMediumSource stackedShortCurrent).stateAfter 1) =
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
        (stackedStageOneResidualExpansion_finiteDebit_pos residual)).elim

theorem stackedStageOne_paidRootStep_factorizes :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source 1)
    HEq (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter 1)).effect stackedStageOneMaterial ∧
      Nonempty (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter 1)).IsPaid ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter 2 := by
  dsimp only
  have factorized :=
    classicalWholeRestart_runStandingEffect_rootStep_factorizes
      stackedShortCurrent 1
  exact ⟨factorized.1, ⟨stackedStageOne_rootOutcome_isPaid⟩,
    factorized.2.2⟩

end

end ButterflyStackedKineticSecondAdvance
end RationalVorticityEvaluator
end NavierStokes
end SaturationMonoid
