import H0mework.Versions.X.NavierStokes.Butterfly.StackedKineticSecondAdvance
import H0mework.NavierStokes.KineticRestart.CumulativeKineticDissipation
import H0mework.NavierStokes.Galerkin.KineticAmbientBound
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.NavierStokes.RationalVorticityEvaluator
namespace ButterflyStackedKineticInvariant

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootArithmeticIncidence
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientStandingValuedKineticPayment
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientNativeFluidMediumRoot
open ButterflyStackedSourceCurrent
open ButterflyStackedKineticAdvance
open ButterflyStackedKineticSecondAdvance

noncomputable section

private theorem coefficientCeiling_one_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    (1 : Real) ≤ wholeRestartCoefficientCeiling current.contact := by
  have positive := wholeRestartCoefficientCeiling_pos current.contact
  have levelPos : 0 < wholeRestartCoefficientLevel current.contact := by
    unfold wholeRestartCoefficientCeiling at positive
    exact_mod_cast positive
  unfold wholeRestartCoefficientCeiling
  exact_mod_cast levelPos

private theorem butterflyGain_duration_mul_ceilingSeventh_le
    (current : GeneratedWholeRestartCurrent butterflyGainViscosity) :
    wholeRestartDuration current.contact *
        wholeRestartCoefficientCeiling current.contact ^ 7 ≤
      1 / (2 * sourceOwnedWholeStateBarrierSeventhCoefficient
        butterflyGainViscosity) := by
  let time := wholeRestartDuration current.contact
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let coefficient := sourceOwnedWholeStateBarrierSeventhCoefficient
    butterflyGainViscosity
  have timeNonneg : 0 ≤ time := (wholeRestartDuration_pos _).le
  have ceilingPos : 0 < ceiling := wholeRestartCoefficientCeiling_pos _
  have coefficientPos : 0 < coefficient := by
    exact sourceOwnedWholeStateBarrierSeventhCoefficient_pos _
  have durationLe := wholeRestartDuration_le_inverse_seventhBarrier current
  have denominatorBasePos : 0 < 2 * (coefficient * ceiling ^ 7) := by
    positivity
  have denominatorLe :
      2 * (coefficient * ceiling ^ 7) ≤
        2 * (coefficient * ceiling ^ 7 + 1) := by linarith
  have reciprocalLe :
      1 / (2 * (coefficient * ceiling ^ 7 + 1)) ≤
        1 / (2 * (coefficient * ceiling ^ 7)) :=
    one_div_le_one_div_of_le denominatorBasePos denominatorLe
  have timeLe : time ≤ 1 / (2 * (coefficient * ceiling ^ 7)) :=
    durationLe.trans reciprocalLe
  have scaled := mul_le_mul_of_nonneg_right timeLe
    (pow_nonneg ceilingPos.le 7)
  dsimp only [time, ceiling, coefficient] at scaled ⊢
  calc
    _ ≤ 1 /
          (2 * (sourceOwnedWholeStateBarrierSeventhCoefficient
            butterflyGainViscosity *
              wholeRestartCoefficientCeiling current.contact ^ 7)) *
        wholeRestartCoefficientCeiling current.contact ^ 7 := scaled
    _ = 1 / (2 * sourceOwnedWholeStateBarrierSeventhCoefficient
          butterflyGainViscosity) := by
      field_simp [coefficientPos.ne']
      apply (div_eq_iff
        (mul_ne_zero coefficientPos.ne' ceilingPos.ne')).2
      change ceiling = (1 / coefficient) * (coefficient * ceiling)
      field_simp [coefficientPos.ne']

private theorem butterflyGain_inverseSeventhHalf_lt_inverse_thirty :
    1 / (2 * sourceOwnedWholeStateBarrierSeventhCoefficient
        butterflyGainViscosity) <
      1 / (10 : Real) ^ 30 := by
  rw [butterflyGainSeventhCoefficient_eq]
  norm_num

private theorem butterflyGain_coeff_lt_one :
    butterflyGainViscosity.coeff < (1 : Real) := by
  have scaled := butterflyGain_viscosity_mul_eighty_eight_lt_one
  nlinarith [butterflyGainViscosity.coeff_pos]

theorem butterflyGain_stackedSideband_weightedKineticError_lt_one_thousandth
    (current : GeneratedWholeRestartCurrent butterflyGainViscosity)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    6 * ‖current.contact.physicalState wave‖ *
        fullReplayKineticTangentSourceUpper current wave <
      1 / 1000 := by
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let time := wholeRestartDuration current.contact
  let coefficient := sourceOwnedWholeStateBarrierSeventhCoefficient
    butterflyGainViscosity
  let cubic :=
    (9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (butterflyGainViscosity.coeff ^ 2 * (2 * Real.pi) ^ 2))
  let tangentUpper := fullReplayWholeTangentSquareSourceUpper current
  let tangentBlock := 3 * time * tangentUpper
  let drift := Real.sqrt tangentBlock
  let outer := (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave)
  let radius := fullReplayKineticVelocityRadius current
  let damping := butterflyGainViscosity.coeff *
    integerWaveViscousMultiplier wave
  have ceilingOne : (1 : Real) ≤ ceiling := coefficientCeiling_one_le current
  have ceilingPos : 0 < ceiling := lt_of_lt_of_le (by norm_num) ceilingOne
  have timePos : 0 < time := wholeRestartDuration_pos _
  have coefficientPos : 0 < coefficient := by
    exact sourceOwnedWholeStateBarrierSeventhCoefficient_pos _
  have cubicNonneg : 0 ≤ cubic := by
    dsimp only [cubic]
    positivity
  have tangentUpperNonneg : 0 ≤ tangentUpper :=
    (fullReplayWholeTangentSquare_le_sourceUpper current).trans'
      (sq_nonneg _)
  have tangentBlockNonneg : 0 ≤ tangentBlock := by
    dsimp only [tangentBlock]
    positivity
  have durationScaled := butterflyGain_duration_mul_ceilingSeventh_le current
  have durationScaleLt : time * ceiling ^ 7 < 1 / (10 : Real) ^ 30 :=
    durationScaled.trans_lt
      butterflyGain_inverseSeventhHalf_lt_inverse_thirty
  have timeLeScaled : time ≤ time * ceiling ^ 7 := by
    have oneLePower : (1 : Real) ≤ ceiling ^ 7 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 1)
        ceilingOne 7
    calc
      time = time * 1 := by ring
      _ ≤ time * ceiling ^ 7 :=
        mul_le_mul_of_nonneg_left oneLePower timePos.le
  have timeLt : time < 1 / (10 : Real) ^ 30 :=
    timeLeScaled.trans_lt durationScaleLt
  have timeScaledNonneg : 0 ≤ time * ceiling ^ 7 := by positivity
  have timeScaledLeOne : time * ceiling ^ 7 ≤ 1 := by
    exact durationScaleLt.le.trans (by norm_num)
  have timeLeOne : time ≤ 1 := timeLeScaled.trans timeScaledLeOne
  have ceilingFiveLeSeven : ceiling ^ 5 ≤ ceiling ^ 7 := by
    rw [show ceiling ^ 7 = ceiling ^ 5 * ceiling ^ 2 by ring]
    have oneLeSquare : (1 : Real) ≤ ceiling ^ 2 := by nlinarith
    exact le_mul_of_one_le_right (pow_nonneg ceilingPos.le 5) oneLeSquare
  have timeCeilingFiveLe : time * ceiling ^ 5 ≤
      1 / (10 : Real) ^ 30 := by
    calc
      time * ceiling ^ 5 ≤ time * ceiling ^ 7 :=
        mul_le_mul_of_nonneg_left ceilingFiveLeSeven timePos.le
      _ ≤ 1 / (10 : Real) ^ 30 := durationScaleLt.le
  have timeSqCeilingSevenLe : time ^ 2 * ceiling ^ 7 ≤
      1 / (10 : Real) ^ 30 := by
    rw [show time ^ 2 * ceiling ^ 7 = time * (time * ceiling ^ 7) by ring]
    calc
      time * (time * ceiling ^ 7) ≤ 1 * (time * ceiling ^ 7) :=
        mul_le_mul_of_nonneg_right timeLeOne timeScaledNonneg
      _ ≤ 1 * (1 / (10 : Real) ^ 30) :=
        mul_le_mul_of_nonneg_left durationScaleLt.le (by norm_num)
      _ = _ := by ring
  have cubicLt : cubic < 2000000000 := by
    exact butterflyGain_cubicTangentConstant_lt_two_billion
  have viscosityLt : butterflyGainViscosity.coeff < 1 :=
    butterflyGain_coeff_lt_one
  have tangentBlockCeilingFourEq :
      tangentBlock * ceiling ^ 4 =
        3 * cubic * (time ^ 2 * ceiling ^ 7) +
          3 * butterflyGainViscosity.coeff *
            (time * ceiling ^ 5) := by
    dsimp only [tangentBlock, tangentUpper,
      fullReplayWholeTangentSquareSourceUpper, time, ceiling, cubic]
    ring
  have tangentBlockCeilingFourLt :
      tangentBlock * ceiling ^ 4 < 1 / (10 : Real) ^ 20 := by
    rw [tangentBlockCeilingFourEq]
    have firstLe :
        3 * cubic * (time ^ 2 * ceiling ^ 7) ≤
          3 * 2000000000 * (1 / (10 : Real) ^ 30) := by
      gcongr
    have secondLe :
        3 * butterflyGainViscosity.coeff * (time * ceiling ^ 5) ≤
          3 * 1 * (1 / (10 : Real) ^ 30) := by
      gcongr
    calc
      _ ≤ 3 * 2000000000 * (1 / (10 : Real) ^ 30) +
          3 * 1 * (1 / (10 : Real) ^ 30) := add_le_add firstLe secondLe
      _ < 1 / (10 : Real) ^ 20 := by norm_num
  have driftScaledSquare : (ceiling ^ 2 * drift) ^ 2 =
      tangentBlock * ceiling ^ 4 := by
    dsimp only [drift]
    rw [mul_pow, Real.sq_sqrt tangentBlockNonneg]
    ring
  have driftScaledNonneg : 0 ≤ ceiling ^ 2 * drift := by positivity
  have driftScaledLt : ceiling ^ 2 * drift < 1 / (10 : Real) ^ 10 := by
    have squareLt : (ceiling ^ 2 * drift) ^ 2 <
        (1 / (10 : Real) ^ 10) ^ 2 := by
      rw [driftScaledSquare]
      norm_num at tangentBlockCeilingFourLt ⊢
      exact tangentBlockCeilingFourLt
    nlinarith [sq_nonneg
      (ceiling ^ 2 * drift + 1 / (10 : Real) ^ 10)]
  have outerLt : outer < 100 := by
    dsimp only [outer]
    have sqrtLt := stackedSideband_sqrtNormSq_lt_twenty_five_sixths
      wave waveMem
    calc
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) <
          (6 * Real.pi) * (25 / 6) :=
        mul_lt_mul_of_pos_left sqrtLt
          (mul_pos (by norm_num) Real.pi_pos)
      _ < 6 * 4 * (25 / 6) := by nlinarith [Real.pi_pos, Real.pi_lt_four]
      _ = 100 := by norm_num
  have outerNonneg : 0 ≤ outer := by dsimp only [outer]; positivity
  have dampingLt : damping < 1 := by
    simpa only [damping] using stackedSideband_damping_lt_one wave waveMem
  have dampingNonneg : 0 ≤ damping := by
    dsimp only [damping]
    exact mul_nonneg butterflyGainViscosity.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave))
  have sqrtCeilingLe : Real.sqrt ceiling ≤ ceiling :=
    Real.sqrt_le_self_iff.mpr (Or.inr ceilingOne)
  have radiusLe : radius ≤ 3 * ceiling := by
    dsimp only [radius, fullReplayKineticVelocityRadius]
    have threeCeilingOne : 1 ≤ 3 * ceiling := by nlinarith
    have sqrtSelf := Real.sqrt_le_self_iff.mpr (Or.inr threeCeilingOne)
    exact sqrtSelf
  have radiusNonneg : 0 ≤ radius :=
    fullReplayKineticVelocityRadius_nonneg current
  have coefficientLe : outer * (2 * radius) + damping ≤
      601 * ceiling := by
    have twoRadiusLe : 2 * radius ≤ 6 * ceiling :=
      by
        have scaled := mul_le_mul_of_nonneg_left radiusLe
          (show (0 : Real) ≤ 2 by norm_num)
        nlinarith
    have outerRadiusLe : outer * (2 * radius) ≤ 100 * (6 * ceiling) :=
      mul_le_mul outerLt.le twoRadiusLe
        (mul_nonneg (by norm_num) radiusNonneg) (by norm_num)
    have dampingLeCeiling : damping ≤ ceiling :=
      dampingLt.le.trans ceilingOne
    nlinarith
  have coefficientNonneg : 0 ≤ outer * (2 * radius) + damping := by
    positivity
  have sourceUpperLe :
      fullReplayKineticTangentSourceUpper current wave ≤
        60100 * ceiling * drift := by
    unfold fullReplayKineticTangentSourceUpper
    change outer * ((outer * (2 * radius) + damping) * drift) ≤ _
    calc
      outer * ((outer * (2 * radius) + damping) * drift) ≤
          100 * ((601 * ceiling) * drift) := by gcongr
      _ = 60100 * ceiling * drift := by ring
  have stateRowLe : ‖current.contact.physicalState wave‖ ≤ ceiling := by
    have rowLe := lp.norm_apply_le_norm (by norm_num)
      current.contact.physicalState wave
    have stateLe := current_physicalState_norm_le_sqrt_coefficientCeiling
      current
    exact rowLe.trans (stateLe.trans sqrtCeilingLe)
  have sourceUpperNonneg : 0 ≤
      fullReplayKineticTangentSourceUpper current wave :=
    (fullReplayKineticTangentDriftUpper_nonneg current wave).trans
      (fullReplayKineticTangentDriftUpper_le_sourceUpper current wave)
  calc
    6 * ‖current.contact.physicalState wave‖ *
          fullReplayKineticTangentSourceUpper current wave ≤
        6 * ceiling * (60100 * ceiling * drift) := by gcongr
    _ = 360600 * (ceiling ^ 2 * drift) := by ring
    _ < 360600 * (1 / (10 : Real) ^ 10) :=
      mul_lt_mul_of_pos_left driftScaledLt (by norm_num)
    _ < 1 / 1000 := by norm_num

/-- A current-side self-work row above one is automatically a paying row of
the same current's kinetic valuation.  The seventh-order source barrier has
already absorbed every scale-dependent remainder. -/
theorem butterflyGain_stackedSideband_kineticPaymentDensity_pos_of_selfWork
    (current : GeneratedWholeRestartCurrent butterflyGainViscosity)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes)
    (selfWork : 1 < selfTangentWorkAt
      current.contact.physicalState wave) :
    0 < nextContactKineticEulerPaymentDensity current wave := by
  have error :=
    butterflyGain_stackedSideband_weightedKineticError_lt_one_thousandth
      current wave waveMem
  unfold selfTangentWorkAt at selfWork
  unfold nextContactKineticEulerPaymentDensity
  nlinarith

theorem butterflyGain_stackedSideband_kineticPaymentDensity_gt_floor
    (current : GeneratedWholeRestartCurrent butterflyGainViscosity)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes)
    (selfWork : 1 < selfTangentWorkAt
      current.contact.physicalState wave) :
    (1999 / 1000 : Real) <
      nextContactKineticEulerPaymentDensity current wave := by
  have error :=
    butterflyGain_stackedSideband_weightedKineticError_lt_one_thousandth
      current wave waveMem
  unfold selfTangentWorkAt at selfWork
  unfold nextContactKineticEulerPaymentDensity
  nlinarith

/-- Finite recursive invariant read directly from one actual run current.
It stores no future table: at stage `n` it asks only whether the two fixed
source rows still own their current self-work instruction. -/
def ButterflyStackedKineticInvariantAt (stage : Nat) : Prop :=
  ∀ wave ∈ stackedSidebandModes,
    1 < selfTangentWorkAt
      (run stackedShortCurrent stage).contact.physicalState wave

theorem butterflyStackedKineticInvariantAt_zero :
    ButterflyStackedKineticInvariantAt 0 := by
  intro wave waveMem
  have source := (stackedShortContact_sourcePatch.2.2 wave waveMem).2.2
  exact (by norm_num : (1 : Real) < 12).trans source

theorem butterflyStackedKineticInvariantAt_one :
    ButterflyStackedKineticInvariantAt 1 := by
  intro wave waveMem
  have generated := stackedSideband_nextContact_selfTangentWork_gt_eleven
    wave waveMem
  change 1 < selfTangentWorkAt
    (run stackedShortCurrent 1).contact.physicalState wave
  rw [show (1 : Nat) = 0 + 1 by omega, run_succ, next_contact]
  exact (by norm_num : (1 : Real) < 11).trans generated

def stackedRunPayingFaceMass (stage : Nat) : Real :=
  finiteStateVorticityCoefficientEnstrophy stackedSidebandModes
    (run stackedShortCurrent stage).contact.physicalState

theorem stackedRunPayingFaceMass_nonneg (stage : Nat) :
    0 ≤ stackedRunPayingFaceMass stage := by
  unfold stackedRunPayingFaceMass
    finiteStateVorticityCoefficientEnstrophy
  exact Finset.sum_nonneg fun wave _waveMem =>
    complexCoordinateAmplitudeSq_nonneg _

/-- While the finite source invariant is active, the two actual paying rows
pay a uniform multiple of the same edge clock in literal coefficient mass. -/
theorem stackedRunPayingFaceMass_edge_payment
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage) :
    (3998 / 1000 : Real) *
        (run stackedShortCurrent stage).nextContact.time.1 ≤
      stackedRunPayingFaceMass (stage + 1) -
        stackedRunPayingFaceMass stage := by
  let current := run stackedShortCurrent stage
  have rowPayment : ∀ wave ∈ stackedSidebandModes,
      (1999 / 1000 : Real) * current.nextContact.time.1 ≤
        complexCoordinateAmplitudeSq
            (current.nextContact.physicalState wave) -
          complexCoordinateAmplitudeSq
            (current.contact.physicalState wave) := by
    intro wave waveMem
    have densityFloor :=
      butterflyGain_stackedSideband_kineticPaymentDensity_gt_floor
        current wave waveMem (invariant wave waveMem)
    have clockScaled :
        (1999 / 1000 : Real) * current.nextContact.time.1 ≤
          current.nextContact.time.1 *
            nextContactKineticEulerPaymentDensity current wave := by
      rw [mul_comm (1999 / 1000 : Real) current.nextContact.time.1]
      exact mul_le_mul_of_nonneg_left densityFloor.le
        current.nextContact.time_pos.le
    exact clockScaled.trans
      (nextContact_amplitudeSq_sub_current_le_from_below_kineticSource
        current wave (fun waveZero =>
          stackedSidebandCone.zeroNotMem (waveZero ▸ waveMem)))
  have plusPayment := rowPayment plusSideband
    (by simp [stackedSidebandModes])
  have minusPayment := rowPayment minusSideband
    (by simp [stackedSidebandModes])
  unfold stackedRunPayingFaceMass
  rw [run_succ, next_contact]
  unfold finiteStateVorticityCoefficientEnstrophy
  have distinct : plusSideband ≠ minusSideband := by decide
  simp [stackedSidebandModes, distinct]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    at plusPayment minusPayment
  dsimp only [current] at plusPayment minusPayment
  calc
    (3998 / 1000 : Real) *
          (run stackedShortCurrent stage).nextContact.time.1 =
        (1999 / 1000 : Real) *
            (run stackedShortCurrent stage).nextContact.time.1 +
          (1999 / 1000 : Real) *
            (run stackedShortCurrent stage).nextContact.time.1 := by ring
    _ ≤
        (complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).nextContact.physicalState
              plusSideband) -
          complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).contact.physicalState
              plusSideband)) +
        (complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).nextContact.physicalState
              minusSideband) -
          complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).contact.physicalState
              minusSideband)) :=
      add_le_add plusPayment minusPayment
    _ =
        complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).nextContact.physicalState
              plusSideband) +
          complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).nextContact.physicalState
              minusSideband) -
        (complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).contact.physicalState
              plusSideband) +
          complexCoordinateVectorNormSq
            ((run stackedShortCurrent stage).contact.physicalState
              minusSideband)) := by ring

/-- The fixed two-row coefficient mass is uniformly bounded by the initial
whole kinetic ledger. -/
theorem stackedRunPayingFaceMass_le_initialKinetic (stage : Nat) :
    stackedRunPayingFaceMass stage ≤
      finiteModeKineticAmbientFactor stackedSidebandModes *
        puncturedWholeVorticityKineticMass
          stackedShortCurrent.contact.physicalState := by
  have zeroNotMem : (0 : IntegerWavevector) ∉ stackedSidebandModes :=
    stackedSidebandCone.zeroNotMem
  have transverse : FiniteStateTransverseOn stackedSidebandModes
      (run stackedShortCurrent stage).contact.physicalState := by
    intro wave _waveMem
    exact (run stackedShortCurrent stage).contact.transverse wave
  have coefficientLe :=
    finiteStateVorticityCoefficientEnstrophy_le_kineticEnergy_factor
      stackedSidebandModes zeroNotMem
        (run stackedShortCurrent stage).contact.physicalState transverse
  have finiteKineticLe :=
    two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
      stackedSidebandModes zeroNotMem
        (run stackedShortCurrent stage).contact.physicalState transverse
  have finiteKineticNonneg :=
    finiteStateVorticityKineticEnergy_nonneg stackedSidebandModes
      (run stackedShortCurrent stage).contact.physicalState
  have finiteLeWhole :
      finiteStateVorticityKineticEnergy stackedSidebandModes
          (run stackedShortCurrent stage).contact.physicalState ≤
        puncturedWholeVorticityKineticMass
          (run stackedShortCurrent stage).contact.physicalState := by
    linarith
  have runKineticLeInitial :
      puncturedWholeVorticityKineticMass
          (run stackedShortCurrent stage).contact.physicalState ≤
        puncturedWholeVorticityKineticMass
          stackedShortCurrent.contact.physicalState := by
    simpa only [run_zero] using
      (run_contact_kineticMass_antitone stackedShortCurrent)
        (Nat.zero_le stage)
  have factorNonneg :=
    finiteModeKineticAmbientFactor_nonneg stackedSidebandModes
  unfold stackedRunPayingFaceMass
  exact coefficientLe.trans
    ((mul_le_mul_of_nonneg_left finiteLeWhole factorNonneg).trans
      (mul_le_mul_of_nonneg_left runKineticLeInitial factorNonneg))

theorem stackedRunPayingFace_clock_prefix_le
    (length : Nat)
    (invariant : ∀ stage < length,
      ButterflyStackedKineticInvariantAt stage) :
    (3998 / 1000 : Real) *
        (∑ stage ∈ Finset.range length,
          (run stackedShortCurrent stage).nextContact.time.1) ≤
      finiteModeKineticAmbientFactor stackedSidebandModes *
        puncturedWholeVorticityKineticMass
          stackedShortCurrent.contact.physicalState := by
  have edges :
      (∑ stage ∈ Finset.range length,
          (3998 / 1000 : Real) *
            (run stackedShortCurrent stage).nextContact.time.1) ≤
        ∑ stage ∈ Finset.range length,
          (stackedRunPayingFaceMass (stage + 1) -
            stackedRunPayingFaceMass stage) := by
    apply Finset.sum_le_sum
    intro stage stageMem
    exact stackedRunPayingFaceMass_edge_payment stage
      (invariant stage (Finset.mem_range.mp stageMem))
  rw [← Finset.mul_sum] at edges
  have telescope :
      (∑ stage ∈ Finset.range length,
          (stackedRunPayingFaceMass (stage + 1) -
            stackedRunPayingFaceMass stage)) =
        stackedRunPayingFaceMass length - stackedRunPayingFaceMass 0 := by
    simpa using Finset.sum_range_sub
      (fun stage => stackedRunPayingFaceMass stage) length
  rw [telescope] at edges
  have terminalUpper := stackedRunPayingFaceMass_le_initialKinetic length
  have initialNonneg := stackedRunPayingFaceMass_nonneg 0
  linarith

/-- Once the local finite invariant is generated recursively, contact-time
summability is an immediate whole-run fold of the same physical rows.  This
is a subordinate consumer; the final public theorem must generate the
invariant internally rather than expose it as a premise. -/
theorem contactTime_summable_of_butterflyStackedKineticInvariant
    (invariant : ∀ stage : Nat,
      ButterflyStackedKineticInvariantAt stage) :
    Summable fun stage => (run stackedShortCurrent stage).contact.time.1 := by
  have chargePos : (0 : Real) < 3998 / 1000 := by norm_num
  refine summable_of_sum_range_le
    (c := stackedShortCurrent.contact.time.1 +
      (finiteModeKineticAmbientFactor stackedSidebandModes *
        puncturedWholeVorticityKineticMass
          stackedShortCurrent.contact.physicalState) /
        (3998 / 1000 : Real)) ?_ ?_
  · intro stage
    exact (run_contact_time_pos stackedShortCurrent stage).le
  · intro length
    have clockPrefix :
        (3998 / 1000 : Real) *
            (∑ stage ∈ Finset.range length,
              (run stackedShortCurrent stage).nextContact.time.1) ≤
          finiteModeKineticAmbientFactor stackedSidebandModes *
            puncturedWholeVorticityKineticMass
              stackedShortCurrent.contact.physicalState :=
      stackedRunPayingFace_clock_prefix_le length
        (fun stage _stageLt => invariant stage)
    have nextSumEq :
        stackedShortCurrent.contact.time.1 +
            ∑ stage ∈ Finset.range length,
              (run stackedShortCurrent stage).nextContact.time.1 =
          ∑ stage ∈ Finset.range (length + 1),
            (run stackedShortCurrent stage).contact.time.1 := by
      have shifted :
          (∑ stage ∈ Finset.range length,
              (run stackedShortCurrent stage).nextContact.time.1) =
            ∑ stage ∈ Finset.range length,
              (run stackedShortCurrent (stage + 1)).contact.time.1 := by
        apply Finset.sum_congr rfl
        intro stage _stageMem
        rw [run_succ, next_contact]
      rw [shifted, Finset.sum_range_succ']
      simp only [run_zero]
      ring
    have successorEq :
        (∑ stage ∈ Finset.range length,
          (run stackedShortCurrent stage).contact.time.1) ≤
        stackedShortCurrent.contact.time.1 +
          ∑ stage ∈ Finset.range length,
            (run stackedShortCurrent stage).nextContact.time.1 := by
      rw [nextSumEq,
        ← elapsedTime_eq_sum_contactTime stackedShortCurrent length,
        ← elapsedTime_eq_sum_contactTime stackedShortCurrent (length + 1)]
      exact (elapsedTime_strictMono stackedShortCurrent).monotone
        (Nat.le_succ length)
    have nextSumLe :
        (∑ stage ∈ Finset.range length,
            (run stackedShortCurrent stage).nextContact.time.1) ≤
          (finiteModeKineticAmbientFactor stackedSidebandModes *
            puncturedWholeVorticityKineticMass
              stackedShortCurrent.contact.physicalState) /
            (3998 / 1000 : Real) := by
      apply (le_div_iff₀ chargePos).2
      simpa only [mul_comm] using clockPrefix
    linarith [successorEq, nextSumLe]

theorem stackedSideband_mem_runStandingAnchorCube
    (stage : Nat)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    wave ∈ wholeRestartModes
      ((runCellStanding stackedShortCurrent stage).anchorLevel + 1) := by
  have anchorEq :=
    runCellStanding_anchorLevel_eq_initial_add_paymentCount
      stackedShortCurrent stage
  have anchorLower : 88 ≤
      (runCellStanding stackedShortCurrent stage).anchorLevel := by
    rw [anchorEq, stackedShortCurrent_level_eq_eighty_eight]
    omega
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

def stackedRunStandingMaterial (stage : Nat) :=
  nativeRestartStandingValuedArithmeticMaterial
    (runStandingCellEffect stackedShortCurrent stage)

/-- Current-only reserve of the exact standing-valued edge.  It contains no
future state: the loss is computed from the current replay and its already
compiler-selected contact. -/
def ButterflyStackedKineticReserveAt (stage : Nat) : Prop :=
  ∀ wave ∈ stackedSidebandModes,
    1 + standingValuedKineticFaceAdvanceLossUpper
          (stackedRunStandingMaterial stage) wave <
      selfTangentWorkAt
        (run stackedShortCurrent stage).contact.physicalState wave

/-- Local source advance: one reserve occurrence transports the complete
paying instruction to the compiler-owned next current. -/
theorem butterflyStackedKineticInvariantAt_succ_of_reserve
    (stage : Nat)
    (reserve : ButterflyStackedKineticReserveAt stage) :
    ButterflyStackedKineticInvariantAt (stage + 1) := by
  intro wave waveMem
  have waveNe : wave ≠ 0 := fun waveZero =>
    stackedSidebandCone.zeroNotMem (waveZero ▸ waveMem)
  have generated :=
    next_selfTangentWork_gt_of_standingValuedReserve
      (nu := butterflyGainViscosity)
      (current := run stackedShortCurrent stage)
      (standing := runCellStanding stackedShortCurrent stage)
      (stackedRunStandingMaterial stage) wave waveNe
      (reserve wave waveMem)
  rw [run_succ]
  unfold selfTangentWorkAt
  unfold kineticSelfTangentWorkAt at generated
  exact generated

theorem stackedStageZero_standingValuedLoss_lt_one
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    standingValuedKineticFaceAdvanceLossUpper
        (stackedRunStandingMaterial 0) wave < 1 := by
  have clockLt : stackedShortCurrent.nextContact.time.1 <
      1 / (10 : Real) ^ 40 :=
    stackedShortCurrent.nextContact.time.2.2.trans_lt
      stackedShortCurrent_duration_lt_inverse_ten_pow_forty
  have rowLt := stackedSideband_currentRow_norm_lt_ten wave
  have tangentLt := stackedSideband_sourceTangent_norm_lt_five_million
    wave waveMem
  have driftLt := stackedSideband_kineticTangentSourceUpper_lt_one_hundredth
    wave waveMem
  have driftNonneg := fullReplayKineticTangentSourceUpper_nonneg
    stackedShortCurrent wave
  unfold standingValuedKineticFaceAdvanceLossUpper
  change
    3 * (stackedShortCurrent.nextContact.time.1 *
          (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedShortCurrent.contact.physicalState wave‖ +
            fullReplayKineticTangentSourceUpper stackedShortCurrent wave)) *
        (‖wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              stackedShortCurrent.contact.physicalState wave‖ +
          fullReplayKineticTangentSourceUpper stackedShortCurrent wave) +
      3 * ‖stackedShortCurrent.contact.physicalState wave‖ *
        fullReplayKineticTangentSourceUpper stackedShortCurrent wave < 1
  calc
    _ ≤
        3 * ((1 / (10 : Real) ^ 40) *
          (5000000 + 1 / 100 : Real)) *
          (5000000 + 1 / 100 : Real) +
        3 * 10 * (1 / 100 : Real) := by
      gcongr
    _ < 1 := by norm_num

theorem butterflyStackedKineticReserveAt_zero :
    ButterflyStackedKineticReserveAt 0 := by
  intro wave waveMem
  have work := (stackedShortContact_sourcePatch.2.2 wave waveMem).2.2
  have loss := stackedStageZero_standingValuedLoss_lt_one wave waveMem
  change 1 + standingValuedKineticFaceAdvanceLossUpper
      (stackedRunStandingMaterial 0) wave <
    selfTangentWorkAt stackedShortCurrent.contact.physicalState wave
  nlinarith

theorem stackedStageOne_standingValuedLoss_lt_one
    (wave : IntegerWavevector)
    (waveMem : wave ∈ stackedSidebandModes) :
    standingValuedKineticFaceAdvanceLossUpper
        (stackedRunStandingMaterial 1) wave < 1 := by
  have clockLt : stackedStageOneCurrent.nextContact.time.1 <
      1 / (10 : Real) ^ 30 :=
    stackedStageOneCurrent.nextContact.time.2.2.trans_lt
      stackedStageOneCurrent_duration_lt_inverse_ten_pow_thirty
  have rowLt := stackedStageOneSideband_currentRow_norm_lt_eleven
    wave waveMem
  have tangentLt :
      ‖wholeLatticeVorticityFourierTangentAt
          butterflyGainViscosity.coeff
          stackedStageOneCurrent.contact.physicalState wave‖ < 5000001 := by
    rw [stackedStageOneCurrent_eq_next]
    exact stackedSideband_nextContactTangent_norm_lt_five_million_one
      wave waveMem
  have driftLt :=
    stackedStageOneSideband_kineticTangentSourceUpper_lt_one_hundredth
      wave waveMem
  have driftNonneg := fullReplayKineticTangentSourceUpper_nonneg
    stackedStageOneCurrent wave
  unfold standingValuedKineticFaceAdvanceLossUpper
  change
    3 * (stackedStageOneCurrent.nextContact.time.1 *
          (‖wholeLatticeVorticityFourierTangentAt
                butterflyGainViscosity.coeff
                stackedStageOneCurrent.contact.physicalState wave‖ +
            fullReplayKineticTangentSourceUpper
              stackedStageOneCurrent wave)) *
        (‖wholeLatticeVorticityFourierTangentAt
              butterflyGainViscosity.coeff
              stackedStageOneCurrent.contact.physicalState wave‖ +
          fullReplayKineticTangentSourceUpper
            stackedStageOneCurrent wave) +
      3 * ‖stackedStageOneCurrent.contact.physicalState wave‖ *
        fullReplayKineticTangentSourceUpper
          stackedStageOneCurrent wave < 1
  calc
    _ ≤
        3 * ((1 / (10 : Real) ^ 30) *
          (5000001 + 1 / 100 : Real)) *
          (5000001 + 1 / 100 : Real) +
        3 * 11 * (1 / 100 : Real) := by
      gcongr
    _ < 1 := by norm_num

theorem butterflyStackedKineticReserveAt_one :
    ButterflyStackedKineticReserveAt 1 := by
  intro wave waveMem
  have work := stackedSideband_nextContact_selfTangentWork_gt_eleven
    wave waveMem
  have loss := stackedStageOne_standingValuedLoss_lt_one wave waveMem
  change 1 + standingValuedKineticFaceAdvanceLossUpper
      (stackedRunStandingMaterial 1) wave <
    selfTangentWorkAt stackedStageOneCurrent.contact.physicalState wave
  rw [stackedStageOneCurrent_eq_next, next_contact]
  calc
    1 + standingValuedKineticFaceAdvanceLossUpper
          (stackedRunStandingMaterial 1) wave < 1 + 1 :=
      by simpa only [add_comm] using add_lt_add_left loss 1
    _ < 11 := by norm_num
    _ < selfTangentWorkAt
        stackedShortCurrent.nextContact.physicalState wave := work

/-- The third literal current is generated by the finite local reserve law,
not by another hand-built stage calculation. -/
theorem butterflyStackedKineticInvariantAt_two :
    ButterflyStackedKineticInvariantAt 2 := by
  simpa only [show (2 : Nat) = 1 + 1 by omega] using
    butterflyStackedKineticInvariantAt_succ_of_reserve 1
      butterflyStackedKineticReserveAt_one

/-- At any stage satisfying the finite source invariant, a residual normal
form is quantitatively paid by its own contact clock and expansion debit. -/
theorem stackedRunResidualExpansion_clock_mul_densitySum_le
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage)
    (residual : GeneratedParallelResidualAt
      (stackedRunStandingMaterial stage)
      (stackedRunStandingMaterial stage).arithmeticMaterial) :
    (run stackedShortCurrent stage).nextContact.time.1 *
        (∑ wave ∈ stackedSidebandModes,
          nextContactKineticEulerPaymentDensity
            (run stackedShortCurrent stage) wave) ≤
      ((stackedRunStandingMaterial stage).generatedResidualExpansion residual
        ).finiteNetEnstrophyDebit := by
  apply NativeRestartStandingValuedArithmeticMaterialAt.GeneratedResidualExpansionAt.clock_mul_sum_kineticDensity_le_finiteNetEnstrophyDebit
  · intro wave waveMem
    exact stackedSideband_mem_runStandingAnchorCube stage wave waveMem
  · intro wave waveMem
    exact butterflyGain_stackedSideband_kineticPaymentDensity_pos_of_selfWork
      (run stackedShortCurrent stage) wave waveMem
      (invariant wave waveMem)

theorem stackedRun_kineticPaymentDensity_sum_pos
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage) :
    0 < ∑ wave ∈ stackedSidebandModes,
      nextContactKineticEulerPaymentDensity
        (run stackedShortCurrent stage) wave := by
  apply Finset.sum_pos'
  · intro wave waveMem
    exact (butterflyGain_stackedSideband_kineticPaymentDensity_pos_of_selfWork
      (run stackedShortCurrent stage) wave waveMem
      (invariant wave waveMem)).le
  · refine ⟨plusSideband, by simp [stackedSidebandModes], ?_⟩
    exact butterflyGain_stackedSideband_kineticPaymentDensity_pos_of_selfWork
      (run stackedShortCurrent stage) plusSideband
      (by simp [stackedSidebandModes])
      (invariant plusSideband (by simp [stackedSidebandModes]))

theorem stackedRunResidualExpansion_finiteDebit_pos
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage)
    (residual : GeneratedParallelResidualAt
      (stackedRunStandingMaterial stage)
      (stackedRunStandingMaterial stage).arithmeticMaterial) :
    0 < ((stackedRunStandingMaterial stage).generatedResidualExpansion residual
      ).finiteNetEnstrophyDebit := by
  have paid := stackedRunResidualExpansion_clock_mul_densitySum_le
    stage invariant residual
  have clockPaymentPos :
      0 < (run stackedShortCurrent stage).nextContact.time.1 *
        (∑ wave ∈ stackedSidebandModes,
          nextContactKineticEulerPaymentDensity
            (run stackedShortCurrent stage) wave) :=
    mul_pos (run stackedShortCurrent stage).nextContact.time_pos
      (stackedRun_kineticPaymentDensity_sum_pos stage invariant)
  exact clockPaymentPos.trans_le paid

/-- One local invariant occurrence compiles directly into the paid subtype
of the already-generated root outcome. -/
noncomputable def stackedRun_rootOutcome_isPaid
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage) :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    (nativeFluidMediumRootOperationalOutcomeAt source
      (source.stateAfter stage)).IsPaid := by
  dsimp only
  generalize outcomeEq :
    nativeFluidMediumRootOperationalOutcomeAt
      (classicalWholeRestartMediumSource stackedShortCurrent)
      ((classicalWholeRestartMediumSource stackedShortCurrent).stateAfter stage) =
        outcome
  cases outcome with
  | exactPayment => exact PUnit.unit
  | generatedResidual => exact PUnit.unit
  | obstruction obstruction _demand =>
      rw [classicalWholeRestartMediumSource_stateAfter] at obstruction
      rcases obstruction with
        ⟨⟨effect, effectEq⟩, residual, expansion, expansionEq,
          _rawNonpositive, expansionNonpositive⟩
      subst effect
      change expansion.finiteNetEnstrophyDebit ≤ 0 at expansionNonpositive
      rw [expansionEq] at expansionNonpositive
      exact (not_lt_of_ge expansionNonpositive
        (stackedRunResidualExpansion_finiteDebit_pos
          stage invariant residual)).elim

theorem stackedRun_paidRootStep_factorizes
    (stage : Nat)
    (invariant : ButterflyStackedKineticInvariantAt stage) :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source stage)
    HEq (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter stage)).effect
      (stackedRunStandingMaterial stage) ∧
      Nonempty (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter stage)).IsPaid ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter (stage + 1) := by
  dsimp only
  have factorized :=
    classicalWholeRestart_runStandingEffect_rootStep_factorizes
      stackedShortCurrent stage
  exact ⟨factorized.1, ⟨stackedRun_rootOutcome_isPaid stage invariant⟩,
    factorized.2.2⟩

/-- The first successor not handled by a dedicated stage file reaches the
paid root disposition through the generic same-material reserve advance. -/
theorem stackedStageTwo_paidRootStep_factorizes :
    let source := classicalWholeRestartMediumSource stackedShortCurrent
    let visit : SourceNativeTemporalVisitAt
        (nativeFluidMediumLivingRoot source).toAuthoritativeRoot.toLedgerRoot :=
      .finite (nativeFluidMediumRootVisit source 2)
    HEq (nativeFluidMediumExactOperationalEffectAt source
        (source.stateAfter 2)).effect
      (stackedRunStandingMaterial 2) ∧
      Nonempty (nativeFluidMediumRootOperationalOutcomeAt source
        (source.stateAfter 2)).IsPaid ∧
      ((nativeFluidMediumLivingRoot source).generatedNextCurrentAt visit
        ).visit.current = source.stateAfter 3 :=
  stackedRun_paidRootStep_factorizes 2
    butterflyStackedKineticInvariantAt_two

end
end ButterflyStackedKineticInvariant
end SaturationMonoid.NavierStokes.RationalVorticityEvaluator
