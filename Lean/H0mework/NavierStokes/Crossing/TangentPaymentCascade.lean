import H0mework.NavierStokes.Crossing.UnforcedTangentPayment
import H0mework.NavierStokes.Restart.FinitePrefixDualSquareLedger
import H0mework.NavierStokes.Restart.HalfCriticalDualSquareReduction
import H0mework.NavierStokes.Energy.WholeKineticDifferenceCancellation
import H0mework.NavierStokes.ShellSources.WholeReceiptEnergyWriteBack

/-!
# Finite-prefix cascade of actual crossing tangent payments

Every nonzero actual unforced tangent already generates its own positive local
time and its own strictly positive `L²_t H⁻¹_x` payment.  This module makes
that choice source-owned, translates it to the unique accumulated restart
window, and sums the payments before any quotient can identify occurrences.

No crossing branch, Fourier output, local time, cutoff, lower-bound
certificate, or continuation is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade

open scoped BigOperators Interval Topology ENNReal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalDualSquareReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingSelfForcingReduction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open AffineRelaxation

noncomputable section

/-! ## Finite-time accumulation forces every current to cross -/

/-- Native restart iteration is associative; shifting the initial current
does not create a second trajectory. -/
theorem run_run
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start length : ℕ) :
    run (run initial start) length = run initial (start + length) := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [run_succ, inductionHypothesis]
      simpa [Nat.add_assoc] using
        (run_succ initial (start + length)).symm

/-- Accumulated physical time on a shifted run is the exact tail of the same
global physical-time axis. -/
theorem elapsedTime_run_add
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start length : ℕ) :
    elapsedTime initial start + elapsedTime (run initial start) length =
      elapsedTime initial (start + length) := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [elapsedTime_succ]
      rw [run_run]
      calc
        elapsedTime initial start +
              (elapsedTime (run initial start) length +
                (run initial (start + length)).contact.time.1) =
            (elapsedTime initial start +
                elapsedTime (run initial start) length) +
              (run initial (start + length)).contact.time.1 := by ring
        _ = elapsedTime initial (start + length) +
              (run initial (start + length)).contact.time.1 := by
          rw [inductionHypothesis]
        _ = elapsedTime initial ((start + length) + 1) := by
          rw [elapsedTime_succ]
        _ = elapsedTime initial (start + (length + 1)) := by
          rw [Nat.add_assoc]

theorem elapsedTime_run_bddAbove
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (start : ℕ) :
    BddAbove (Set.range (elapsedTime (run initial start))) := by
  rcases elapsedBounded with ⟨upper, upperBound⟩
  refine ⟨upper - elapsedTime initial start, ?_⟩
  rintro time ⟨length, rfl⟩
  have globalLe : elapsedTime initial (start + length) ≤ upper :=
    upperBound ⟨start + length, rfl⟩
  rw [← elapsedTime_run_add initial start length] at globalLe
  linarith

/-- If the actual physical write-chain accumulated in finite time, every
generated current would be on the half-critical crossing side.  A single
noncrossing current would start a crossing-free tail, whose existing
dual-square theorem forces unbounded physical time. -/
theorem elapsedTime_bddAbove_forces_every_halfCriticalCrossing
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    wholeRestartHalfCriticalCrossed initial index := by
  by_contra notCrossed
  have shiftedMargin :
      criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass
            (run initial index).contact.physicalState ≤
        (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 :=
    le_of_not_gt notCrossed
  exact
    (elapsedTime_not_bddAbove_of_initial_halfCriticalMargin
      (run initial index) shiftedMargin)
      (elapsedTime_run_bddAbove initial elapsedBounded index)

/-! ## Whole unforced stationary exclusion -/

private theorem zero_whole_gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          ((0 : ComplexVorticityHilbertState) wave) := by
  simp [complexCoordinateAmplitudeSq]

/-- Exact finite kinetic cancellation survives the canonical punctured-cube
limit for the nonlinear self-pairing of an arbitrary physical whole state. -/
theorem wholeStateVorticityNonlinearSelfKineticPairing_eq_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (stateReality : FiniteStateFourierReality state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityNonlinearDifferenceKineticPairing
        state 0 stateTransverse wholeStateTransverse_zero
        gradientSummable zero_whole_gradient_summable
        (summable_wholeStateVorticityGradientDensity_sub
          state 0 gradientSummable zero_whole_gradient_summable) = 0 := by
  have canonicalTendsto :=
    canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_tendsto
      state 0 zeroRow (by simp) stateTransverse wholeStateTransverse_zero
      gradientSummable zero_whole_gradient_summable
  have canonicalZero : ∀ radius : ℕ,
      canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
          radius state 0 stateTransverse wholeStateTransverse_zero = 0 := by
    intro radius
    let modes := puncturedIntegerWaveFrequencyCube radius
    have zeroNotMem : 0 ∉ modes :=
      zero_not_mem_puncturedIntegerWaveFrequencyCube radius
    have negClosed : FiniteModeNegClosed modes :=
      fun wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    have finiteTransverse : FiniteStateTransverseOn modes state :=
      finiteStateTransverseOn_of_wholeStateTransverse
        modes state stateTransverse
    have finiteReality : FiniteStateRealityOn modes state :=
      fun wave _waveMem => stateReality wave
    rw [canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_eq_finite]
    have zeroCoefficient :
        ∀ output : IntegerWavevector,
          finiteStateVorticityNonlinearCoefficientAt
              modes 0 output = 0 := by
      intro output
      simp [finiteStateVorticityNonlinearCoefficientAt,
        finiteStateVorticityNonlinearPairContribution,
        finiteStateVelocityCoefficient]
    have differenceEq :
        (fun output =>
          finiteStateVorticityNonlinearCoefficientAt modes state output -
            finiteStateVorticityNonlinearCoefficientAt modes 0 output) =
          fun output =>
            finiteStateVorticityNonlinearCoefficientAt modes state output := by
      funext output
      rw [zeroCoefficient, sub_zero]
    unfold finiteStateVorticityNonlinearDifferenceKineticPairing
    rw [sub_zero, differenceEq]
    exact finiteStateVorticityNonlinearKineticPairing_eq_zero
      modes zeroNotMem negClosed state finiteTransverse finiteReality
  have zeroTendsto :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique
    (canonicalTendsto.congr'
      (Filter.Eventually.of_forall fun radius => canonicalZero radius))
    zeroTendsto

/-- A whole physical state with zero unforced Navier--Stokes tangent has zero
vorticity mass.  This is the infinite-carrier stationary exclusion obtained
from exact nonlinear kinetic cancellation and positive viscosity. -/
theorem wholeUnforcedTangent_zero_forces_euclideanMass_zero
    (viscosity : ℝ)
    (viscosityPos : 0 < viscosity)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (stateReality : FiniteStateFourierReality state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (tangentZero : ∀ output : IntegerWavevector,
      wholeStateVorticityNonlinearCoefficientAt state output -
          (viscosity * integerWaveViscousMultiplier output) •
            state output = 0) :
    wholeVorticityEuclideanMass state = 0 := by
  let pairing :=
    wholeStateVorticityNonlinearDifferenceKineticPairing
      state 0 stateTransverse wholeStateTransverse_zero
      gradientSummable zero_whole_gradient_summable
      (summable_wholeStateVorticityGradientDensity_sub
        state 0 gradientSummable zero_whole_gradient_summable)
  have pairingZero : pairing = 0 := by
    simpa [pairing] using
      wholeStateVorticityNonlinearSelfKineticPairing_eq_zero
        state zeroRow stateTransverse stateReality gradientSummable
  have nonlinearAtZero : ∀ output : IntegerWavevector,
      wholeStateVorticityNonlinearCoefficientAt
        (0 : ComplexVorticityHilbertState) output = 0 := by
    intro output
    simp [wholeStateVorticityNonlinearCoefficientAt,
      finiteStateVorticityNonlinearPairContribution]
  have pairingTsum :
      pairing =
        ∑' wave : NonzeroIntegerWavevector,
          complexCoordinateRealInner
              (state wave.1)
              (wholeStateVorticityNonlinearCoefficientAt
                state wave.1) /
            integerWaveViscousMultiplier wave.1 := by
    simpa [pairing, nonlinearAtZero] using
      wholeStateVorticityNonlinearDifferenceKineticPairing_eq_tsum
        state 0 stateTransverse wholeStateTransverse_zero
        gradientSummable zero_whole_gradient_summable
  have workEq : ∀ wave : NonzeroIntegerWavevector,
      complexCoordinateRealInner
            (state wave.1)
            (wholeStateVorticityNonlinearCoefficientAt
              state wave.1) /
          integerWaveViscousMultiplier wave.1 =
        viscosity * complexCoordinateAmplitudeSq (state wave.1) := by
    intro wave
    have nonlinearEq :
        wholeStateVorticityNonlinearCoefficientAt state wave.1 =
          (viscosity * integerWaveViscousMultiplier wave.1) •
            state wave.1 :=
      sub_eq_zero.mp (tangentZero wave.1)
    rw [nonlinearEq,
      complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self,
      ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    have multiplierNe : integerWaveViscousMultiplier wave.1 ≠ 0 :=
      ne_of_gt (integerWaveViscousMultiplier_pos wave)
    field_simp [multiplierNe]
  have pairingEqMass :
      pairing =
        viscosity * puncturedWholeVorticityEuclideanMass state := by
    rw [pairingTsum]
    calc
      (∑' wave : NonzeroIntegerWavevector,
          complexCoordinateRealInner
              (state wave.1)
              (wholeStateVorticityNonlinearCoefficientAt
                state wave.1) /
            integerWaveViscousMultiplier wave.1) =
          ∑' wave : NonzeroIntegerWavevector,
            viscosity * complexCoordinateAmplitudeSq (state wave.1) := by
        exact tsum_congr workEq
      _ = viscosity *
            ∑' wave : NonzeroIntegerWavevector,
              complexCoordinateAmplitudeSq (state wave.1) := by
        rw [tsum_mul_left]
      _ = viscosity * puncturedWholeVorticityEuclideanMass state := rfl
  have puncturedZero : puncturedWholeVorticityEuclideanMass state = 0 := by
    have productZero :
        viscosity * puncturedWholeVorticityEuclideanMass state = 0 := by
      rw [← pairingEqMass, pairingZero]
    exact (mul_eq_zero.mp productZero).resolve_left viscosityPos.ne'
  rw [← puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
    state zeroRow]
  exact puncturedZero

/-- An actual half-critical crossing cannot have zero unforced tangent.
The zero-tangent branch would be a whole stationary state; exact kinetic
cancellation then makes its vorticity mass zero, contradicting the crossing
threshold. -/
theorem wholeRestartCrossingUnforcedTangentRow_ne_zero_of_crossed
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingUnforcedTangentRow initial index ≠ 0 := by
  intro tangentZero
  have tangentPointwise : ∀ output : IntegerWavevector,
      wholeStateVorticityNonlinearCoefficientAt
            (run initial index).contact.physicalState output -
        (ν.coeff * integerWaveViscousMultiplier output) •
          (run initial index).contact.physicalState output = 0 := by
    intro output
    simpa [wholeRestartCrossingUnforcedTangentRow] using
      congrFun tangentZero output
  have massZero :
      wholeVorticityEuclideanMass
          (run initial index).contact.physicalState = 0 :=
    wholeUnforcedTangent_zero_forces_euclideanMass_zero
      ν.coeff ν.coeff_pos
      (run initial index).contact.physicalState
      (run initial index).contact.physicalState_zero
      (run initial index).contact.transverse
      (run initial index).contact.reality
      (run initial index).contact.gradient_summable
      tangentPointwise
  have thresholdPos :
      0 < (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
    exact mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos ν.coeff_pos))
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  unfold wholeRestartHalfCriticalCrossed at crossed
  rw [massZero] at crossed
  simp only [mul_zero] at crossed
  exact (not_lt_of_ge thresholdPos.le) crossed

/-! ## Source-owned local payment -/

/-- The positive local time generated by the actual tangent when it is
nonzero, and zero on the faithfully zero branch. -/
noncomputable def wholeRestartCrossingTangentPaymentTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ := by
  classical
  exact
    if tangentNonzero :
        wholeRestartCrossingUnforcedTangentRow initial index ≠ 0 then
      Classical.choose
        (wholeRestartCrossingUnforcedTangent_positiveTimePayment
          initial index tangentNonzero)
    else
      0

theorem wholeRestartCrossingTangentPaymentTime_spec
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0) :
    0 < wholeRestartCrossingTangentPaymentTime initial index ∧
      wholeRestartCrossingTangentPaymentTime initial index <
        (run initial index).nextContact.time.1 ∧
      wholeRestartCrossingTangentPaymentTime initial index *
            (wholeRestartCrossingContinuousUnforcedTangentDensity
              initial index tangentNonzero 0 / 2) ≤
        ∫ time in (0 : ℝ)..
            wholeRestartCrossingTangentPaymentTime initial index,
          wholeRestartCrossingContinuousUnforcedTangentDensity
            initial index tangentNonzero time ∧
      0 <
        ∫ time in (0 : ℝ)..
            wholeRestartCrossingTangentPaymentTime initial index,
          wholeRestartCrossingContinuousUnforcedTangentDensity
            initial index tangentNonzero time ∧
      (∫ time in (0 : ℝ)..
          wholeRestartCrossingTangentPaymentTime initial index,
        wholeRestartCrossingContinuousUnforcedTangentDensity
          initial index tangentNonzero time) ≤
        ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  unfold wholeRestartCrossingTangentPaymentTime
  rw [dif_pos tangentNonzero]
  exact Classical.choose_spec
    (wholeRestartCrossingUnforcedTangent_positiveTimePayment
      initial index tangentNonzero)

/-- The total actual tangent payment at one restart contact.  Its branch and
time are selected by the generated tangent itself. -/
noncomputable def wholeRestartCrossingTangentPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ := by
  classical
  exact
    if tangentNonzero :
        wholeRestartCrossingUnforcedTangentRow initial index ≠ 0 then
      ∫ time in (0 : ℝ)..
          wholeRestartCrossingTangentPaymentTime initial index,
        wholeRestartCrossingContinuousUnforcedTangentDensity
          initial index tangentNonzero time
    else
      0

theorem wholeRestartCrossingTangentPayment_pos_iff
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 < wholeRestartCrossingTangentPayment initial index ↔
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0 := by
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0
  · rw [wholeRestartCrossingTangentPayment, dif_pos tangentNonzero]
    exact ⟨fun _ => tangentNonzero, fun _ =>
      (wholeRestartCrossingTangentPaymentTime_spec
        initial index tangentNonzero).2.2.2.1⟩
  · simp [wholeRestartCrossingTangentPayment, tangentNonzero]

/-- Every actual half-critical crossing pays a strictly positive tangent
amount on its source-selected unforced physical-time window. -/
theorem wholeRestartCrossingTangentPayment_pos_of_crossed
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 < wholeRestartCrossingTangentPayment initial index :=
  (wholeRestartCrossingTangentPayment_pos_iff initial index).2
    (wholeRestartCrossingUnforcedTangentRow_ne_zero_of_crossed
      initial index crossed)

/-- If the complete actual restart time stays bounded, every generated
current crosses and therefore every occurrence pays strictly positive
unforced tangent work. -/
theorem elapsedTime_bddAbove_forces_every_crossingTangentPayment_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    0 < wholeRestartCrossingTangentPayment initial index :=
  wholeRestartCrossingTangentPayment_pos_of_crossed initial index
    (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
      initial elapsedBounded index)

/-- The exact zero-tangent relation is not a surviving crossing branch.
Every actual crossing either has the source-generated reciprocal-count
forcing reduction, or its nonzero gluing obstruction is transported and
pays strictly positive actual unforced tangent work. -/
theorem wholeRestartCrossing_reduced_forcing_or_native_positive_tangentPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable =
        ((canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              initial index crossed) : ℝ)⁻¹ : ℂ) •
          wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed) ∨
      (wholeRestartCrossingCompleteSourceGluingNegativeOneState
            initial index crossed ≠ 0 ∧
        (wholeRestartComponentGluingResidualRow initial (index + 1) ≠ 0 ∨
          linearResidualTrace wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail initial index) 0 ≠
            0) ∧
        0 < wholeRestartCrossingTangentPayment initial index) := by
  rcases
      wholeRestartCrossing_reduced_forcing_or_native_residual_transport
        initial index crossed with reduced | transported
  · exact Or.inl reduced
  · exact Or.inr
      ⟨transported.1, transported.2,
        wholeRestartCrossingTangentPayment_pos_of_crossed
          initial index crossed⟩

/-- A finite accumulated physical-time axis therefore exposes this exact
reduced-forcing/positive-payment alternative at every generated round. -/
theorem elapsedTime_bddAbove_forces_every_reduced_forcing_or_native_positive_tangentPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial)))
    (index : ℕ) :
    let crossed :=
      elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index
    (wholeStateVorticityNonlinearNegativeOneState
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable =
        ((canonicalHalfCriticalComponentCount ν
            (wholeRestartCrossingFiniteCoreState
              initial index crossed) : ℝ)⁻¹ : ℂ) •
          wholeRestartCrossingFiniteCoreNegativeOneState
            initial index crossed) ∨
      (wholeRestartCrossingCompleteSourceGluingNegativeOneState
            initial index crossed ≠ 0 ∧
        (wholeRestartComponentGluingResidualRow initial (index + 1) ≠ 0 ∨
          linearResidualTrace wholeRestartComponentGluingResidualTailKeep
              (wholeRestartComponentGluingResidualTail initial index) 0 ≠
            0) ∧
        0 < wholeRestartCrossingTangentPayment initial index) := by
  dsimp only
  exact wholeRestartCrossing_reduced_forcing_or_native_positive_tangentPayment
    initial index
      (elapsedTime_bddAbove_forces_every_halfCriticalCrossing
        initial elapsedBounded index)

theorem wholeRestartCrossingTangentPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartCrossingTangentPayment initial index := by
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0
  · exact (wholeRestartCrossingTangentPayment_pos_iff
      initial index).2 tangentNonzero |>.le
  · simp [wholeRestartCrossingTangentPayment, tangentNonzero]

theorem wholeRestartCrossingTangentPayment_le_wholeTangent
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartCrossingTangentPayment initial index ≤
      ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0
  · rw [wholeRestartCrossingTangentPayment, dif_pos tangentNonzero]
    exact (wholeRestartCrossingTangentPaymentTime_spec
      initial index tangentNonzero).2.2.2.2
  · rw [wholeRestartCrossingTangentPayment, dif_neg tangentNonzero]
    exact sq_nonneg _

/-! ## Translation to the single physical-time axis -/

/-- The exact global interval occupied by the source-selected local tangent
payment. -/
def wholeRestartCrossingTangentPaymentWindow
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : Set ℝ :=
  Ioc
    (elapsedTime initial (index + 1))
    (elapsedTime initial (index + 1) +
      wholeRestartCrossingTangentPaymentTime initial index)

theorem wholeRestartCrossingTangentPaymentWindow_subset
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartCrossingTangentPaymentWindow initial index ⊆
      wholeRestartPhysicalWindow initial (index + 1) := by
  intro time timeMem
  unfold wholeRestartCrossingTangentPaymentWindow at timeMem
  unfold wholeRestartPhysicalWindow
  refine ⟨timeMem.1, ?_⟩
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0
  · have timeLt :=
      (wholeRestartCrossingTangentPaymentTime_spec
        initial index tangentNonzero).2.1
    exact (calc
      time ≤ elapsedTime initial (index + 1) +
            wholeRestartCrossingTangentPaymentTime initial index := timeMem.2
      _ < elapsedTime initial (index + 1) +
            (run initial index).nextContact.time.1 :=
        by
          simpa [add_comm] using
            add_lt_add_left timeLt (elapsedTime initial (index + 1))
      _ = elapsedTime initial ((index + 1) + 1) := by
        rw [elapsedTime_succ]
        rfl).le
  · have timeEq :
        wholeRestartCrossingTangentPaymentTime initial index = 0 := by
      simp [wholeRestartCrossingTangentPaymentTime, tangentNonzero]
    rw [timeEq, add_zero] at timeMem
    exact False.elim ((not_lt_of_ge timeMem.2) timeMem.1)

theorem wholeRestartCrossingTangentPaymentWindow_disjoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    {left right : ℕ}
    (different : left ≠ right) :
    Disjoint
      (wholeRestartCrossingTangentPaymentWindow initial left)
      (wholeRestartCrossingTangentPaymentWindow initial right) := by
  exact
    (wholeRestartPhysicalWindow_disjoint initial
      (by omega : left + 1 ≠ right + 1)).mono
        (wholeRestartCrossingTangentPaymentWindow_subset initial left)
        (wholeRestartCrossingTangentPaymentWindow_subset initial right)

/-- The same source-selected density translated into accumulated physical
time before any occurrence quotient is taken. -/
noncomputable def wholeRestartCrossingTranslatedTangentDensity
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (time : ℝ) : ℝ := by
  classical
  exact
    if tangentNonzero :
        wholeRestartCrossingUnforcedTangentRow initial index ≠ 0 then
      wholeRestartCrossingContinuousUnforcedTangentDensity
        initial index tangentNonzero
          (time - elapsedTime initial (index + 1))
    else
      0

theorem wholeRestartCrossingTangentPayment_eq_globalWindowIntegral
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartCrossingTangentPayment initial index =
      ∫ time in
          elapsedTime initial (index + 1)..
            elapsedTime initial (index + 1) +
              wholeRestartCrossingTangentPaymentTime initial index,
        wholeRestartCrossingTranslatedTangentDensity
          initial index time := by
  by_cases tangentNonzero :
      wholeRestartCrossingUnforcedTangentRow initial index ≠ 0
  · rw [wholeRestartCrossingTangentPayment, dif_pos tangentNonzero]
    unfold wholeRestartCrossingTranslatedTangentDensity
    simp only [dif_pos tangentNonzero]
    rw [intervalIntegral.integral_comp_sub_right]
    simp
  · have timeEq :
        wholeRestartCrossingTangentPaymentTime initial index = 0 := by
      simp [wholeRestartCrossingTangentPaymentTime, tangentNonzero]
    simp [wholeRestartCrossingTangentPayment,
      wholeRestartCrossingTranslatedTangentDensity,
      tangentNonzero, timeEq]

/-! ## Payment by the existing whole dual-square ledger -/

/-- The actual whole tangent is already paid by the nonlinear and viscous
negative-one states of that same receipt. -/
theorem receipt_wholeTangent_norm_sq_le_two_dual_states
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    ‖receipt.wholeTangent‖ ^ 2 ≤
      2 *
        (‖receiptNonlinearNegativeOneState receipt‖ ^ 2 +
          ‖receiptViscousNegativeOneState receipt‖ ^ 2) := by
  have tangentEq :
      receipt.wholeTangent =
        receiptNonlinearNegativeOneState receipt -
          receiptViscousNegativeOneState receipt := by
    simp [receiptNonlinearNegativeOneState]
  rw [tangentEq]
  have normLe :
      ‖receiptNonlinearNegativeOneState receipt -
          receiptViscousNegativeOneState receipt‖ ≤
        ‖receiptNonlinearNegativeOneState receipt‖ +
          ‖receiptViscousNegativeOneState receipt‖ :=
    norm_sub_le _ _
  have squareLe :
      ‖receiptNonlinearNegativeOneState receipt -
          receiptViscousNegativeOneState receipt‖ ^ 2 ≤
        (‖receiptNonlinearNegativeOneState receipt‖ +
          ‖receiptViscousNegativeOneState receipt‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  nlinarith [squareLe, sq_nonneg
    (‖receiptNonlinearNegativeOneState receipt‖ -
      ‖receiptViscousNegativeOneState receipt‖)]

/-- The next actual receipt's tangent square is controlled by the existing
dual-square payment on exactly its own restart segment. -/
theorem nextContact_wholeTangent_norm_sq_le_segmentDualSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 ≤
      (2 * ν.coeff / 3) *
        wholeRestartSegmentDualSquarePayment initial (index + 1) := by
  have tangentLe :=
    receipt_wholeTangent_norm_sq_le_two_dual_states
      (run initial index).nextContact.prefixReceipt
  calc
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 ≤
        2 *
          (‖receiptNonlinearNegativeOneState
              (run initial index).nextContact.prefixReceipt‖ ^ 2 +
            ‖receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt‖ ^ 2) :=
      tangentLe
    _ = (2 * ν.coeff / 3) *
          wholeRestartSegmentDualSquarePayment initial (index + 1) := by
      unfold wholeRestartSegmentDualSquarePayment
      rw [run_succ]
      dsimp only [GeneratedWholeRestartCurrent.next]
      field_simp [ν.coeff_pos.ne']
      exact add_comm _ _

theorem wholeRestartCrossingTangentPayment_le_segmentDualSquarePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartCrossingTangentPayment initial index ≤
      (2 * ν.coeff / 3) *
        wholeRestartSegmentDualSquarePayment initial (index + 1) :=
  (wholeRestartCrossingTangentPayment_le_wholeTangent initial index).trans
    (nextContact_wholeTangent_norm_sq_le_segmentDualSquarePayment
      initial index)

/-! ## Exact finite-prefix accumulation -/

/-- Sum every source-owned tangent payment before occurrence identities are
forgotten. -/
def wholeRestartAccumulatedCrossingTangentPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartCrossingTangentPayment initial index

theorem wholeRestartAccumulatedCrossingTangentPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    0 ≤ wholeRestartAccumulatedCrossingTangentPayment initial length := by
  unfold wholeRestartAccumulatedCrossingTangentPayment
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartCrossingTangentPayment_nonneg initial index

/-- Under finite total physical time, the no-silent occurrence ledger grows
strictly at every actual source round. -/
theorem wholeRestartAccumulatedCrossingTangentPayment_strictMono_of_elapsedTime_bddAbove
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    StrictMono (wholeRestartAccumulatedCrossingTangentPayment initial) := by
  apply strictMono_nat_of_lt_succ
  intro length
  unfold wholeRestartAccumulatedCrossingTangentPayment
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _
    (elapsedTime_bddAbove_forces_every_crossingTangentPayment_pos
      initial elapsedBounded length)

/-- The accumulated payment is literally the sum over the source-generated,
pairwise-disjoint global physical windows. -/
theorem wholeRestartAccumulatedCrossingTangentPayment_eq_globalWindowIntegrals
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    wholeRestartAccumulatedCrossingTangentPayment initial length =
      ∑ index ∈ Finset.range length,
        ∫ time in
            elapsedTime initial (index + 1)..
              elapsedTime initial (index + 1) +
                wholeRestartCrossingTangentPaymentTime initial index,
          wholeRestartCrossingTranslatedTangentDensity
            initial index time := by
  unfold wholeRestartAccumulatedCrossingTangentPayment
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact
    wholeRestartCrossingTangentPayment_eq_globalWindowIntegral
      initial index

private theorem shifted_segmentDualSquare_sum_le_accumulated
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    (∑ index ∈ Finset.range length,
        wholeRestartSegmentDualSquarePayment initial (index + 1)) ≤
      wholeRestartAccumulatedDualSquarePayment initial (length + 1) := by
  unfold wholeRestartAccumulatedDualSquarePayment
  induction length with
  | zero =>
      simpa using
        wholeRestartSegmentDualSquarePayment_nonneg initial 0
  | succ length inductionHypothesis =>
      simpa [Finset.sum_range_succ, Nat.succ_eq_add_one] using
        add_le_add_right inductionHypothesis
          (wholeRestartSegmentDualSquarePayment initial (length + 1))

/-- Arbitrary finite prefixes pay all pre-quotient tangent occurrences once,
and the complete sum is controlled by the already existing physical
dual-square ledger. -/
theorem wholeRestartAccumulatedCrossingTangentPayment_le_dualSquare
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    wholeRestartAccumulatedCrossingTangentPayment initial length ≤
      (2 * ν.coeff / 3) *
        wholeRestartAccumulatedDualSquarePayment initial (length + 1) := by
  have coefficientNonneg : 0 ≤ 2 * ν.coeff / 3 :=
    div_nonneg (mul_nonneg (by norm_num) ν.coeff_pos.le) (by norm_num)
  calc
    wholeRestartAccumulatedCrossingTangentPayment initial length ≤
        ∑ index ∈ Finset.range length,
          (2 * ν.coeff / 3) *
            wholeRestartSegmentDualSquarePayment initial (index + 1) := by
      unfold wholeRestartAccumulatedCrossingTangentPayment
      exact Finset.sum_le_sum fun index _indexMem =>
        wholeRestartCrossingTangentPayment_le_segmentDualSquarePayment
          initial index
    _ = (2 * ν.coeff / 3) *
          (∑ index ∈ Finset.range length,
            wholeRestartSegmentDualSquarePayment initial (index + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * ν.coeff / 3) *
          wholeRestartAccumulatedDualSquarePayment initial (length + 1) :=
      mul_le_mul_of_nonneg_left
        (shifted_segmentDualSquare_sum_le_accumulated initial length)
        coefficientNonneg

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
end NavierStokes
end SaturationMonoid
