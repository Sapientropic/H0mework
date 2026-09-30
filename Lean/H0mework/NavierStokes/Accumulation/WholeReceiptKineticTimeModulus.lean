import H0mework.NavierStokes.EndpointTransport.CofinalNonlinearNegativeOneEuclideanBalance
import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance
import H0mework.NavierStokes.Accumulation.FullReceiptFourierConeAdvance
import H0mework.NavierStokes.VelocityEndpoint.PositiveTimeH1Reentry

/-!
# Cutoff-free kinetic time modulus of an actual whole receipt

The complete nonzero-wave kinetic weight is the exact inverse of the
frequency multiplier in the existing rowwise tangent estimate.  Summing that
same-receipt estimate therefore removes the frequency altogether and gives a
global time modulus without a finite observation, tail capture, or cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped BigOperators ENNReal

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus

open Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCoordinateParseval
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

noncomputable section

/-- The actual whole receipt is globally `1/2`-Hölder in the kinetic
`H⁻¹` vorticity metric.  The right side is the receipt's own complete tangent
write; no observed modes or frequency ceiling occur. -/
theorem receipt_puncturedKineticMass_sub_le_wholeTangent
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    puncturedWholeVorticityKineticMass
        (receipt.wholePath b - receipt.wholePath a) ≤
      3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2 := by
  let difference : ComplexVorticityHilbertState :=
    receipt.wholePath b - receipt.wholePath a
  let rowSquare : IntegerWavevector → Real := fun wave =>
    ‖fixedWaveSpaceTimeRestriction
      requestedTime wave receipt.wholeTangent‖ ^ 2
  have differenceSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        complexCoordinateAmplitudeSq (difference wave.1) /
          integerWaveViscousMultiplier wave.1 :=
    summable_puncturedWholeVorticityKineticMass difference
  have rowSquareSummable : Summable rowSquare := by
    simpa only [rowSquare] using
      summable_fixedWaveSpaceTimeRestriction_norm_sq
        requestedTime receipt.wholeTangent
  have restrictedRowSquareSummable :
      Summable fun wave : NonzeroIntegerWavevector => rowSquare wave.1 := by
    change Summable (rowSquare ∘ Subtype.val)
    exact rowSquareSummable.subtype {wave | wave ≠ 0}
  have timeNonneg : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab
  have rightSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        3 * (b.1 - a.1) * rowSquare wave.1 :=
    restrictedRowSquareSummable.mul_left (3 * (b.1 - a.1))
  have pointwise : ∀ wave : NonzeroIntegerWavevector,
      complexCoordinateAmplitudeSq (difference wave.1) /
          integerWaveViscousMultiplier wave.1 ≤
        3 * (b.1 - a.1) * rowSquare wave.1 := by
    intro wave
    have multiplierPos : 0 < integerWaveViscousMultiplier wave.1 :=
      integerWaveViscousMultiplier_pos wave
    have amplitudeLe :=
      complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (receipt.wholePath b wave.1 - receipt.wholePath a wave.1)
    have rowLe :=
      receiptWave_timeIncrement_sq_le_wholeTangentRow
        receipt wave.1 wave.2 a b hab
    change
      complexCoordinateAmplitudeSq
          (receipt.wholePath b wave.1 - receipt.wholePath a wave.1) /
            integerWaveViscousMultiplier wave.1 ≤ _
    apply (div_le_iff₀ multiplierPos).2
    calc
      complexCoordinateAmplitudeSq
            (receipt.wholePath b wave.1 - receipt.wholePath a wave.1) ≤
          3 * ‖receipt.wholePath b wave.1 -
            receipt.wholePath a wave.1‖ ^ 2 := amplitudeLe
      _ ≤ 3 * ((b.1 - a.1) *
          integerWaveViscousMultiplier wave.1 * rowSquare wave.1) := by
        exact mul_le_mul_of_nonneg_left rowLe (by norm_num)
      _ = (3 * (b.1 - a.1) * rowSquare wave.1) *
          integerWaveViscousMultiplier wave.1 := by ring
  unfold puncturedWholeVorticityKineticMass
  change (∑' wave : NonzeroIntegerWavevector,
      complexCoordinateAmplitudeSq (difference wave.1) /
        integerWaveViscousMultiplier wave.1) ≤ _
  calc
    (∑' wave : NonzeroIntegerWavevector,
        complexCoordinateAmplitudeSq (difference wave.1) /
          integerWaveViscousMultiplier wave.1) ≤
        ∑' wave : NonzeroIntegerWavevector,
          3 * (b.1 - a.1) * rowSquare wave.1 :=
      differenceSummable.tsum_le_tsum pointwise rightSummable
    _ = 3 * (b.1 - a.1) *
        ∑' wave : NonzeroIntegerWavevector, rowSquare wave.1 := by
      rw [tsum_mul_left]
    _ ≤ 3 * (b.1 - a.1) *
        ∑' wave : IntegerWavevector, rowSquare wave := by
      apply mul_le_mul_of_nonneg_left
      · exact Summable.tsum_subtype_le rowSquare
          {wave : IntegerWavevector | wave ≠ 0}
          (fun wave => sq_nonneg _) rowSquareSummable
      · positivity
    _ = 3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2 := by
      rw [show (∑' wave : IntegerWavevector, rowSquare wave) =
          ‖receipt.wholeTangent‖ ^ 2 by
        simpa only [rowSquare] using
          tsum_fixedWaveSpaceTimeRestriction_norm_sq
            requestedTime receipt.wholeTangent]

/-- Biot--Savart installation is linear on the complete whole carrier. -/
theorem wholeBiotSavartVelocityState_sub
    (left right : ComplexVorticityHilbertState) :
    wholeBiotSavartVelocityState (left - right) =
      wholeBiotSavartVelocityState left -
        wholeBiotSavartVelocityState right := by
  apply lp.ext
  rw [lp.coeFn_sub]
  change finiteStateVelocityCoefficient (left - right) =
    finiteStateVelocityCoefficient left -
      finiteStateVelocityCoefficient right
  funext wave
  unfold finiteStateVelocityCoefficient
  change biotSavartVelocityCoefficient wave
      ((left - right) wave) =
    biotSavartVelocityCoefficient wave (left wave) -
      biotSavartVelocityCoefficient wave (right wave)
  rw [show (left - right) wave = left wave - right wave by rfl,
    ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.biotSavartVelocityCoefficient_sub]

/-- The same actual receipt is globally `1/2`-Hölder after its physical
Biot--Savart projection.  This is the cutoff-free velocity displacement
needed by fixed-output nonlinear rows. -/
theorem receipt_wholeBiotSavartVelocity_sub_norm_sq_le_wholeTangent
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    ‖wholeBiotSavartVelocityState (receipt.wholePath b) -
        wholeBiotSavartVelocityState (receipt.wholePath a)‖ ^ 2 ≤
      3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2 := by
  let difference : ComplexVorticityHilbertState :=
    receipt.wholePath b - receipt.wholePath a
  have differenceTransverse : WholeStateTransverse difference :=
    wholeStateTransverse_sub
      (receipt.wholePath b) (receipt.wholePath a)
      (wholePath_transverse receipt b) (wholePath_transverse receipt a)
  rw [← wholeBiotSavartVelocityState_sub]
  calc
    ‖wholeBiotSavartVelocityState difference‖ ^ 2 ≤
        wholeVorticityEuclideanMass
          (wholeBiotSavartVelocityState difference) :=
      wholeState_norm_sq_le_wholeVorticityEuclideanMass _
    _ = puncturedWholeVorticityKineticMass difference :=
      wholeVorticityEuclideanMass_wholeBiotSavartVelocityState
        difference differenceTransverse
    _ ≤ 3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2 :=
      receipt_puncturedKineticMass_sub_le_wholeTangent receipt a b hab

/-- Removing the silent zero row from canonical cubes does not change their
strong exhaustion of a physical zero-row state. -/
theorem complexSharpSupportProjection_puncturedCube_tendsto
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    Filter.Tendsto
      (fun radius =>
        complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius) state)
      Filter.atTop (nhds state) := by
  have full := complexSharpSupportProjection_frequencyCube_tendsto state
  apply full.congr'
  exact Filter.Eventually.of_forall fun radius => by
    ext wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [puncturedIntegerWaveFrequencyCube, zeroRow,
        complexSharpSupportProjection_apply]
    · by_cases waveMem : wave ∈ integerWaveFrequencyCube radius
      · simp [puncturedIntegerWaveFrequencyCube,
          complexSharpSupportProjection_apply, waveZero, waveMem]
      · simp [puncturedIntegerWaveFrequencyCube,
          complexSharpSupportProjection_apply, waveMem]

/-- A finite installed velocity is literally the sharp projection of the
whole Biot--Savart velocity of the same vorticity state. -/
theorem finiteStateWholeVelocity_eq_projection_wholeBiotSavart
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateWholeVelocity modes state =
      complexSharpSupportProjection modes
        (wholeBiotSavartVelocityState state) := by
  ext wave
  simp [finiteStateWholeVelocity_apply,
    complexSharpSupportProjection_apply]

/-- Whole Biot--Savart installation is bounded in the original whole
carrier, with only the exact three-coordinate norm conversion. -/
theorem wholeBiotSavartVelocityState_norm_sq_le_three_mul
    (state : ComplexVorticityHilbertState) :
    ‖wholeBiotSavartVelocityState state‖ ^ 2 ≤ 3 * ‖state‖ ^ 2 := by
  have velocityMassLe :
      wholeVorticityEuclideanMass (wholeBiotSavartVelocityState state) ≤
        wholeVorticityEuclideanMass state := by
    have velocitySummable :=
      summable_vorticityRowAmplitude_sq
        (wholeBiotSavartVelocityState state)
    have stateSummable := summable_vorticityRowAmplitude_sq state
    unfold wholeVorticityEuclideanMass
    apply velocitySummable.tsum_le_tsum _ stateSummable
    intro wave
    rw [vorticityRowAmplitude_sq,
      wholeBiotSavartVelocityState_apply]
    calc
      complexCoordinateVectorNormSq
          (finiteStateVelocityCoefficient state wave) =
        complexCoordinateAmplitudeSq
          (finiteStateVelocityCoefficient state wave) := by
        rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      _ = velocityRowAmplitude state wave ^ 2 :=
        (velocityRowAmplitude_sq state wave).symm
      _ ≤ vorticityRowAmplitude state wave ^ 2 := by
        have factorLe : (1 / (2 * Real.pi) : Real) ≤ 1 := by
          apply (div_le_iff₀ (by positivity : (0 : Real) < 2 * Real.pi)).2
          nlinarith [Real.pi_gt_three]
        have rowLe : velocityRowAmplitude state wave ≤
            vorticityRowAmplitude state wave :=
          (velocityRowAmplitude_le_vorticityRowAmplitude state wave).trans
            (mul_le_of_le_one_left
              (vorticityRowAmplitude_nonneg state wave) factorLe)
        exact (sq_le_sq₀
          (velocityRowAmplitude_nonneg state wave)
          (vorticityRowAmplitude_nonneg state wave)).2 rowLe
  exact (wholeState_norm_sq_le_wholeVorticityEuclideanMass _).trans
    (velocityMassLe.trans
      (wholeVorticityEuclideanMass_le_three_mul_norm_sq state))

/-- The whole vorticity convection row is the curl of the whole physical
velocity convection row.  This is obtained by passing the existing finite
identity through the source-generated punctured cubes; no cutoff remains in
the theorem mouth. -/
theorem wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (transverse : WholeStateTransverse state)
    (output : IntegerWavevector) :
    wholeStateVorticityNonlinearCoefficientAt state output =
      fourierCurlCoefficient output
        (wholeStateVelocityNonlinearCoefficientAt
          (wholeBiotSavartVelocityState state) output) := by
  let modes : Nat → Finset IntegerWavevector :=
    puncturedIntegerWaveFrequencyCube
  let projected : Nat → ComplexVorticityHilbertState := fun radius =>
    complexSharpSupportProjection (modes radius) state
  let velocity := wholeBiotSavartVelocityState state
  have projectedTendsto : Filter.Tendsto projected Filter.atTop (nhds state) := by
    simpa only [projected, modes] using
      complexSharpSupportProjection_puncturedCube_tendsto state zeroRow
  have projectedTransverse : ∀ radius,
      WholeStateTransverse (projected radius) := fun radius =>
    wholeStateTransverse_projection (modes radius) state transverse
  have vorticityTendsto : Filter.Tendsto
      (fun radius =>
        finiteStateVorticityNonlinearCoefficientAt
          (modes radius) state output)
      Filter.atTop
      (nhds (wholeStateVorticityNonlinearCoefficientAt state output)) := by
    have generated := tendsto_wholeStateVorticityNonlinearCoefficientAt
      projected state projectedTransverse transverse projectedTendsto output
    simpa only [projected,
      wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
      using generated
  have velocityZero : velocity 0 = 0 := by
    simp [velocity, wholeBiotSavartVelocityState_apply,
      finiteStateVelocityCoefficient, biotSavartVelocityCoefficient_zero]
  have velocityProjectedTendsto : Filter.Tendsto
      (fun radius => complexSharpSupportProjection (modes radius) velocity)
      Filter.atTop (nhds velocity) := by
    simpa only [modes] using
      complexSharpSupportProjection_puncturedCube_tendsto
        velocity velocityZero
  have velocityProjectionTransverse : ∀ radius,
      WholeStateTransverse
        (complexSharpSupportProjection (modes radius) velocity) :=
    fun radius => wholeStateTransverse_projection (modes radius) velocity
      (wholeBiotSavartVelocityState_transverse state)
  have velocityTendsto : Filter.Tendsto
      (fun radius =>
        finiteStateVelocityNonlinearCoefficientAt
          (modes radius) state output)
      Filter.atTop
      (nhds (wholeStateVelocityNonlinearCoefficientAt velocity output)) := by
    have generated := tendsto_wholeStateVelocityNonlinearCoefficientAt
      (fun radius =>
        complexSharpSupportProjection (modes radius) velocity)
      velocity velocityProjectionTransverse
      (wholeBiotSavartVelocityState_transverse state)
      velocityProjectedTendsto output
    simpa only [← finiteStateWholeVelocity_eq_projection_wholeBiotSavart,
      wholeStateVelocityNonlinearCoefficientAt_finiteStateWholeVelocity,
      velocity] using generated
  have curlContinuous : Continuous (fourierCurlCoefficient output) := by
    unfold fourierCurlCoefficient
    fun_prop
  have curlTendsto : Filter.Tendsto
      (fun radius =>
        fourierCurlCoefficient output
          (finiteStateVelocityNonlinearCoefficientAt
            (modes radius) state output))
      Filter.atTop
      (nhds (fourierCurlCoefficient output
        (wholeStateVelocityNonlinearCoefficientAt velocity output))) :=
    (curlContinuous.tendsto
      (wholeStateVelocityNonlinearCoefficientAt velocity output)).comp
        velocityTendsto
  have sameTendsto : Filter.Tendsto
      (fun radius =>
        finiteStateVorticityNonlinearCoefficientAt
          (modes radius) state output)
      Filter.atTop
      (nhds (fourierCurlCoefficient output
        (wholeStateVelocityNonlinearCoefficientAt velocity output))) := by
    apply curlTendsto.congr'
    exact Filter.Eventually.of_forall fun radius => by
      exact finiteStateVorticityNonlinearCoefficientAt_eq_fourierCurl
        (modes radius)
        (by simp [modes, puncturedIntegerWaveFrequencyCube])
        state (fun wave _waveMem => transverse wave) output |>.symm
  exact tendsto_nhds_unique vorticityTendsto sameTendsto

/-- Explicit cutoff-free operator bound for one Fourier curl row. -/
theorem fourierCurlCoefficient_norm_le_six_pi_sqrt
    (wave : IntegerWavevector)
    (value : ComplexCoordinateVector) :
    ‖fourierCurlCoefficient wave value‖ ≤
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) * ‖value‖ := by
  have squareBound :=
    fourierCurlCoefficient_norm_sq_le_gradientDensity wave value
  have amplitudeBound :=
    complexCoordinateAmplitudeSq_le_three_mul_norm_sq value
  have waveNonneg := integerWaveNormSq_nonneg wave
  have rightNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq wave) * ‖value‖ := by
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) rightNonneg).mp
  calc
    ‖fourierCurlCoefficient wave value‖ ^ 2 ≤
        (2 * Real.pi) ^ 2 *
          (integerWaveNormSq wave *
            complexCoordinateAmplitudeSq value) := squareBound
    _ ≤ (2 * Real.pi) ^ 2 *
          (integerWaveNormSq wave * (3 * ‖value‖ ^ 2)) := by
      gcongr
    _ ≤ ((6 * Real.pi) *
          Real.sqrt (integerWaveNormSq wave) * ‖value‖) ^ 2 := by
      nlinarith [Real.sq_sqrt waveNonneg,
        sq_nonneg (Real.pi * ‖value‖)]

/-- Source-generated cutoff-free upper bound for the whole physical velocity
displacement on one receipt interval. -/
def receiptKineticVelocityDriftUpper
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (a b : Icc (0 : Real) requestedTime) : Real :=
  Real.sqrt (3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2)

theorem receiptKineticVelocityDriftUpper_nonneg
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (a b : Icc (0 : Real) requestedTime) :
    0 ≤ receiptKineticVelocityDriftUpper receipt a b :=
  Real.sqrt_nonneg _

theorem receipt_wholeBiotSavartVelocity_sub_norm_le_driftUpper
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    ‖wholeBiotSavartVelocityState (receipt.wholePath b) -
        wholeBiotSavartVelocityState (receipt.wholePath a)‖ ≤
      receiptKineticVelocityDriftUpper receipt a b := by
  have squareBound :=
    receipt_wholeBiotSavartVelocity_sub_norm_sq_le_wholeTangent
      receipt a b hab
  have rightNonneg :
      0 ≤ 3 * (b.1 - a.1) * ‖receipt.wholeTangent‖ ^ 2 := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)) (sq_nonneg _)
  unfold receiptKineticVelocityDriftUpper
  exact (Real.le_sqrt (norm_nonneg _) rightNonneg).2 squareBound

/-- Fixed-output nonlinear drift of the actual whole receipt, paid entirely
by its complete kinetic tangent row.  No whole-vorticity tail norm, observed
frequency inventory, or same-space viscous bound appears. -/
theorem receipt_wholeVorticityNonlinearCoefficient_sub_norm_le_kineticDrift
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    ‖wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath b) output -
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath a) output‖ ≤
      ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          receiptKineticVelocityDriftUpper receipt a b *
          (‖wholeBiotSavartVelocityState (receipt.wholePath b)‖ +
            ‖wholeBiotSavartVelocityState (receipt.wholePath a)‖)) := by
  let velocityB := wholeBiotSavartVelocityState (receipt.wholePath b)
  let velocityA := wholeBiotSavartVelocityState (receipt.wholePath a)
  have bZero : receipt.wholePath b 0 = 0 := receipt.wholePath_zero_row b
  have aZero : receipt.wholePath a 0 = 0 := receipt.wholePath_zero_row a
  have bTransverse := wholePath_transverse receipt b
  have aTransverse := wholePath_transverse receipt a
  have nonlinearB :=
    wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity
      (receipt.wholePath b) bZero bTransverse output
  have nonlinearA :=
    wholeStateVorticityNonlinearCoefficientAt_eq_fourierCurl_velocity
      (receipt.wholePath a) aZero aTransverse output
  have velocityDifference :=
    wholeStateVelocityNonlinearCoefficientAt_sub_norm_le
      velocityB velocityA
      (wholeBiotSavartVelocityState_transverse (receipt.wholePath b))
      (wholeBiotSavartVelocityState_transverse (receipt.wholePath a)) output
  have drift :=
    receipt_wholeBiotSavartVelocity_sub_norm_le_driftUpper
      receipt a b hab
  rw [nonlinearB, nonlinearA]
  change
    ‖fourierCurlCoefficientContinuousLinearMap output
          (wholeStateVelocityNonlinearCoefficientAt velocityB output) -
        fourierCurlCoefficientContinuousLinearMap output
          (wholeStateVelocityNonlinearCoefficientAt velocityA output)‖ ≤ _
  rw [← map_sub]
  calc
    ‖fourierCurlCoefficientContinuousLinearMap output
        (wholeStateVelocityNonlinearCoefficientAt velocityB output -
          wholeStateVelocityNonlinearCoefficientAt velocityA output)‖ ≤
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
          ‖wholeStateVelocityNonlinearCoefficientAt velocityB output -
            wholeStateVelocityNonlinearCoefficientAt velocityA output‖ := by
      simpa only [fourierCurlCoefficientContinuousLinearMap_apply] using
        fourierCurlCoefficient_norm_le_six_pi_sqrt output
          (wholeStateVelocityNonlinearCoefficientAt velocityB output -
            wholeStateVelocityNonlinearCoefficientAt velocityA output)
    _ ≤ ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          ‖velocityB - velocityA‖ *
          (‖velocityB‖ + ‖velocityA‖)) :=
      mul_le_mul_of_nonneg_left velocityDifference (by positivity)
    _ ≤ ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          receiptKineticVelocityDriftUpper receipt a b *
          (‖velocityB‖ + ‖velocityA‖)) := by
      have angularNonneg :
          0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) := by
        positivity
      have velocitySumNonneg : 0 ≤ ‖velocityB‖ + ‖velocityA‖ := by
        positivity
      gcongr
    _ = _ := by rfl

/-- The complete fixed-output NS tangent inherits the cutoff-free kinetic
drift.  Both its nonlinear and viscous rows are projections of the same
actual velocity displacement. -/
theorem receipt_wholeLatticeVorticityTangent_sub_norm_le_kineticDrift
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt :
      WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (a b : Icc (0 : Real) requestedTime)
    (hab : a.1 ≤ b.1) :
    ‖wholeLatticeVorticityFourierTangentAt nu.coeff
          (receipt.wholePath b) output -
        wholeLatticeVorticityFourierTangentAt nu.coeff
          (receipt.wholePath a) output‖ ≤
      ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
        (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (‖wholeBiotSavartVelocityState (receipt.wholePath b)‖ +
              ‖wholeBiotSavartVelocityState (receipt.wholePath a)‖) +
          nu.coeff * integerWaveViscousMultiplier output) *
          receiptKineticVelocityDriftUpper receipt a b) := by
  let stateB := receipt.wholePath b
  let stateA := receipt.wholePath a
  let velocityB := wholeBiotSavartVelocityState stateB
  let velocityA := wholeBiotSavartVelocityState stateA
  let curl := fourierCurlCoefficientContinuousLinearMap output
  let damping := nu.coeff * integerWaveViscousMultiplier output
  have nonlinear :=
    receipt_wholeVorticityNonlinearCoefficient_sub_norm_le_kineticDrift
      receipt output a b hab
  have stateBTransverse := wholePath_transverse receipt b
  have stateATransverse := wholePath_transverse receipt a
  have rowB : stateB output = curl (velocityB output) := by
    dsimp only [stateB, velocityB, curl]
    change receipt.wholePath b output =
      fourierCurlCoefficient output
        (biotSavartVelocityCoefficient output (receipt.wholePath b output))
    exact (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
      output (receipt.wholePath b output) outputNe
      (stateBTransverse output)).symm
  have rowA : stateA output = curl (velocityA output) := by
    dsimp only [stateA, velocityA, curl]
    change receipt.wholePath a output =
      fourierCurlCoefficient output
        (biotSavartVelocityCoefficient output (receipt.wholePath a output))
    exact (fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse
      output (receipt.wholePath a output) outputNe
      (stateATransverse output)).symm
  have velocityRowDifference :
      ‖velocityB output - velocityA output‖ ≤
        receiptKineticVelocityDriftUpper receipt a b := by
    exact (lp.norm_apply_le_norm (by norm_num)
      (velocityB - velocityA) output).trans
        (receipt_wholeBiotSavartVelocity_sub_norm_le_driftUpper
          receipt a b hab)
  have vorticityRowDifference :
      ‖stateB output - stateA output‖ ≤
        ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
          receiptKineticVelocityDriftUpper receipt a b := by
    rw [rowB, rowA, ← map_sub]
    exact (fourierCurlCoefficient_norm_le_six_pi_sqrt output
      (velocityB output - velocityA output)).trans
        (mul_le_mul_of_nonneg_left velocityRowDifference (by positivity))
  have dampingNonneg : 0 ≤ damping := by
    dsimp only [damping]
    exact mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  unfold wholeLatticeVorticityFourierTangentAt
  rw [show
      (wholeStateVorticityNonlinearCoefficientAt stateB output -
          damping • stateB output) -
        (wholeStateVorticityNonlinearCoefficientAt stateA output -
          damping • stateA output) =
      (wholeStateVorticityNonlinearCoefficientAt stateB output -
          wholeStateVorticityNonlinearCoefficientAt stateA output) -
        damping • (stateB output - stateA output) by module]
  calc
    ‖(wholeStateVorticityNonlinearCoefficientAt stateB output -
          wholeStateVorticityNonlinearCoefficientAt stateA output) -
        damping • (stateB output - stateA output)‖ ≤
      ‖wholeStateVorticityNonlinearCoefficientAt stateB output -
          wholeStateVorticityNonlinearCoefficientAt stateA output‖ +
        ‖damping • (stateB output - stateA output)‖ := norm_sub_le _ _
    _ ≤ ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
          ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            receiptKineticVelocityDriftUpper receipt a b *
              (‖velocityB‖ + ‖velocityA‖)) +
        damping * (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
          receiptKineticVelocityDriftUpper receipt a b) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg dampingNonneg]
      exact add_le_add nonlinear
        (mul_le_mul_of_nonneg_left vorticityRowDifference dampingNonneg)
    _ = ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
        (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (‖velocityB‖ + ‖velocityA‖) + damping) *
          receiptKineticVelocityDriftUpper receipt a b) := by ring
    _ = _ := by rfl

/-! ## Uniform source readout on one canonical full replay -/

/-- Cutoff-free velocity radius of the unchanged canonical full receipt. -/
def fullReplayKineticVelocityRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  Real.sqrt
    (3 * wholeRestartCoefficientCeiling current.contact)

theorem fullReplayKineticVelocityRadius_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    0 ≤ fullReplayKineticVelocityRadius current :=
  Real.sqrt_nonneg _

theorem fullReplay_wholeBiotSavartVelocity_norm_le_radius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    ‖wholeBiotSavartVelocityState
        (current.nextReceipt.wholePath time)‖ ≤
      fullReplayKineticVelocityRadius current := by
  have stateNormSqLe :
      ‖current.nextReceipt.wholePath time‖ ^ 2 ≤
        wholeRestartCoefficientCeiling current.contact :=
    (wholeState_norm_sq_le_wholeVorticityEuclideanMass _).trans
      (fullReplayWholeMass_le_coefficientCeiling current time)
  have velocityNormSqLe :=
    wholeBiotSavartVelocityState_norm_sq_le_three_mul
      (current.nextReceipt.wholePath time)
  have combined :
      ‖wholeBiotSavartVelocityState
          (current.nextReceipt.wholePath time)‖ ^ 2 ≤
        3 * wholeRestartCoefficientCeiling current.contact :=
    velocityNormSqLe.trans
      (mul_le_mul_of_nonneg_left stateNormSqLe (by norm_num))
  have rightNonneg :
      0 ≤ 3 * wholeRestartCoefficientCeiling current.contact :=
    mul_nonneg (by norm_num)
      (wholeRestartCoefficientCeiling_pos current.contact).le
  unfold fullReplayKineticVelocityRadius
  exact (Real.le_sqrt (norm_nonneg _) rightNonneg).2 combined

theorem fullReplay_initialWholeBiotSavartVelocity_norm_le_radius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ‖wholeBiotSavartVelocityState current.contact.physicalState‖ ≤
      fullReplayKineticVelocityRadius current := by
  let zeroTime : Icc (0 : Real)
      (wholeRestartDuration current.contact) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
  have initialEq : current.nextReceipt.wholePath zeroTime =
      current.contact.physicalState := current.nextReceipt.wholePath_initial
  rw [← initialEq]
  exact fullReplay_wholeBiotSavartVelocity_norm_le_radius current zeroTime

/-- Maximum kinetic velocity displacement generated by the complete
canonical full-replay horizon. -/
def fullReplayKineticVelocityDriftUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  Real.sqrt
    (3 * wholeRestartDuration current.contact *
      ‖current.nextReceipt.wholeTangent‖ ^ 2)

theorem fullReplayKineticVelocityDriftUpper_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    0 ≤ fullReplayKineticVelocityDriftUpper current :=
  Real.sqrt_nonneg _

/-- Source-only upper bound for the complete whole tangent square.  The
signed endpoint term in the exact Euclidean balance is retained and then
paid by the nonnegative target mass; no future monotonicity premise is used. -/
def fullReplayWholeTangentSquareSourceUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) : Real :=
  ((9 * 1557504 * biotSavartSerrinConstant ^ 2) /
      (2 * (nu.coeff ^ 2 * (2 * Real.pi) ^ 2))) *
      (wholeRestartCoefficientCeiling current.contact ^ 3 *
        wholeRestartDuration current.contact) +
    nu.coeff * wholeRestartCoefficientCeiling current.contact

theorem fullReplayWholeTangentSquare_le_sourceUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    ‖current.nextReceipt.wholeTangent‖ ^ 2 ≤
      fullReplayWholeTangentSquareSourceUpper current := by
  let receipt := current.nextReceipt
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let terminal : Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨wholeRestartDuration current.contact,
      ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩
  have massBound : ∀ᵐ time
      ∂(commonTimeMeasure (wholeRestartDuration current.contact)),
      wholeVorticityEuclideanMass (receipt.wholePath time) ≤ ceiling :=
    Filter.Eventually.of_forall fun time => by
      simpa only [receipt, ceiling] using
        fullReplayWholeMass_le_coefficientCeiling current time
  have signed :=
    receipt_tangentHalfViscousSquare_add_boundary_le_cubicTime
      receipt massBound
  have tangentLeEuclidean :=
    receiptWholeTangentSquare_le_euclideanSquare receipt
  have viscousNonneg :
      0 ≤ puncturedEuclideanSpaceTimeSquare
        (receiptViscousNegativeOneState receipt) := by
    unfold puncturedEuclideanSpaceTimeSquare
    positivity
  have targetNonneg :
      0 ≤ wholeVorticityEuclideanMass (receipt.wholePath terminal) :=
    by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
  have sourceLe :
      wholeVorticityEuclideanMass current.contact.physicalState ≤
        ceiling := by
    have rawLe := wholeRestartRawCoefficientCeiling_le current.contact
    rw [wholeRestartRawCoefficientCeiling_eq] at rawLe
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
      at rawLe
    dsimp only [ceiling]
    linarith
  unfold fullReplayWholeTangentSquareSourceUpper
  dsimp only [receipt, ceiling, terminal] at signed tangentLeEuclidean viscousNonneg targetNonneg sourceLe ⊢
  nlinarith [nu.coeff_pos.le]

theorem fullReplayKineticVelocityDriftUpper_le_source
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu) :
    fullReplayKineticVelocityDriftUpper current ≤
      Real.sqrt
        (3 * wholeRestartDuration current.contact *
          fullReplayWholeTangentSquareSourceUpper current) := by
  unfold fullReplayKineticVelocityDriftUpper
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left
    (fullReplayWholeTangentSquare_le_sourceUpper current)
    (mul_nonneg (by norm_num)
      (wholeRestartDuration_pos current.contact).le)

theorem receiptKineticVelocityDriftUpper_le_fullReplay
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (time : Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    let zeroTime : Icc (0 : Real)
        (wholeRestartDuration current.contact) :=
      ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
    receiptKineticVelocityDriftUpper current.nextReceipt zeroTime time ≤
      fullReplayKineticVelocityDriftUpper current := by
  dsimp only
  unfold receiptKineticVelocityDriftUpper
    fullReplayKineticVelocityDriftUpper
  simp only [sub_zero]
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left time.2.2 (by norm_num))
    (sq_nonneg _)

/-- Uniform fixed-output tangent error generated from the complete kinetic
ledger of the same current. -/
def fullReplayKineticTangentDriftUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) : Real :=
  ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
    (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (2 * fullReplayKineticVelocityRadius current) +
      nu.coeff * integerWaveViscousMultiplier output) *
      fullReplayKineticVelocityDriftUpper current)

/-- Fully source-readable replacement of the actual tangent norm in the
kinetic fixed-output remainder. -/
def fullReplayKineticTangentSourceUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) : Real :=
  ((6 * Real.pi) * Real.sqrt (integerWaveNormSq output)) *
    (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
        (2 * fullReplayKineticVelocityRadius current) +
      nu.coeff * integerWaveViscousMultiplier output) *
      Real.sqrt
        (3 * wholeRestartDuration current.contact *
          fullReplayWholeTangentSquareSourceUpper current))

theorem fullReplayKineticTangentDriftUpper_le_sourceUpper
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) :
    fullReplayKineticTangentDriftUpper current output ≤
      fullReplayKineticTangentSourceUpper current output := by
  unfold fullReplayKineticTangentDriftUpper
    fullReplayKineticTangentSourceUpper
  have coefficientNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
          (2 * fullReplayKineticVelocityRadius current) +
        nu.coeff * integerWaveViscousMultiplier output := by
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)
          (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num)
          (fullReplayKineticVelocityRadius_nonneg current))
    · exact mul_nonneg nu.coeff_pos.le (by
        unfold integerWaveViscousMultiplier
        exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (fullReplayKineticVelocityDriftUpper_le_source current)
      coefficientNonneg)
    (by positivity)

theorem fullReplayKineticTangentDriftUpper_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) :
    0 ≤ fullReplayKineticTangentDriftUpper current output := by
  unfold fullReplayKineticTangentDriftUpper
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier output := by
    exact mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  exact mul_nonneg (by positivity)
    (mul_nonneg
      (add_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) Real.pi_pos.le)
            (Real.sqrt_nonneg _))
          (mul_nonneg (by norm_num)
            (fullReplayKineticVelocityRadius_nonneg current)))
        dampingNonneg)
      (fullReplayKineticVelocityDriftUpper_nonneg current))

theorem fullReplayEulerErrorDerivative_norm_le_kinetic
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (actual : Real)
    (actualMem : actual ∈ Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    ‖fullReplayEulerErrorDerivative current output actual‖ ≤
      fullReplayKineticTangentDriftUpper current output := by
  let receipt := current.nextReceipt
  let zeroTime : Icc (0 : Real)
      (wholeRestartDuration current.contact) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
  let physicalTime : Icc (0 : Real)
      (wholeRestartDuration current.contact) := ⟨actual, actualMem⟩
  let pathState : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  have pathStateEq : pathState = receipt.wholePath physicalTime := by
    change receipt.wholePath
        (Set.projIcc 0 (wholeRestartDuration current.contact)
          (wholeRestartDuration_pos current.contact).le actual) =
      receipt.wholePath physicalTime
    rw [Set.projIcc_of_mem
      (wholeRestartDuration_pos current.contact).le actualMem]
  have heatPathEq :
      actualWholeContinuousHeatDuhamelPath receipt output actual =
        receipt.wholePath physicalTime output :=
    (wholePath_wave_eq_actualWholeContinuousHeatDuhamelPath
      receipt output outputNe physicalTime).symm
  have generated :=
    receipt_wholeLatticeVorticityTangent_sub_norm_le_kineticDrift
      receipt output outputNe zeroTime physicalTime actualMem.1
  have driftLe :=
    receiptKineticVelocityDriftUpper_le_fullReplay current physicalTime
  have pathVelocityLe :=
    fullReplay_wholeBiotSavartVelocity_norm_le_radius current physicalTime
  have initialVelocityLe :=
    fullReplay_initialWholeBiotSavartVelocity_norm_le_radius current
  have velocitySumLe :
      ‖wholeBiotSavartVelocityState (receipt.wholePath physicalTime)‖ +
          ‖wholeBiotSavartVelocityState (receipt.wholePath zeroTime)‖ ≤
        2 * fullReplayKineticVelocityRadius current := by
    have zeroEq : receipt.wholePath zeroTime =
        current.contact.physicalState := receipt.wholePath_initial
    rw [zeroEq]
    linarith
  have angularNonneg :
      0 ≤ (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) := by
    positivity
  have dampingNonneg :
      0 ≤ nu.coeff * integerWaveViscousMultiplier output := by
    exact mul_nonneg nu.coeff_pos.le (by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg output))
  have coefficientLe :
      (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (‖wholeBiotSavartVelocityState (receipt.wholePath physicalTime)‖ +
              ‖wholeBiotSavartVelocityState (receipt.wholePath zeroTime)‖) +
          nu.coeff * integerWaveViscousMultiplier output ≤
        (6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (2 * fullReplayKineticVelocityRadius current) +
          nu.coeff * integerWaveViscousMultiplier output := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left velocitySumLe angularNonneg) le_rfl
  have productLe :
      (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (‖wholeBiotSavartVelocityState (receipt.wholePath physicalTime)‖ +
              ‖wholeBiotSavartVelocityState (receipt.wholePath zeroTime)‖) +
          nu.coeff * integerWaveViscousMultiplier output) *
          receiptKineticVelocityDriftUpper receipt zeroTime physicalTime) ≤
        (((6 * Real.pi) * Real.sqrt (integerWaveNormSq output) *
            (2 * fullReplayKineticVelocityRadius current) +
          nu.coeff * integerWaveViscousMultiplier output) *
          fullReplayKineticVelocityDriftUpper current) := by
    exact mul_le_mul coefficientLe driftLe
      (receiptKineticVelocityDriftUpper_nonneg receipt zeroTime physicalTime)
      (add_nonneg
        (mul_nonneg angularNonneg
          (mul_nonneg (by norm_num)
            (fullReplayKineticVelocityRadius_nonneg current))) dampingNonneg)
  unfold fullReplayEulerErrorDerivative
  rw [heatPathEq, ← pathStateEq]
  change
    ‖wholeLatticeVorticityFourierTangentAt nu.coeff pathState output -
      wholeLatticeVorticityFourierTangentAt nu.coeff
        current.contact.physicalState output‖ ≤ _
  rw [pathStateEq]
  have bounded := generated.trans
    (mul_le_mul_of_nonneg_left productLe (by positivity))
  have zeroEq : receipt.wholePath zeroTime =
      current.contact.physicalState := receipt.wholePath_initial
  simpa only [zeroEq, fullReplayKineticTangentDriftUpper] using bounded

/-- Sharper actual-receipt Euler remainder: its slope is generated by the
kinetic ledger and therefore vanishes with the full-replay horizon. -/
theorem fullReplay_row_sub_euler_norm_le_kinetic
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (time : Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    ‖current.nextReceipt.wholePath time output -
        fullReplayEulerRow current time.1 output‖ ≤
      time.1 * fullReplayKineticTangentDriftUpper current output := by
  rw [← fullReplayEulerError_integral_eq current output outputNe time]
  calc
    ‖∫ actual in (0 : Real)..time.1,
        fullReplayEulerErrorDerivative current output actual‖ ≤
        fullReplayKineticTangentDriftUpper current output *
          |time.1 - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro actual actualMem
      apply fullReplayEulerErrorDerivative_norm_le_kinetic
        current output outputNe actual
      rw [uIoc_of_le time.2.1] at actualMem
      exact ⟨actualMem.1.le, actualMem.2.trans time.2.2⟩
    _ = time.1 * fullReplayKineticTangentDriftUpper current output := by
      rw [sub_zero, abs_of_nonneg time.2.1]
      ring

theorem fullReplay_row_sub_euler_norm_le_kineticSource
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0)
    (time : Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    ‖current.nextReceipt.wholePath time output -
        fullReplayEulerRow current time.1 output‖ ≤
      time.1 * fullReplayKineticTangentSourceUpper current output := by
  exact (fullReplay_row_sub_euler_norm_le_kinetic
      current output outputNe time).trans
    (mul_le_mul_of_nonneg_left
      (fullReplayKineticTangentDriftUpper_le_sourceUpper current output)
      time.2.1)

def nextContactKineticEulerPaymentDensity
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector) : Real :=
  2 * complexCoordinateRealInner
      (current.contact.physicalState output)
      (wholeLatticeVorticityFourierTangentAt nu.coeff
        current.contact.physicalState output) -
    6 * ‖current.contact.physicalState output‖ *
      fullReplayKineticTangentSourceUpper current output

/-- Same-occurrence coefficient valuation generated by the cutoff-free
kinetic remainder. -/
theorem nextContact_amplitudeSq_sub_current_le_from_below_kineticSource
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (output : IntegerWavevector)
    (outputNe : output ≠ 0) :
    current.nextContact.time.1 *
        nextContactKineticEulerPaymentDensity current output ≤
      complexCoordinateAmplitudeSq
          (current.nextContact.physicalState output) -
        complexCoordinateAmplitudeSq
          (current.contact.physicalState output) := by
  let source := current.contact.physicalState output
  let tangent := wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState output
  let error := current.nextContact.physicalState output -
    fullReplayEulerRow current current.nextContact.time.1 output
  have errorNormLe : ‖error‖ ≤
      current.nextContact.time.1 *
        fullReplayKineticTangentSourceUpper current output := by
    change
      ‖current.nextReceipt.wholePath current.nextContact.time output -
        fullReplayEulerRow current current.nextContact.time.1 output‖ ≤ _
    exact fullReplay_row_sub_euler_norm_le_kineticSource
      current output outputNe current.nextContact.time
  have errorPairingAbs :=
    abs_complexCoordinateRealInner_le_three_mul_norm source error
  have errorPairingLower :
      -(3 * ‖source‖ * current.nextContact.time.1 *
          fullReplayKineticTangentSourceUpper current output) ≤
        complexCoordinateRealInner source error := by
    have scaled :
        |complexCoordinateRealInner source error| ≤
          3 * ‖source‖ * current.nextContact.time.1 *
            fullReplayKineticTangentSourceUpper current output := by
      calc
        |complexCoordinateRealInner source error| ≤
            3 * ‖source‖ * ‖error‖ := errorPairingAbs
        _ ≤ 3 * ‖source‖ *
            (current.nextContact.time.1 *
              fullReplayKineticTangentSourceUpper current output) :=
          mul_le_mul_of_nonneg_left errorNormLe (by positivity)
        _ = _ := by ring
    linarith [neg_abs_le (complexCoordinateRealInner source error)]
  have targetSubSource :
      current.nextContact.physicalState output - source =
        current.nextContact.time.1 • tangent + error := by
    dsimp only [source, tangent, error]
    unfold fullReplayEulerRow
    module
  have innerSplit :
      complexCoordinateRealInner source
          (current.nextContact.physicalState output - source) =
        current.nextContact.time.1 *
            complexCoordinateRealInner source tangent +
          complexCoordinateRealInner source error := by
    rw [targetSubSource, complexCoordinateRealInner_add_right,
      complexCoordinateRealInner_real_smul_right]
  have amplitudeDifference :=
    complexCoordinateAmplitudeSq_sub_eq_realInner_add source
      (current.nextContact.physicalState output)
  have differenceNonneg :
      0 ≤ complexCoordinateAmplitudeSq
        (current.nextContact.physicalState output - source) :=
    complexCoordinateAmplitudeSq_nonneg _
  rw [innerSplit] at amplitudeDifference
  unfold nextContactKineticEulerPaymentDensity
  dsimp only [source, tangent] at errorPairingLower amplitudeDifference ⊢
  linarith

end
end ThreeDimensionalVorticityCoefficientWholeReceiptKineticTimeModulus
end NavierStokes
end SaturationMonoid
