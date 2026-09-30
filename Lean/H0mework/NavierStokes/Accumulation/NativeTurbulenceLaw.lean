import H0mework.NavierStokes.Accumulation.DuhamelBoundary
import H0mework.NavierStokes.Accumulation.CofinalActionSettlement
import H0mework.NavierStokes.Accumulation.ScaleCriticalWindow
import H0mework.NavierStokes.Accumulation.BoundaryContinuation
import H0mework.NavierStokes.Fourier.PuncturedCanonicalGalerkinTarget
import H0mework.NavierStokes.Restart.EnstrophyWork
import H0mework.NavierStokes.Energy.ClosedEnstrophyPhysicalBridge
import H0mework.NavierStokes.Restart.GlobalPhysicalTrajectory

/-!
# Exact native turbulence completion

The original same-source boundary failure selects one canonical coface row.  This module decodes
that row as a Fourier and physical correction, integrates its enstrophy flux on the exact failure
blocks, and propagates the same correction through the nonlinear Duhamel and recovery-next writes.
These layers stay together because every identity is indexed by the identical correction and
source-owned receipt.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw

open scoped BigOperators Interval

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ResponsibilityLifecycle
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNonlinearDuhamelConcentration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationBoundaryContinuation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearDuhamelRegeneration
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNonlinearRegenerationCascade
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityPairDiagonalAction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPreQuotientNonlinearWork
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPositiveOutputWorkDualBudget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityNativeHighFrequencyProjectedParabolicTrace
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime.GeneratedInfiniteWholeRestartEndpointMacroLineage.FullFrameBoundaryVorticityCofinalNonlinearNegativeOneEuclideanBalance

noncomputable section

universe u

/-- Output projection of the genuine whole nonlinear row. -/
def projectedWholeNonlinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if wave ∈ modes then
    wholeStateVorticityNonlinearCoefficientAt state wave
  else 0

/-- The old finite carrier only pays the missing output rows. -/
def oldCarrierOutputCorrectionAt
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedWholeNonlinearCoefficientAt modes state wave -
    wholeStateVorticityNonlinearCoefficientAt state wave

/-- The new coface row pays the exact input-filter commutator. -/
def cofaceInputCorrectionAt
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedWholeNonlinearCoefficientAt modes wholeState wave -
    projectedWholeNonlinearCoefficientAt modes
      (complexSharpSupportProjection modes wholeState) wave

/-- Canonical native turbulence correction, with no free closure field. -/
def nativeTurbulenceCorrectionAt
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  projectedWholeNonlinearCoefficientAt modes wholeState wave -
    wholeStateVorticityNonlinearCoefficientAt
      (complexSharpSupportProjection modes wholeState) wave

theorem nativeTurbulenceCorrection_eq_old_add_coface
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    nativeTurbulenceCorrectionAt modes wholeState wave =
      oldCarrierOutputCorrectionAt modes
          (complexSharpSupportProjection modes wholeState) wave +
        cofaceInputCorrectionAt modes wholeState wave := by
  unfold nativeTurbulenceCorrectionAt oldCarrierOutputCorrectionAt
    cofaceInputCorrectionAt
  abel

/-- Exact Fourier filtered-NS equation with the canonical coface correction. -/
theorem projectedWholeTangent_eq_classical_add_nativeTurbulence
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    (if wave ∈ modes then
        wholeLatticeVorticityFourierTangentAt nu wholeState wave
      else 0) =
      wholeLatticeVorticityFourierTangentAt nu
          (complexSharpSupportProjection modes wholeState) wave +
        nativeTurbulenceCorrectionAt modes wholeState wave := by
  by_cases waveMem : wave ∈ modes
  · simp only [if_pos waveMem]
    unfold wholeLatticeVorticityFourierTangentAt
      nativeTurbulenceCorrectionAt projectedWholeNonlinearCoefficientAt
    rw [if_pos waveMem, complexSharpSupportProjection_apply, if_pos waveMem]
    abel
  · simp only [if_neg waveMem]
    unfold wholeLatticeVorticityFourierTangentAt
      nativeTurbulenceCorrectionAt projectedWholeNonlinearCoefficientAt
    rw [if_neg waveMem, complexSharpSupportProjection_apply, if_neg waveMem]
    simp

/-- On a classically realizable old carrier the native correction is exactly zero. -/
theorem nativeTurbulenceCorrection_eq_zero_of_oldRealizable
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState)
    (stateSupported :
      complexSharpSupportProjection modes wholeState = wholeState)
    (nonlinearSupported :
      ∀ wave : IntegerWavevector, wave ∉ modes →
        wholeStateVorticityNonlinearCoefficientAt wholeState wave = 0)
    (wave : IntegerWavevector) :
    nativeTurbulenceCorrectionAt modes wholeState wave = 0 := by
  unfold nativeTurbulenceCorrectionAt projectedWholeNonlinearCoefficientAt
  rw [stateSupported]
  by_cases waveMem : wave ∈ modes
  · simp [waveMem]
  · simp [waveMem, nonlinearSupported wave waveMem]

/-- Physical compilation of the whole nonlinear row observed on the old carrier. -/
def projectedWholeNonlinearField
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  finiteRealComplexFourierField modes
    (wholeStateVorticityNonlinearCoefficientAt wholeState)

/-- Physical classical nonlinearity of the resolved state, on its complete output table. -/
def resolvedWholeNonlinearField
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  let projected := complexSharpSupportProjection modes wholeState
  let source := rawSourceOfFiniteVorticityState modes projected
  finiteRealComplexFourierField
    (generatedStretchingOutputInventory source)
    (wholeStateVorticityNonlinearCoefficientAt projected)

/-- Physical-space native correction generated by the two canonical compilers. -/
def nativeTurbulenceCorrectionField
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  projectedWholeNonlinearField modes wholeState -
    resolvedWholeNonlinearField modes wholeState

/-- Exact physical-space closure law. -/
theorem projectedWholeNonlinearField_eq_resolved_add_nativeTurbulence
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    projectedWholeNonlinearField modes wholeState =
      resolvedWholeNonlinearField modes wholeState +
        nativeTurbulenceCorrectionField modes wholeState := by
  unfold nativeTurbulenceCorrectionField
  abel

/-- Viscous Fourier field of the resolved state. -/
def resolvedViscousField
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  let projected := complexSharpSupportProjection modes wholeState
  finiteRealComplexFourierField modes fun wave =>
    (nu * integerWaveViscousMultiplier wave) • projected wave

/-- Projected actual physical tangent. -/
def projectedWholePhysicalTangent
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  projectedWholeNonlinearField modes wholeState -
    resolvedViscousField modes nu wholeState

/-- Classical physical tangent of the resolved vorticity. -/
def resolvedClassicalPhysicalTangent
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState) :
    PhysicalSpace → PhysicalSpace :=
  resolvedWholeNonlinearField modes wholeState -
    resolvedViscousField modes nu wholeState

/-- Exact physical-space vorticity equation, including viscosity. -/
theorem projectedWholePhysicalTangent_eq_classical_add_nativeTurbulence
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState) :
    projectedWholePhysicalTangent modes nu wholeState =
      resolvedClassicalPhysicalTangent modes nu wholeState +
        nativeTurbulenceCorrectionField modes wholeState := by
  unfold projectedWholePhysicalTangent resolvedClassicalPhysicalTangent
  rw [projectedWholeNonlinearField_eq_resolved_add_nativeTurbulence]
  abel

/-- Enstrophy transfer paid specifically by the generated coface row. -/
def nativeTurbulenceEnstrophyFlux
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) : Real :=
  let projected := complexSharpSupportProjection modes wholeState
  ∑ wave ∈ modes,
    complexCoordinateRealInner (projected wave)
      (cofaceInputCorrectionAt modes wholeState wave)

/-- The observed whole nonlinear work is autonomous resolved work plus the
canonical coface flux. -/
theorem projectedWholeNonlinearWork_eq_resolved_add_nativeTurbulenceFlux
    (modes : Finset IntegerWavevector)
    (wholeState : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner
        ((complexSharpSupportProjection modes wholeState) wave)
        (wholeStateVorticityNonlinearCoefficientAt wholeState wave)) =
      finiteStateVorticityNonlinearWork modes
          (complexSharpSupportProjection modes wholeState) +
        nativeTurbulenceEnstrophyFlux modes wholeState := by
  let projected := complexSharpSupportProjection modes wholeState
  have supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → projected wave = 0 := by
    intro wave waveNotMem
    simp [projected, complexSharpSupportProjection_apply, waveNotMem]
  have nonlinearEq (wave : IntegerWavevector) :
      wholeStateVorticityNonlinearCoefficientAt projected wave =
        finiteStateVorticityNonlinearCoefficientAt modes projected wave :=
    wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
      modes projected supported wave
  unfold finiteStateVorticityNonlinearWork
    nativeTurbulenceEnstrophyFlux cofaceInputCorrectionAt
    projectedWholeNonlinearCoefficientAt
  dsimp only [projected]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [if_pos waveMem, if_pos waveMem]
  rw [← nonlinearEq]
  rw [complexCoordinateRealInner_sub_right]
  ring

/-- Exact full tangent/enstrophy-work identity.  The only term beyond the
classical resolved generator is the native coface flux. -/
theorem projectedWholeTangentWork_eq_resolvedGenerator_add_nativeFlux
    (modes : Finset IntegerWavevector)
    (nu : Real)
    (wholeState : ComplexVorticityHilbertState) :
    let projected := complexSharpSupportProjection modes wholeState
    (∑ wave ∈ modes,
      complexCoordinateRealInner (projected wave)
        (wholeLatticeVorticityFourierTangentAt nu wholeState wave)) =
      (∑ wave ∈ modes,
        complexCoordinateRealInner (projected wave)
          (finiteStateVorticityGenerator modes nu projected wave)) +
        nativeTurbulenceEnstrophyFlux modes wholeState := by
  dsimp only
  have nonlinearSplit :=
    projectedWholeNonlinearWork_eq_resolved_add_nativeTurbulenceFlux
      modes wholeState
  have viscousEq :
      (∑ wave ∈ modes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection modes wholeState) wave)
          ((nu * integerWaveViscousMultiplier wave) • wholeState wave)) =
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          ((complexSharpSupportProjection modes wholeState) wave)
          ((nu * integerWaveViscousMultiplier wave) •
            (complexSharpSupportProjection modes wholeState) wave) := by
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  rw [finiteStateVorticityGenerator_realWork]
  rw [← finiteStateVorticityViscousWork_eq]
  unfold wholeLatticeVorticityFourierTangentAt
  simp_rw [complexCoordinateRealInner_sub_right]
  rw [Finset.sum_sub_distrib, viscousEq]
  linarith

/-! ## Exact receipt integration of the native flux -/

/-- Complete retained-output enstrophy power of the actual whole state. -/
def actualProjectedWholeEnstrophyPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  let state := (actualWholeProjectedTransversePath receipt actual).1
  2 * ∑ wave ∈ modes,
    complexCoordinateRealInner
      ((complexSharpSupportProjection modes state) wave)
      (wholeStateVorticityNonlinearCoefficientAt state wave)

/-- Classical resolved contribution to the same actual enstrophy power. -/
def actualResolvedEnstrophyPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  let state := (actualWholeProjectedTransversePath receipt actual).1
  2 * finiteStateVorticityNonlinearWork modes
    (complexSharpSupportProjection modes state)

/-- Instantaneous enstrophy flux paid by the native correction. -/
def actualNativeTurbulenceEnstrophyFluxPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  let state := (actualWholeProjectedTransversePath receipt actual).1
  2 * nativeTurbulenceEnstrophyFlux modes state

theorem actualProjectedWholeEnstrophyPower_eq_resolved_add_native
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) :
    actualProjectedWholeEnstrophyPower receipt modes actual =
      actualResolvedEnstrophyPower receipt modes actual +
        actualNativeTurbulenceEnstrophyFluxPower receipt modes actual := by
  let state : ComplexVorticityHilbertState :=
    (actualWholeProjectedTransversePath receipt actual).1
  change
    2 * (∑ wave ∈ modes,
      complexCoordinateRealInner
        ((complexSharpSupportProjection modes state) wave)
        (wholeStateVorticityNonlinearCoefficientAt state wave)) =
      2 * finiteStateVorticityNonlinearWork modes
          (complexSharpSupportProjection modes state) +
        2 * nativeTurbulenceEnstrophyFlux modes state
  rw [projectedWholeNonlinearWork_eq_resolved_add_nativeTurbulenceFlux]
  ring

private theorem actualWholeRowBilinearWork_eq_projectedPower_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    actualWholeRowBilinearWork receipt wave =
      ∫ actual in (0 : Real)..requestedTime,
        2 * complexCoordinateRealInner
          ((actualWholeProjectedTransversePath receipt actual).1 wave)
          (wholeStateVorticityNonlinearCoefficientAt
            (actualWholeProjectedTransversePath receipt actual).1 wave) := by
  unfold actualWholeRowBilinearWork
  rw [dif_neg waveNe]
  rw [← commonTime_integral_eq_intervalIntegral
      requestedTime receipt.requestedTimePos.le,
    ← commonTime_integral_eq_intervalIntegral
      requestedTime receipt.requestedTimePos.le]
  apply integral_congr_ae
  filter_upwards [receipt.wholePath_eq_transverse_ae] with time pathEq
  have rowEq :
      receipt.rowExtension wave waveNe time.1 =
        (receipt.transverseLimit time).1 wave := by
    rw [receipt.rowExtension_on_interval wave waveNe time, pathEq]
  have projectedEq :
      (actualWholeProjectedTransversePath receipt time.1).1 =
        (receipt.transverseLimit time).1 := by
    change
      receipt.wholePath
          (Set.projIcc (0 : Real) requestedTime
            receipt.requestedTimePos.le time.1) =
        (receipt.transverseLimit time).1
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le time.property,
      pathEq]
  have nonlinearEq :=
    commonTimeZeroExtension_of_mem requestedTime
      (fun localTime =>
        wholeStateVorticityBilinearCoefficientAt
          (receipt.transverseLimit localTime).1
          (receipt.transverseLimit localTime).1 wave)
      time.1 time.property
  rw [rowEq, nonlinearEq, projectedEq]
  rfl

private theorem actualWholeRowProjectedPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector) :
    Continuous fun actual : Real =>
      2 * complexCoordinateRealInner
        ((actualWholeProjectedTransversePath receipt actual).1 wave)
        (wholeStateVorticityNonlinearCoefficientAt
          (actualWholeProjectedTransversePath receipt actual).1 wave) := by
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous receipt)
  have rowContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp stateContinuous
  have nonlinearContinuous :
      Continuous fun actual : Real =>
        wholeStateVorticityNonlinearCoefficientAt
          (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
      (actualWholeProjectedTransversePath_continuous receipt)
  exact (complexCoordinateRealInner_prod_continuous.comp
    (rowContinuous.prodMk nonlinearContinuous)).const_mul 2

/-- Physical projected whole-state enstrophy power is continuous on the
receipt's real-time representative. -/
theorem actualProjectedWholeEnstrophyPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous (actualProjectedWholeEnstrophyPower receipt modes) := by
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous receipt)
  unfold actualProjectedWholeEnstrophyPower
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro wave waveMem
  have stateRowContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp stateContinuous
  have projectedRowContinuous :
      Continuous fun actual : Real =>
        (complexSharpSupportProjection modes
          (actualWholeProjectedTransversePath receipt actual).1) wave := by
    simpa only [complexSharpSupportProjection_apply, if_pos waveMem] using
      stateRowContinuous
  have nonlinearContinuous :
      Continuous fun actual : Real =>
        wholeStateVorticityNonlinearCoefficientAt
          (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
      (actualWholeProjectedTransversePath_continuous receipt)
  exact complexCoordinateRealInner_prod_continuous.comp
    (projectedRowContinuous.prodMk nonlinearContinuous)

private theorem complexSharpSupportProjection_continuous_native
    (modes : Finset IntegerWavevector) :
    Continuous (complexSharpSupportProjection modes) := by
  have contractive :
      LipschitzWith 1 (complexSharpSupportProjection modes) := by
    apply LipschitzWith.of_dist_le_mul
    intro left right
    simpa using complexSharpSupportProjection_dist_le modes left right
  exact contractive.continuous

private theorem actualResolvedEnstrophyPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous (actualResolvedEnstrophyPower receipt modes) := by
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous receipt)
  have projectedContinuous :
      Continuous fun actual : Real =>
        complexSharpSupportProjection modes
          (actualWholeProjectedTransversePath receipt actual).1 :=
    (complexSharpSupportProjection_continuous_native modes).comp
      stateContinuous
  unfold actualResolvedEnstrophyPower finiteStateVorticityNonlinearWork
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro wave _waveMem
  have projectedRowContinuous :
      Continuous fun actual : Real =>
        (complexSharpSupportProjection modes
          (actualWholeProjectedTransversePath receipt actual).1) wave :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp projectedContinuous
  have nonlinearContinuous :
      Continuous fun actual : Real =>
        finiteStateVorticityNonlinearCoefficientAt modes
          (complexSharpSupportProjection modes
            (actualWholeProjectedTransversePath receipt actual).1) wave :=
    (finiteStateVorticityNonlinearCoefficientAt_contDiff modes wave)
      |>.continuous.comp projectedContinuous
  exact complexCoordinateRealInner_prod_continuous.comp
    (projectedRowContinuous.prodMk nonlinearContinuous)

private theorem actualNativeTurbulenceEnstrophyFluxPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous (actualNativeTurbulenceEnstrophyFluxPower receipt modes) := by
  have functionEq :
      actualNativeTurbulenceEnstrophyFluxPower receipt modes =
        actualProjectedWholeEnstrophyPower receipt modes -
          actualResolvedEnstrophyPower receipt modes := by
    funext actual
    have split :=
      actualProjectedWholeEnstrophyPower_eq_resolved_add_native
        receipt modes actual
    change actualNativeTurbulenceEnstrophyFluxPower receipt modes actual =
      actualProjectedWholeEnstrophyPower receipt modes actual -
        actualResolvedEnstrophyPower receipt modes actual
    linarith
  rw [functionEq]
  exact
    (actualProjectedWholeEnstrophyPower_continuous receipt modes).sub
      (actualResolvedEnstrophyPower_continuous receipt modes)

/-- Integrated classical resolved enstrophy transfer on one actual receipt. -/
def actualResolvedEnstrophyWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) : Real :=
  ∫ actual in (0 : Real)..requestedTime,
    actualResolvedEnstrophyPower receipt modes actual

/-- Integrated native enstrophy flux on the identical receipt and modes. -/
def actualNativeTurbulenceEnstrophyFluxWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) : Real :=
  ∫ actual in (0 : Real)..requestedTime,
    actualNativeTurbulenceEnstrophyFluxPower receipt modes actual

/-- The complete pair-occurrence work on a punctured finite inventory is the
integral of the physical whole-state power seen by that same inventory. -/
theorem actualWholeFinitePairOccurrenceWork_eq_projectedPower_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFinitePairOccurrenceWork receipt modes =
      ∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeEnstrophyPower receipt modes actual := by
  rw [actualWholeFinitePairOccurrenceWork_eq_preQuotientWork
    receipt modes zeroNotMem]
  rw [actualWholeFinitePreQuotientWork_eq_bilinearWork]
  unfold actualWholeFiniteBilinearWork
  calc
    (∑ wave ∈ modes, actualWholeRowBilinearWork receipt wave) =
        ∑ wave ∈ modes,
          ∫ actual in (0 : Real)..requestedTime,
            2 * complexCoordinateRealInner
              ((actualWholeProjectedTransversePath receipt actual).1 wave)
              (wholeStateVorticityNonlinearCoefficientAt
                (actualWholeProjectedTransversePath receipt actual).1 wave) := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      exact actualWholeRowBilinearWork_eq_projectedPower_integral
        receipt wave (fun waveZero => zeroNotMem (waveZero ▸ waveMem))
    _ = ∫ actual in (0 : Real)..requestedTime,
          ∑ wave ∈ modes,
            2 * complexCoordinateRealInner
              ((actualWholeProjectedTransversePath receipt actual).1 wave)
              (wholeStateVorticityNonlinearCoefficientAt
                (actualWholeProjectedTransversePath receipt actual).1 wave) := by
      rw [← intervalIntegral.integral_finsetSum]
      intro wave _waveMem
      exact (actualWholeRowProjectedPower_continuous receipt wave).intervalIntegrable
        0 requestedTime
    _ = ∫ actual in (0 : Real)..requestedTime,
          actualProjectedWholeEnstrophyPower receipt modes actual := by
      apply intervalIntegral.integral_congr
      intro actual _actualMem
      unfold actualProjectedWholeEnstrophyPower
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [complexSharpSupportProjection_apply, if_pos waveMem]

/-- The actual complete pair table is exactly classical resolved work plus
the time-integrated native coface flux. -/
theorem actualWholeFinitePairOccurrenceWork_eq_resolved_add_nativeFluxWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFinitePairOccurrenceWork receipt modes =
      actualResolvedEnstrophyWork receipt modes +
        actualNativeTurbulenceEnstrophyFluxWork receipt modes := by
  rw [actualWholeFinitePairOccurrenceWork_eq_projectedPower_integral
    receipt modes zeroNotMem]
  unfold actualResolvedEnstrophyWork
    actualNativeTurbulenceEnstrophyFluxWork
  rw [← intervalIntegral.integral_add
    (actualResolvedEnstrophyPower_continuous receipt modes
      |>.intervalIntegrable 0 requestedTime)
    (actualNativeTurbulenceEnstrophyFluxPower_continuous receipt modes
      |>.intervalIntegrable 0 requestedTime)]
  apply intervalIntegral.integral_congr
  intro actual _actualMem
  exact actualProjectedWholeEnstrophyPower_eq_resolved_add_native
    receipt modes actual

/-! ## Exact Duhamel propagation of the native correction -/

/-- Heat-weighted whole nonlinear row retained by the old output carrier. -/
def projectedReceiptWeightedNonlinearDuhamelAt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : ComplexCoordinateVector :=
  ∫ earlier in Iic time,
    finiteStateVorticityHeatMultiplier
        nu.coeff (time.1 - earlier.1) wave •
      projectedWholeNonlinearCoefficientAt
        modes (receipt.wholePath earlier) wave
    ∂(commonTimeMeasure requestedTime)

/-- Heat-weighted classical nonlinear row of the resolved state. -/
def resolvedReceiptWeightedNonlinearDuhamelAt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : ComplexCoordinateVector :=
  ∫ earlier in Iic time,
    finiteStateVorticityHeatMultiplier
        nu.coeff (time.1 - earlier.1) wave •
      wholeStateVorticityNonlinearCoefficientAt
        (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave
    ∂(commonTimeMeasure requestedTime)

/-- Heat-weighted Duhamel write generated by the native coface correction. -/
def nativeTurbulenceWeightedDuhamelAt
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) : ComplexCoordinateVector :=
  ∫ earlier in Iic time,
    finiteStateVorticityHeatMultiplier
        nu.coeff (time.1 - earlier.1) wave •
      nativeTurbulenceCorrectionAt modes (receipt.wholePath earlier) wave
    ∂(commonTimeMeasure requestedTime)

private theorem resolvedWeightedIntegrand_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    Continuous fun earlier : Icc (0 : Real) requestedTime =>
      finiteStateVorticityHeatMultiplier
          nu.coeff (time.1 - earlier.1) wave •
        wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave := by
  have projectedContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        complexSharpSupportProjection modes (receipt.wholePath earlier) :=
    (complexSharpSupportProjection_continuous_native modes).comp
      receipt.wholePath.continuous
  have projectedTransverse :
      ∀ earlier : Icc (0 : Real) requestedTime,
        WholeStateTransverse
          (complexSharpSupportProjection modes (receipt.wholePath earlier)) := by
    intro earlier
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath earlier) (wholePath_transverse receipt earlier)
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun earlier =>
      ⟨complexSharpSupportProjection modes (receipt.wholePath earlier),
        projectedTransverse earlier⟩
  have projectedTransverseContinuous : Continuous projectedTransversePath :=
    projectedContinuous.subtype_mk projectedTransverse
  have nonlinearContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave := by
    have rowContinuous :
        Continuous fun earlier : Icc (0 : Real) requestedTime =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedTransversePath earlier).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        projectedTransverseContinuous
    simpa only [projectedTransversePath] using rowContinuous
  unfold finiteStateVorticityHeatMultiplier
  fun_prop

private theorem nativeWeightedIntegrand_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    Continuous fun earlier : Icc (0 : Real) requestedTime =>
      finiteStateVorticityHeatMultiplier
          nu.coeff (time.1 - earlier.1) wave •
        nativeTurbulenceCorrectionAt modes (receipt.wholePath earlier) wave := by
  have wholeNonlinearContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath earlier) wave := by
    let wholeTransversePath :
        Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
      fun earlier =>
        ⟨receipt.wholePath earlier, wholePath_transverse receipt earlier⟩
    have wholeTransverseContinuous : Continuous wholeTransversePath :=
      receipt.wholePath.continuous.subtype_mk (wholePath_transverse receipt)
    have rowContinuous :
        Continuous fun earlier : Icc (0 : Real) requestedTime =>
          wholeStateVorticityNonlinearCoefficientAt
            (wholeTransversePath earlier).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        wholeTransverseContinuous
    simpa only [wholeTransversePath] using rowContinuous
  have projectedContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        complexSharpSupportProjection modes (receipt.wholePath earlier) :=
    (complexSharpSupportProjection_continuous_native modes).comp
      receipt.wholePath.continuous
  have projectedTransverse :
      ∀ earlier : Icc (0 : Real) requestedTime,
        WholeStateTransverse
          (complexSharpSupportProjection modes (receipt.wholePath earlier)) := by
    intro earlier
    exact wholeStateTransverse_sharpSupportProjection
      modes (receipt.wholePath earlier) (wholePath_transverse receipt earlier)
  let projectedTransversePath :
      Icc (0 : Real) requestedTime → WholeTransverseVorticityState :=
    fun earlier =>
      ⟨complexSharpSupportProjection modes (receipt.wholePath earlier),
        projectedTransverse earlier⟩
  have projectedTransverseContinuous : Continuous projectedTransversePath :=
    projectedContinuous.subtype_mk projectedTransverse
  have resolvedNonlinearContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        wholeStateVorticityNonlinearCoefficientAt
          (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave := by
    have rowContinuous :
        Continuous fun earlier : Icc (0 : Real) requestedTime =>
          wholeStateVorticityNonlinearCoefficientAt
            (projectedTransversePath earlier).1 wave :=
      (wholeStateVorticityNonlinearCoefficientAt_continuous wave).comp
        projectedTransverseContinuous
    simpa only [projectedTransversePath] using rowContinuous
  have correctionContinuous :
      Continuous fun earlier : Icc (0 : Real) requestedTime =>
        nativeTurbulenceCorrectionAt modes (receipt.wholePath earlier) wave := by
    unfold nativeTurbulenceCorrectionAt projectedWholeNonlinearCoefficientAt
    by_cases waveMem : wave ∈ modes
    · simp only [if_pos waveMem]
      exact wholeNonlinearContinuous.sub resolvedNonlinearContinuous
    · simp only [if_neg waveMem]
      exact continuous_const.sub resolvedNonlinearContinuous
  unfold finiteStateVorticityHeatMultiplier
  fun_prop

private theorem resolvedWeightedIntegrand_integrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    Integrable
      (fun earlier : Icc (0 : Real) requestedTime =>
        finiteStateVorticityHeatMultiplier
            nu.coeff (time.1 - earlier.1) wave •
          wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave)
      ((commonTimeMeasure requestedTime).restrict (Iic time)) := by
  have wholeIntegrable :
      Integrable
        (fun earlier : Icc (0 : Real) requestedTime =>
          finiteStateVorticityHeatMultiplier
              nu.coeff (time.1 - earlier.1) wave •
            wholeStateVorticityNonlinearCoefficientAt
              (complexSharpSupportProjection modes (receipt.wholePath earlier)) wave)
        (commonTimeMeasure requestedTime) := by
    simpa using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (resolvedWeightedIntegrand_continuous
          receipt modes wave time).continuousOn)
  exact wholeIntegrable.integrableOn

private theorem nativeWeightedIntegrand_integrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    Integrable
      (fun earlier : Icc (0 : Real) requestedTime =>
        finiteStateVorticityHeatMultiplier
            nu.coeff (time.1 - earlier.1) wave •
          nativeTurbulenceCorrectionAt modes (receipt.wholePath earlier) wave)
      ((commonTimeMeasure requestedTime).restrict (Iic time)) := by
  have wholeIntegrable :
      Integrable
        (fun earlier : Icc (0 : Real) requestedTime =>
          finiteStateVorticityHeatMultiplier
              nu.coeff (time.1 - earlier.1) wave •
            nativeTurbulenceCorrectionAt modes (receipt.wholePath earlier) wave)
        (commonTimeMeasure requestedTime) := by
    simpa using
      (ContinuousOn.integrableOn_compact isCompact_univ
        (nativeWeightedIntegrand_continuous
          receipt modes wave time).continuousOn)
  exact wholeIntegrable.integrableOn

/-- The retained Duhamel row is exactly the sum of the classical resolved
convolution and the native correction convolution. -/
theorem projectedReceiptWeightedNonlinearDuhamelAt_eq_resolved_add_native
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime) :
    projectedReceiptWeightedNonlinearDuhamelAt receipt modes wave time =
      resolvedReceiptWeightedNonlinearDuhamelAt receipt modes wave time +
        nativeTurbulenceWeightedDuhamelAt receipt modes wave time := by
  unfold projectedReceiptWeightedNonlinearDuhamelAt
    resolvedReceiptWeightedNonlinearDuhamelAt
    nativeTurbulenceWeightedDuhamelAt
  rw [← MeasureTheory.integral_add
    (resolvedWeightedIntegrand_integrable receipt modes wave time)
    (nativeWeightedIntegrand_integrable receipt modes wave time)]
  apply integral_congr_ae
  filter_upwards [] with earlier
  rw [← smul_add]
  unfold nativeTurbulenceCorrectionAt
  abel

private theorem projectedReceiptWeightedNonlinearDuhamelAt_eq_actual
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) requestedTime) :
    projectedReceiptWeightedNonlinearDuhamelAt receipt modes wave time =
      if wave ∈ modes then
        receiptWeightedNonlinearDuhamelAt receipt wave waveNe time
      else 0 := by
  by_cases waveMem : wave ∈ modes
  · simp only [if_pos waveMem]
    rw [receiptWeightedNonlinearDuhamelAt_eq_actual_integral]
    unfold projectedReceiptWeightedNonlinearDuhamelAt
    apply integral_congr_ae
    filter_upwards [
      ae_mono Measure.restrict_le_self receipt.wholePath_eq_transverse_ae,
      ae_mono Measure.restrict_le_self
        (transverseSpaceTimeNonlinearRow_coeFn
          receipt.transverseLimit wave)] with earlier pathEq rowEq
    unfold projectedWholeNonlinearCoefficientAt
    rw [if_pos waveMem, pathEq]
    rw [show transverseSpaceTimeNonlinearRow receipt.transverseLimit wave earlier =
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.transverseLimit earlier).1 wave by
      simpa [transverseSpaceTimeNonlinearRowFunction] using rowEq]
  · simp only [if_neg waveMem]
    unfold projectedReceiptWeightedNonlinearDuhamelAt
      projectedWholeNonlinearCoefficientAt
    simp only [waveMem, if_false, smul_zero, integral_zero]

/-- The actual unforced receipt Duhamel write is the exact classical
resolved write plus the generated native turbulence write. -/
theorem receiptWeightedNonlinearDuhamelAt_projected_eq_resolved_add_native
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) requestedTime) :
    (if wave ∈ modes then
        receiptWeightedNonlinearDuhamelAt receipt wave waveNe time
      else 0) =
      resolvedReceiptWeightedNonlinearDuhamelAt receipt modes wave time +
        nativeTurbulenceWeightedDuhamelAt receipt modes wave time := by
  rw [← projectedReceiptWeightedNonlinearDuhamelAt_eq_actual
    receipt modes wave waveNe time]
  exact projectedReceiptWeightedNonlinearDuhamelAt_eq_resolved_add_native
    receipt modes wave time

/-- The terminal nonlinear regeneration on one native edge is exactly the
resolved Duhamel write plus the native correction write. -/
theorem wholeRestartNonlinearRegenerationState_projected_eq_resolved_add_native
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    let receipt := (run initial index).nextContact.prefixReceipt
    let terminal : Icc (0 : Real) (run initial index).nextContact.time.1 :=
      ⟨(run initial index).nextContact.time.1,
        ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩
    (if wave ∈ modes then
        wholeRestartNonlinearRegenerationState initial index wave
      else 0) =
      resolvedReceiptWeightedNonlinearDuhamelAt
          receipt modes wave terminal +
        nativeTurbulenceWeightedDuhamelAt receipt modes wave terminal := by
  dsimp only
  rw [wholeRestartNonlinearRegenerationState_apply_eq_actualDuhamel
    initial index wave waveNe]
  exact receiptWeightedNonlinearDuhamelAt_projected_eq_resolved_add_native
    (run initial index).nextContact.prefixReceipt modes wave waveNe
    ⟨(run initial index).nextContact.time.1,
      ⟨(run initial index).nextContact.time_pos.le, le_rfl⟩⟩

private theorem nativeTurbulenceWeightedDuhamelAt_eq_zero_of_oldRealizablePath
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (time : Icc (0 : Real) requestedTime)
    (stateSupported : ∀ earlier : Icc (0 : Real) requestedTime,
      complexSharpSupportProjection modes (receipt.wholePath earlier) =
        receipt.wholePath earlier)
    (nonlinearSupported : ∀ earlier : Icc (0 : Real) requestedTime,
      ∀ output : IntegerWavevector, output ∉ modes →
        wholeStateVorticityNonlinearCoefficientAt
          (receipt.wholePath earlier) output = 0) :
    nativeTurbulenceWeightedDuhamelAt receipt modes wave time = 0 := by
  unfold nativeTurbulenceWeightedDuhamelAt
  apply integral_eq_zero_of_ae
  filter_upwards [] with earlier
  rw [nativeTurbulenceCorrection_eq_zero_of_oldRealizable
    modes (receipt.wholePath earlier) (stateSupported earlier)
    (nonlinearSupported earlier) wave]
  simp

/-- Actual receipt row form of the corrected equation.  The derivative row,
whole state, and correction all come from the same receipt and time. -/
theorem receipt_projectedRowTangent_eq_classical_add_nativeTurbulence_ae
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt
      nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      (if wave ∈ modes then receipt.rowTangent wave waveNe time else 0) =
        wholeLatticeVorticityFourierTangentAt nu.coeff
            (complexSharpSupportProjection modes
              (receipt.wholePath time)) wave +
          nativeTurbulenceCorrectionAt modes
            (receipt.wholePath time) wave := by
  filter_upwards [receipt.rowTangent_eq_unforced_ae wave waveNe,
    receipt.wholePath_eq_transverse_ae] with time tangentEq pathEq
  have tangentEq' :
      receipt.rowTangent wave waveNe time =
        wholeLatticeVorticityFourierTangentAt nu.coeff
          (receipt.wholePath time) wave := by
    rw [tangentEq, ← pathEq,
      wholeStateVorticityBilinearCoefficientAt_self]
    rfl
  rw [tangentEq']
  exact projectedWholeTangent_eq_classical_add_nativeTurbulence
    modes nu.coeff (receipt.wholePath time) wave

/-- The exact cofinal blocks selected by the same failure which opened the
minimal coface. -/
structure SourceGeneratedNativeTurbulenceBlocksAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Type where
  private mk ::
  contactIndex : Nat → Nat
  contactIndex_zero : contactIndex 0 = 0
  contactIndex_strictMono : StrictMono contactIndex
  exactFlux :
    ∀ step : Nat,
      let radius := 2 * (contactIndex step + 1)
      let interval := Finset.Ico
        (contactIndex step) (contactIndex (step + 1))
      let trace :=
        ∑ index ∈ interval,
          receiptHighFrequencyProjectedParabolicTrace
            (run initial index).nextContact.prefixReceipt radius
      let pairWork :=
        ∑ index ∈ interval,
          actualWholeFinitePairOccurrenceWork
            (run initial index).nextContact.prefixReceipt
            (wholeRestartModes radius)
      let tangentViscousCross :=
        ∑ index ∈ interval,
          2 * RCLike.re (inner ℂ
            (puncturedEuclideanSpaceTimeState
              (run initial index).nextContact.prefixReceipt.wholeTangent)
            (puncturedEuclideanSpaceTimeState
              (receiptViscousNegativeOneState
                (run initial index).nextContact.prefixReceipt)))
      let viscousDebit :=
        ∑ index ∈ interval,
          actualWholeFiniteViscousPayment
            (run initial index).nextContact.prefixReceipt
            (wholeRestartModes radius)
      nu.coeff < trace ∧
        trace + nu.coeff * pairWork =
          tangentViscousCross + nu.coeff * viscousDebit ∧
        ∃ index ∈ interval,
          receiptHighFrequencyProjectedParabolicTrace
              (run initial index).nextContact.prefixReceipt radius ≠ 0 ∧
            ((∃ output ∈ wholeRestartModes radius,
                ∃ first : IntegerWavevector,
                  actualWholePairOccurrenceWork
                    (run initial index).nextContact.prefixReceipt
                    output first ≠ 0) ∨
              2 * RCLike.re (inner ℂ
                  (puncturedEuclideanSpaceTimeState
                    (run initial index).nextContact.prefixReceipt.wholeTangent)
                  (puncturedEuclideanSpaceTimeState
                    (receiptViscousNegativeOneState
                      (run initial index).nextContact.prefixReceipt))) ≠ 0 ∨
              actualWholeFiniteViscousPayment
                  (run initial index).nextContact.prefixReceipt
                  (wholeRestartModes radius) ≠ 0)

/-- The cofinal block selector is read internally from the exact source
failure.  It is not a radius, branch, or scheduler supplied by a caller. -/
noncomputable def sourceGeneratedNativeTurbulenceContactIndex
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) : Nat → Nat :=
  Classical.choose
    ((nativeTemporalCofinalStrongFaceFailure initial).wholePDEEffect
      elapsedBounded)

private theorem sourceGeneratedNativeTurbulenceContactIndex_spec
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let contactIndex :=
      sourceGeneratedNativeTurbulenceContactIndex initial elapsedBounded
    contactIndex 0 = 0 ∧
      StrictMono contactIndex ∧
        ∀ step : Nat,
          let radius := 2 * (contactIndex step + 1)
          let interval := Finset.Ico
            (contactIndex step) (contactIndex (step + 1))
          let trace :=
            ∑ index ∈ interval,
              receiptHighFrequencyProjectedParabolicTrace
                (run initial index).nextContact.prefixReceipt radius
          let pairWork :=
            ∑ index ∈ interval,
              actualWholeFinitePairOccurrenceWork
                (run initial index).nextContact.prefixReceipt
                (wholeRestartModes radius)
          let tangentViscousCross :=
            ∑ index ∈ interval,
              2 * RCLike.re (inner ℂ
                (puncturedEuclideanSpaceTimeState
                  (run initial index).nextContact.prefixReceipt.wholeTangent)
                (puncturedEuclideanSpaceTimeState
                  (receiptViscousNegativeOneState
                    (run initial index).nextContact.prefixReceipt)))
          let viscousDebit :=
            ∑ index ∈ interval,
              actualWholeFiniteViscousPayment
                (run initial index).nextContact.prefixReceipt
                (wholeRestartModes radius)
          nu.coeff < trace ∧
            trace + nu.coeff * pairWork =
              tangentViscousCross + nu.coeff * viscousDebit ∧
            ∃ index ∈ interval,
              receiptHighFrequencyProjectedParabolicTrace
                  (run initial index).nextContact.prefixReceipt radius ≠ 0 ∧
                ((∃ output ∈ wholeRestartModes radius,
                    ∃ first : IntegerWavevector,
                      actualWholePairOccurrenceWork
                        (run initial index).nextContact.prefixReceipt
                        output first ≠ 0) ∨
                  2 * RCLike.re (inner ℂ
                      (puncturedEuclideanSpaceTimeState
                        (run initial index).nextContact.prefixReceipt.wholeTangent)
                      (puncturedEuclideanSpaceTimeState
                        (receiptViscousNegativeOneState
                          (run initial index).nextContact.prefixReceipt))) ≠ 0 ∨
                  actualWholeFiniteViscousPayment
                      (run initial index).nextContact.prefixReceipt
                      (wholeRestartModes radius) ≠ 0) := by
  exact Classical.choose_spec
    ((nativeTemporalCofinalStrongFaceFailure initial).wholePDEEffect
      elapsedBounded)

private noncomputable def sourceGeneratedNativeTurbulenceBlocks
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    SourceGeneratedNativeTurbulenceBlocksAt initial elapsedBounded := by
  let contactIndex :=
    sourceGeneratedNativeTurbulenceContactIndex initial elapsedBounded
  have specifications :=
    sourceGeneratedNativeTurbulenceContactIndex_spec initial elapsedBounded
  exact
    { contactIndex := contactIndex
      contactIndex_zero := specifications.1
      contactIndex_strictMono := specifications.2.1
      exactFlux := specifications.2.2 }

/-- Zero-information seal for the native-turbulence readout generated by one
fixed revised inquiry occurrence.  The seal stores no equation, block choice,
continuation, or proof payload: every public field below is recomputed from the
dependent `initial`/`inquiry` indices. -/
structure SourceGeneratedNativeTurbulenceLawAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial) : Type 12 where
  private mk ::

namespace SourceGeneratedNativeTurbulenceLawAt

instance
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial} :
    Subsingleton (SourceGeneratedNativeTurbulenceLawAt initial inquiry) where
  allEq left right := by cases left; cases right; rfl

/-- A fixed revised inquiry has no second native-turbulence law payload.  Any
domain diversity must therefore occur in the root inquiry occurrence itself,
not in fields attached after that occurrence was generated. -/
theorem eq_of_same_inquiry
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (left right : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    left = right := by
  cases left
  cases right
  rfl

/-- The U8 payload is the one already carried by the fixed inquiry. -/
def u8
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (_law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    SourceGeneratedNativeAccumulationBoundaryU8At
      initial inquiry.elapsedBounded :=
  inquiry.u8

@[simp] theorem u8_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    law.u8 = inquiry.u8 :=
  rfl

/-- The cofinal failure is read from the same sealed inquiry occurrence. -/
theorem cofinalFailure_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    law.u8.exactExit.strongFaceFailure =
      nativeTemporalCofinalStrongFaceFailure initial :=
  law.u8.strongFaceFailure_eq

/-- The correction split is a theorem of the fixed coface coordinate, not a
field that can be submitted beside it. -/
theorem correctionDecomposition
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (_law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ (modes : Finset IntegerWavevector)
      (wholeState : ComplexVorticityHilbertState)
      (wave : IntegerWavevector),
      nativeTurbulenceCorrectionAt modes wholeState wave =
        oldCarrierOutputCorrectionAt modes
            (complexSharpSupportProjection modes wholeState) wave +
          cofaceInputCorrectionAt modes wholeState wave :=
  nativeTurbulenceCorrection_eq_old_add_coface

/-- Cofinal blocks are selected only from the exact failure retained by the
inquiry index. -/
noncomputable def blocks
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (_law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    SourceGeneratedNativeTurbulenceBlocksAt
      initial inquiry.elapsedBounded :=
  sourceGeneratedNativeTurbulenceBlocks initial inquiry.elapsedBounded

theorem fourierLaw
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ (step index : Nat),
      index ∈ Finset.Ico (law.blocks.contactIndex step)
          (law.blocks.contactIndex (step + 1)) →
      let radius := 2 * (law.blocks.contactIndex step + 1)
      let receipt := (run initial index).nextContact.prefixReceipt
      ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
        ∀ᵐ time ∂(commonTimeMeasure
          (run initial index).nextContact.time.1),
          (if wave ∈ wholeRestartModes radius then
              receipt.rowTangent wave waveNe time
            else 0) =
            wholeLatticeVorticityFourierTangentAt nu.coeff
                (complexSharpSupportProjection
                  (wholeRestartModes radius) (receipt.wholePath time)) wave +
              nativeTurbulenceCorrectionAt
                (wholeRestartModes radius) (receipt.wholePath time) wave := by
  intro step index _indexMem
  dsimp only
  intro wave waveNe
  exact receipt_projectedRowTangent_eq_classical_add_nativeTurbulence_ae
    (run initial index).nextContact.prefixReceipt
    (wholeRestartModes (2 * (law.blocks.contactIndex step + 1))) wave waveNe

theorem physicalLaw
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ (step index : Nat),
      index ∈ Finset.Ico (law.blocks.contactIndex step)
          (law.blocks.contactIndex (step + 1)) →
      let radius := 2 * (law.blocks.contactIndex step + 1)
      let receipt := (run initial index).nextContact.prefixReceipt
      ∀ time : Icc (0 : Real) (run initial index).nextContact.time.1,
        projectedWholePhysicalTangent
            (wholeRestartModes radius) nu.coeff (receipt.wholePath time) =
          resolvedClassicalPhysicalTangent
              (wholeRestartModes radius) nu.coeff (receipt.wholePath time) +
            nativeTurbulenceCorrectionField
              (wholeRestartModes radius) (receipt.wholePath time) := by
  intro step index _indexMem
  dsimp only
  intro time
  exact projectedWholePhysicalTangent_eq_classical_add_nativeTurbulence
    (wholeRestartModes (2 * (law.blocks.contactIndex step + 1))) nu.coeff
    ((run initial index).nextContact.prefixReceipt.wholePath time)

theorem enstrophyFluxLaw
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ (step index : Nat),
      index ∈ Finset.Ico (law.blocks.contactIndex step)
          (law.blocks.contactIndex (step + 1)) →
      let radius := 2 * (law.blocks.contactIndex step + 1)
      let receipt := (run initial index).nextContact.prefixReceipt
      ∀ time : Icc (0 : Real) (run initial index).nextContact.time.1,
        (∑ wave ∈ wholeRestartModes radius,
          complexCoordinateRealInner
            ((complexSharpSupportProjection
              (wholeRestartModes radius) (receipt.wholePath time)) wave)
            (wholeLatticeVorticityFourierTangentAt nu.coeff
              (receipt.wholePath time) wave)) =
          (∑ wave ∈ wholeRestartModes radius,
            complexCoordinateRealInner
              ((complexSharpSupportProjection
                (wholeRestartModes radius) (receipt.wholePath time)) wave)
              (finiteStateVorticityGenerator
                (wholeRestartModes radius) nu.coeff
                (complexSharpSupportProjection
                  (wholeRestartModes radius) (receipt.wholePath time)) wave)) +
            nativeTurbulenceEnstrophyFlux
              (wholeRestartModes radius) (receipt.wholePath time) := by
  intro step index _indexMem
  dsimp only
  intro time
  exact projectedWholeTangentWork_eq_resolvedGenerator_add_nativeFlux
    (wholeRestartModes (2 * (law.blocks.contactIndex step + 1))) nu.coeff
    ((run initial index).nextContact.prefixReceipt.wholePath time)

theorem conservativeOnOldCarrier
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (_law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ (modes : Finset IntegerWavevector)
      (wholeState : ComplexVorticityHilbertState),
      complexSharpSupportProjection modes wholeState = wholeState →
      (∀ wave : IntegerWavevector, wave ∉ modes →
        wholeStateVorticityNonlinearCoefficientAt wholeState wave = 0) →
      ∀ wave : IntegerWavevector,
        nativeTurbulenceCorrectionAt modes wholeState wave = 0 := by
  intro modes wholeState stateSupported nonlinearSupported wave
  exact nativeTurbulenceCorrection_eq_zero_of_oldRealizable
    modes wholeState stateSupported nonlinearSupported wave

theorem duhamelWrite
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (_law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    ∀ index : Nat,
      (run initial index).contact.physicalState =
        wholeRestartBlockTransportedInitialState initial 0 index +
          nativeAccumulationNonlinearDuhamelPrefix initial index := by
  intro index
  exact run_contact_eq_transportedInitial_add_nativeAccumulationNonlinearDuhamelPrefix
    initial index

/-- The recovery is the literal continuation generated from the inquiry's U8
payload. -/
noncomputable def recovery
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    NativeAccumulationBoundaryRecoveryNSContinuationAt initial law.u8 :=
  sourceGeneratedNativeAccumulationBoundaryRecoveryNSContinuation
    initial law.u8

@[simp] theorem recovery_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    law.recovery =
    sourceGeneratedNativeAccumulationBoundaryRecoveryNSContinuation
      initial law.u8 :=
  rfl

theorem recoveryPhysicalEvolution
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    let endpoint :=
      sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial
    let slice := sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
    0 < law.recovery.next.duration ∧
      law.recovery.next.receipt.wholePath
          ⟨0, ⟨le_rfl, law.recovery.next.receipt.requestedTimePos.le⟩⟩ =
        slice.vorticityState ∧
      ∀ wave : IntegerWavevector,
        biotSavartVelocityCoefficient wave
            (law.recovery.next.initialState wave) =
          endpoint.wholePath slice.time wave :=
  sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent_sameEvent initial

theorem recoveryNext_restricts
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    law.u8.recoveryNativeCurrent =
      (.galerkin 2 : NativeTemporalCurrent initial) :=
  rfl

theorem recoveryMacroWrite
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry) :
    generatedWholeRestartEndpointMacroRespond initial =
      some ⟨law.recovery.next, law.recovery.step⟩ :=
  sourceGeneratedNativeAccumulationBoundaryRecovery_macroRespond_exact
    initial law.u8

end SourceGeneratedNativeTurbulenceLawAt

/-- The original failure itself generates the coface correction law and its
recovery-next evolution. -/
private def sourceGeneratedNativeTurbulenceLaw
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial) :
    SourceGeneratedNativeTurbulenceLawAt initial inquiry :=
  .mk

/-- The recovery-next whole path is advanced by homogeneous heat, the
classical resolved Duhamel write, and the same native coface correction. -/
theorem SourceGeneratedNativeTurbulenceLawAt.recoveryNextDuhamelEvolution
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) law.recovery.next.duration) :
    (if wave ∈ modes then
        law.recovery.next.receipt.wholePath time wave -
          finiteStateVorticityHeatMultiplier
              nu.coeff time.1 wave • law.recovery.next.initialState wave
      else 0) =
      resolvedReceiptWeightedNonlinearDuhamelAt
          law.recovery.next.receipt modes wave time +
        nativeTurbulenceWeightedDuhamelAt
          law.recovery.next.receipt modes wave time := by
  rw [← receiptWeightedNonlinearDuhamelAt_projected_eq_resolved_add_native
    law.recovery.next.receipt modes wave waveNe time]
  by_cases waveMem : wave ∈ modes
  · simp only [if_pos waveMem]
    exact wholeContinuousMildSerrinReceipt_row_sub_heat_eq
      law.recovery.next.receipt wave waveNe time
  · simp only [if_neg waveMem]

/-- Evolution-level conservativity of the recovery write.  On a path
realized by the old carrier, the native Duhamel term vanishes and the same
recovery next is recognized by the original authoritative NS ledger. -/
theorem SourceGeneratedNativeTurbulenceLawAt.recoveryNext_classicalDuhamel_and_originalRootNext
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (modes : Finset IntegerWavevector)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (time : Icc (0 : Real) law.recovery.next.duration)
    (stateSupported : ∀ earlier : Icc (0 : Real) law.recovery.next.duration,
      complexSharpSupportProjection modes
          (law.recovery.next.receipt.wholePath earlier) =
        law.recovery.next.receipt.wholePath earlier)
    (nonlinearSupported :
      ∀ earlier : Icc (0 : Real) law.recovery.next.duration,
      ∀ output : IntegerWavevector, output ∉ modes →
        wholeStateVorticityNonlinearCoefficientAt
          (law.recovery.next.receipt.wholePath earlier) output = 0) :
    ((if wave ∈ modes then
          law.recovery.next.receipt.wholePath time wave -
            finiteStateVorticityHeatMultiplier
                nu.coeff time.1 wave • law.recovery.next.initialState wave
        else 0) =
        resolvedReceiptWeightedNonlinearDuhamelAt
          law.recovery.next.receipt modes wave time) ∧
      ((nativeTemporalRoot initial).toRoot.evolutionAt
          (.galerkin 1 : NativeTemporalCurrent initial)).nextCurrent? =
        some
          law.u8.recoveryNativeCurrent := by
  constructor
  · have evolution := law.recoveryNextDuhamelEvolution modes wave waveNe time
    rw [nativeTurbulenceWeightedDuhamelAt_eq_zero_of_oldRealizablePath
      law.recovery.next.receipt modes wave time stateSupported nonlinearSupported,
      add_zero] at evolution
    exact evolution
  · exact law.recovery.rootNext_generated

/-- The same failure block ledger, with its complete pair table decoded into
classical resolved transfer and the integrated native turbulence flux. -/
theorem SourceGeneratedNativeTurbulenceLawAt.cofinalBlockFlux_eq
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (step : Nat) :
    let radius := 2 * (law.blocks.contactIndex step + 1)
    let interval := Finset.Ico
      (law.blocks.contactIndex step) (law.blocks.contactIndex (step + 1))
    let trace :=
      ∑ index ∈ interval,
        receiptHighFrequencyProjectedParabolicTrace
          (run initial index).nextContact.prefixReceipt radius
    let resolvedWork :=
      ∑ index ∈ interval,
        actualResolvedEnstrophyWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    let nativeFluxWork :=
      ∑ index ∈ interval,
        actualNativeTurbulenceEnstrophyFluxWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    let tangentViscousCross :=
      ∑ index ∈ interval,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt)))
    let viscousDebit :=
      ∑ index ∈ interval,
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    nu.coeff < trace ∧
      trace + nu.coeff * (resolvedWork + nativeFluxWork) =
        tangentViscousCross + nu.coeff * viscousDebit := by
  dsimp only
  have ledger := law.blocks.exactFlux step
  dsimp only at ledger
  rcases ledger with ⟨tracePositive, balance, _nontrivial⟩
  refine ⟨tracePositive, ?_⟩
  have pairSplit :
      (∑ index ∈ Finset.Ico
          (law.blocks.contactIndex step)
          (law.blocks.contactIndex (step + 1)),
        actualWholeFinitePairOccurrenceWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes (2 * (law.blocks.contactIndex step + 1)))) =
        (∑ index ∈ Finset.Ico
            (law.blocks.contactIndex step)
            (law.blocks.contactIndex (step + 1)),
          actualResolvedEnstrophyWork
            (run initial index).nextContact.prefixReceipt
            (wholeRestartModes (2 * (law.blocks.contactIndex step + 1)))) +
          ∑ index ∈ Finset.Ico
            (law.blocks.contactIndex step)
            (law.blocks.contactIndex (step + 1)),
          actualNativeTurbulenceEnstrophyFluxWork
            (run initial index).nextContact.prefixReceipt
            (wholeRestartModes
              (2 * (law.blocks.contactIndex step + 1))) := by
    calc
      _ = ∑ index ∈ Finset.Ico
            (law.blocks.contactIndex step)
            (law.blocks.contactIndex (step + 1)),
          (actualResolvedEnstrophyWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes
                (2 * (law.blocks.contactIndex step + 1))) +
            actualNativeTurbulenceEnstrophyFluxWork
              (run initial index).nextContact.prefixReceipt
              (wholeRestartModes
                (2 * (law.blocks.contactIndex step + 1)))) := by
        apply Finset.sum_congr rfl
        intro index _indexMem
        exact
          actualWholeFinitePairOccurrenceWork_eq_resolved_add_nativeFluxWork
            (run initial index).nextContact.prefixReceipt
            (wholeRestartModes
              (2 * (law.blocks.contactIndex step + 1)))
            (zero_not_mem_wholeRestartModes
              (2 * (law.blocks.contactIndex step + 1)))
      _ = _ := Finset.sum_add_distrib
  rw [pairSplit] at balance
  exact balance

/-- Exact literal cross-pair settlement on one source-selected cofinal
block.  The native flux is the unique correction term in the same original
NS energy, tangent, viscous and pair ledger. -/
theorem SourceGeneratedNativeTurbulenceLawAt.cofinalBlockLiteralCross_eq_nativeFlux
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {inquiry : SourceGeneratedBoundaryRevisedInquiryAt initial}
    (law : SourceGeneratedNativeTurbulenceLawAt initial inquiry)
    (step : Nat) :
    let start := law.blocks.contactIndex step
    let finish := law.blocks.contactIndex (step + 1)
    let radius := 2 * (start + 1)
    let interval := Finset.Ico start finish
    let literalCross :=
      ∑ index ∈ interval,
        wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
          (run initial index)
    let diagonal :=
      ∑ index ∈ interval,
        wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
          (run initial index)
    let lowMassChange :=
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) (run initial finish).contact.physicalState -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) (run initial start).contact.physicalState
    let tangentPayment :=
      wholeRestartIcoTangentNegativeOneEuclideanPayment initial start finish
    let viscousPayment :=
      wholeRestartIcoViscousNegativeOneEuclideanPayment initial start finish
    let resolvedWork :=
      ∑ index ∈ interval,
        actualResolvedEnstrophyWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    let nativeFluxWork :=
      ∑ index ∈ interval,
        actualNativeTurbulenceEnstrophyFluxWork
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    let tangentViscousCross :=
      ∑ index ∈ interval,
        2 * RCLike.re (inner ℂ
          (puncturedEuclideanSpaceTimeState
            (run initial index).nextContact.prefixReceipt.wholeTangent)
          (puncturedEuclideanSpaceTimeState
            (receiptViscousNegativeOneState
              (run initial index).nextContact.prefixReceipt)))
    let finiteViscousDebit :=
      ∑ index ∈ interval,
        actualWholeFiniteViscousPayment
          (run initial index).nextContact.prefixReceipt
          (wholeRestartModes radius)
    literalCross =
      tangentViscousCross + nu.coeff * finiteViscousDebit -
        nu.coeff * (resolvedWork + nativeFluxWork) +
        nu.coeff * lowMassChange + tangentPayment + viscousPayment - diagonal := by
  dsimp only
  have blockFlux := law.cofinalBlockFlux_eq step
  dsimp only at blockFlux
  have startLeFinish :
      law.blocks.contactIndex step ≤
        law.blocks.contactIndex (step + 1) :=
    (law.blocks.contactIndex_strictMono (Nat.lt_succ_self step)).le
  have settlement :=
    wholeRestartIcoHighFrequencyProjectedParabolicTrace_exactSettlement
      initial (2 * (law.blocks.contactIndex step + 1))
      (law.blocks.contactIndex step) (law.blocks.contactIndex (step + 1))
      startLeFinish
  have polarization :
      wholeRestartIcoNonlinearNegativeOneEuclideanPayment initial
          (law.blocks.contactIndex step) (law.blocks.contactIndex (step + 1)) =
        (∑ index ∈ Finset.Ico
            (law.blocks.contactIndex step) (law.blocks.contactIndex (step + 1)),
          wholeRestartNextPrefixSymmetricVorticityPairDiagonalActionReal
            (run initial index)) +
          ∑ index ∈ Finset.Ico
            (law.blocks.contactIndex step) (law.blocks.contactIndex (step + 1)),
          wholeRestartNextPrefixSymmetricVorticityPairLiteralCrossAction
            (run initial index) := by
    unfold wholeRestartIcoNonlinearNegativeOneEuclideanPayment
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index _indexMem
    exact
      nextPrefix_receiptNonlinearNegativeOneEuclideanSquare_eq_diagonal_add_literalCross
        (run initial index)
  rcases blockFlux with ⟨_tracePositive, fluxEq⟩
  rw [polarization] at settlement
  linarith

/-! ## Source-owned boundary resolution -/

/-- Private old/new-language coordinate for one native source.  It stores only
the fixed inquiry branch.  The trajectory, predecessor occurrence and
native-turbulence readout are derived when the coordinate is consumed; they
cannot be installed as sibling fields. -/
private inductive NativeBoundaryReachabilityCoordinateAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13
  | oldAnswer
      (generated : SourceGeneratedBoundaryOldInquiryAt initial)
  | revisedAnswer
      (generated : SourceGeneratedBoundaryRevisedInquiryAt initial)

/-- Exhaustive source-generated answer.  Its branch coordinate is private;
callers can consume it but cannot repackage a sibling law as this result. -/
structure SourceGeneratedNativeBoundaryReachabilityAnswerAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) : Type 13 where
  private mk ::
  private coordinate : NativeBoundaryReachabilityCoordinateAt initial

namespace SourceGeneratedNativeBoundaryReachabilityAnswerAt

/-- Consume the answer without acquiring either branch constructor. -/
def fold
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial)
    {Result : Sort u}
    (oldAnswer : (generated : SourceGeneratedBoundaryOldInquiryAt initial) ->
      GeneratedWholeGlobalPhysicalTrajectory initial -> Result)
    (revisedAnswer : (generated : SourceGeneratedBoundaryRevisedInquiryAt initial) ->
      GeneratedNativeAccumulationConditionalOccurrenceAt initial ->
      SourceGeneratedNativeTurbulenceLawAt initial generated -> Result) : Result :=
  match answer.coordinate with
  | .oldAnswer generated =>
      oldAnswer generated
        (generatedWholeGlobalPhysicalTrajectory_of_unbounded
          initial generated.elapsedUnbounded)
  | .revisedAnswer generated =>
      revisedAnswer generated
        (generatedNativeAccumulationConditionalOccurrence initial
          generated.elapsedBounded)
        (sourceGeneratedNativeTurbulenceLaw initial generated)

/-- The public domain answer retains the exact occurrence emitted by the
fixed inquiry engine.  Old and revised semantics are restrictions of this
occurrence, not independently stored outcomes. -/
noncomputable def occurrence
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (answer : SourceGeneratedNativeBoundaryReachabilityAnswerAt initial) :=
  answer.fold
    (fun generated _trajectory => generated.occurrence)
    (fun generated _predecessor _law => generated.occurrence)

end SourceGeneratedNativeBoundaryReachabilityAnswerAt

/-- Run the fixed-root resolver and compile its dependent old or revised
answer.  No boundedness proof, face, branch, trajectory, revision candidate,
or answer is accepted from the caller. -/
noncomputable def sourceGeneratedNativeBoundaryReachabilityAnswer
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    SourceGeneratedNativeBoundaryReachabilityAnswerAt initial :=
  (sourceGeneratedBoundaryInquiryOutcome initial).fold
    (fun generated => ⟨.oldAnswer generated⟩)
    (fun generated => ⟨.revisedAnswer generated⟩)

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
end NavierStokes
end SaturationMonoid
