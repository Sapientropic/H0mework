import H0mework.Realization.Arithmetic.Incidence
import H0mework.NavierStokes.Accumulation.NativeTurbulenceLaw
import H0mework.NavierStokes.Accumulation.TemporalActionCoupling

/-!
# Exact temporal enstrophy ledger

The whole nonlinear pair-occurrence row and the physical viscous row are
integrated on the same actual receipt.  Their difference therefore folds
exactly to the finite projected coefficient-mass change.  No rate sign,
time bound, branch, endpoint state, or future recurrence is supplied by a
caller.
-/

set_option autoImplicit false

open scoped BigOperators Interval

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger

open MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.ArithmeticIncidence
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairOccurrenceWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeEnstrophyIdentity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart
open ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalActionCoupling
open ThreeDimensionalVorticityCoefficientSourceOwnedLocalKernelAbsorption

noncomputable section

/-- Viscous enstrophy power seen by the same finite projection as the whole
nonlinear power. -/
def actualProjectedWholeViscousEnstrophyPower
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
      ((nu.coeff * integerWaveViscousMultiplier wave) • state wave)

theorem actualProjectedWholeViscousEnstrophyPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous
      (actualProjectedWholeViscousEnstrophyPower receipt modes) := by
  have stateContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
    continuous_subtype_val.comp
      (actualWholeProjectedTransversePath_continuous receipt)
  unfold actualProjectedWholeViscousEnstrophyPower
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro wave waveMem
  have stateRowContinuous :
      Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 wave :=
    (lp.evalCLM Complex
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).continuous.comp stateContinuous
  have projectedRowContinuous :
      Continuous fun actual : Real =>
        (complexSharpSupportProjection modes
          (actualWholeProjectedTransversePath receipt actual).1) wave := by
    simpa only [complexSharpSupportProjection_apply,
      if_pos waveMem] using stateRowContinuous
  have viscousRowContinuous :
      Continuous fun actual : Real =>
        (nu.coeff * integerWaveViscousMultiplier wave) •
          (actualWholeProjectedTransversePath receipt actual).1 wave :=
    stateRowContinuous.const_smul
      (nu.coeff * integerWaveViscousMultiplier wave)
  exact complexCoordinateRealInner_prod_continuous.comp
    (projectedRowContinuous.prodMk viscousRowContinuous)

private def actualWholeRowViscousPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector)
    (actual : Real) : Real :=
  if waveZero : wave = 0 then
    0
  else
    2 * complexCoordinateRealInner
      (receipt.rowExtension wave waveZero actual)
      ((nu.coeff * integerWaveViscousMultiplier wave) •
        receipt.rowExtension wave waveZero actual)

private theorem actualWholeRowViscousPayment_eq_power_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowViscousPayment receipt wave =
      ∫ actual in (0 : Real)..requestedTime,
        actualWholeRowViscousPower receipt wave actual := by
  by_cases waveZero : wave = 0
  · simp [actualWholeRowViscousPayment,
      actualWholeRowViscousPower, waveZero]
  · simp [actualWholeRowViscousPayment,
      actualWholeRowViscousPower, waveZero]

private theorem actualWholeRowViscousPower_intervalIntegrable
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (wave : IntegerWavevector) :
    IntervalIntegrable
      (actualWholeRowViscousPower receipt wave)
      volume 0 requestedTime := by
  by_cases waveZero : wave = 0
  · have powerZero : actualWholeRowViscousPower receipt wave = 0 := by
      funext actual
      simp [actualWholeRowViscousPower, waveZero]
    rw [powerZero]
    exact intervalIntegrable_const
  · have pathContinuous :
        ContinuousOn
          (receipt.rowExtension wave waveZero)
          [[(0 : Real), requestedTime]] :=
      (receipt.rowExtension_absolutelyContinuous
        wave waveZero).continuousOn
    have pathContinuousIcc :
        ContinuousOn
          (receipt.rowExtension wave waveZero)
          (Set.Icc (0 : Real) requestedTime) := by
      simpa only [Set.uIcc_of_le receipt.requestedTimePos.le] using
        pathContinuous
    have viscousIntegrable :
        IntervalIntegrable
          (fun actual =>
            (nu.coeff * integerWaveViscousMultiplier wave) •
              receipt.rowExtension wave waveZero actual)
          volume 0 requestedTime :=
      (pathContinuousIcc.const_smul
        (nu.coeff * integerWaveViscousMultiplier wave))
          |>.intervalIntegrable_of_Icc receipt.requestedTimePos.le
    have innerIntegrable :=
      (complexCoordinateRealInner_intervalIntegrable
        pathContinuous viscousIntegrable).const_mul 2
    have powerEq :
        actualWholeRowViscousPower receipt wave =
          fun actual =>
            2 * complexCoordinateRealInner
              (receipt.rowExtension wave waveZero actual)
              ((nu.coeff * integerWaveViscousMultiplier wave) •
                receipt.rowExtension wave waveZero actual) := by
      funext actual
      simp [actualWholeRowViscousPower, waveZero]
    rw [powerEq]
    exact innerIntegrable

/-- The summed viscous payment is the integral of its same-occurrence
projected physical power. -/
theorem actualWholeFiniteViscousPayment_eq_projectedPower_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFiniteViscousPayment receipt modes =
      ∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeViscousEnstrophyPower
          receipt modes actual := by
  unfold actualWholeFiniteViscousPayment
  calc
    (∑ wave ∈ modes, actualWholeRowViscousPayment receipt wave) =
        ∑ wave ∈ modes,
          ∫ actual in (0 : Real)..requestedTime,
            actualWholeRowViscousPower receipt wave actual := by
      apply Finset.sum_congr rfl
      intro wave _waveMem
      exact actualWholeRowViscousPayment_eq_power_integral
        receipt wave
    _ = ∫ actual in (0 : Real)..requestedTime,
          ∑ wave ∈ modes,
            actualWholeRowViscousPower receipt wave actual := by
      rw [← intervalIntegral.integral_finsetSum]
      intro wave _waveMem
      exact actualWholeRowViscousPower_intervalIntegrable receipt wave
    _ = ∫ actual in (0 : Real)..requestedTime,
          actualProjectedWholeViscousEnstrophyPower
            receipt modes actual := by
      apply intervalIntegral.integral_congr
      intro actual actualMem
      have actualMem' : actual ∈ Set.Icc (0 : Real) requestedTime := by
        rw [Set.uIcc_of_le receipt.requestedTimePos.le] at actualMem
        exact actualMem
      unfold actualProjectedWholeViscousEnstrophyPower
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro wave waveMem
      let waveNonzero : wave ≠ 0 :=
        fun waveZero => zeroNotMem (by simpa [waveZero] using waveMem)
      rw [actualWholeRowViscousPower, dif_neg waveNonzero]
      rw [complexSharpSupportProjection_apply, if_pos waveMem]
      rw [receipt.rowExtension_on_interval wave waveNonzero
        ⟨actual, actualMem'⟩]
      simp only [actualWholeProjectedTransversePath,
        Set.projIcc_of_mem receipt.requestedTimePos.le actualMem']

/-- Net nonlinear-minus-viscous enstrophy power on one actual finite
projection. -/
def actualProjectedWholeNetEnstrophyPower
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) : Real :=
  actualProjectedWholeEnstrophyPower receipt modes actual -
    actualProjectedWholeViscousEnstrophyPower receipt modes actual

theorem actualProjectedWholeNetEnstrophyPower_continuous
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    Continuous (actualProjectedWholeNetEnstrophyPower receipt modes) := by
  exact
    (actualProjectedWholeEnstrophyPower_continuous receipt modes).sub
      (actualProjectedWholeViscousEnstrophyPower_continuous receipt modes)

/-- The current selected endpoint power is the time-zero power instruction
read by its exact generated next receipt. -/
theorem nextReceipt_netPower_zero_eq_contact_selectedEndpoint
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    actualProjectedWholeNetEnstrophyPower
        current.nextReceipt modes 0 =
      actualProjectedWholeNetEnstrophyPower
        current.contact.prefixReceipt modes
        current.contact.time.1 := by
  have nextZero :
      (actualWholeProjectedTransversePath
        current.nextReceipt 0).1 =
        current.contact.physicalState := by
    change current.nextReceipt.wholePath
        (Set.projIcc (0 : Real)
          (wholeRestartDuration current.contact)
          current.nextReceipt.requestedTimePos.le 0) =
      current.contact.physicalState
    rw [Set.projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨le_rfl, current.nextReceipt.requestedTimePos.le⟩]
    exact current.nextReceipt.wholePath_initial
  have selectedTerminal :
      (actualWholeProjectedTransversePath
        current.contact.prefixReceipt
        current.contact.time.1).1 =
        current.contact.physicalState := by
    change current.contact.prefixReceipt.wholePath
        (Set.projIcc (0 : Real) current.contact.time.1
          current.contact.time_pos.le
          current.contact.time.1) =
      current.contact.physicalState
    rw [Set.projIcc_of_mem current.contact.time_pos.le
      ⟨current.contact.time_pos.le, le_rfl⟩]
    exact current.contact.prefixReceipt_terminal
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [nextZero, selectedTerminal]

/-- The selected endpoint power of one exact emitter edge is the time-zero
power instruction read by its generated physical successor.  This is the
local commuting seam used by source-generated recurrence laws: no stage
table, replacement receipt, or second scheduler is introduced. -/
theorem next_netPower_zero_eq_current_selectedEndpoint
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    actualProjectedWholeNetEnstrophyPower
        current.next.nextReceipt modes 0 =
      actualProjectedWholeNetEnstrophyPower
        current.nextContact.prefixReceipt modes
        current.nextContact.time.1 := by
  convert
    nextReceipt_netPower_zero_eq_contact_selectedEndpoint current.next modes
      using 1
  · rw [next_contact]
    rfl

/-- Exact arbitrary-state source split.  The actual projected net-power row
is the resolved finite generator pairing plus the native coface flux; no tail
term is discarded after the first source occurrence. -/
theorem actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (actual : Real) :
    let state := (actualWholeProjectedTransversePath receipt actual).1
    let projected := complexSharpSupportProjection modes state
    actualProjectedWholeNetEnstrophyPower receipt modes actual =
      2 * ((∑ wave ∈ modes,
          complexCoordinateRealInner (projected wave)
            (finiteStateVorticityGenerator
              modes nu.coeff projected wave)) +
        nativeTurbulenceEnstrophyFlux modes state) := by
  dsimp only
  let state := (actualWholeProjectedTransversePath receipt actual).1
  let projected := complexSharpSupportProjection modes state
  have nonlinearSplit :=
    projectedWholeNonlinearWork_eq_resolved_add_nativeTurbulenceFlux
      modes state
  have viscousEq :
      (∑ wave ∈ modes,
        complexCoordinateRealInner (projected wave)
          ((nu.coeff * integerWaveViscousMultiplier wave) • state wave)) =
        ∑ wave ∈ modes,
          complexCoordinateRealInner (projected wave)
            ((nu.coeff * integerWaveViscousMultiplier wave) •
              projected wave) := by
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  have generatorSplit := finiteStateVorticityGenerator_realWork
    modes nu.coeff projected
  rw [← finiteStateVorticityViscousWork_eq] at generatorSplit
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  dsimp only [state, projected]
  rw [viscousEq]
  linarith

/-- At the source endpoint `t = 0`, the actual projected whole net-power row
is exactly twice the finite generator pairing whenever the source state is
supported on that same inventory. -/
theorem actualProjectedWholeNetEnstrophyPower_zero_eq_generatorRealWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → initialState wave = 0) :
    actualProjectedWholeNetEnstrophyPower receipt modes 0 =
      2 * ∑ wave ∈ modes,
        complexCoordinateRealInner (initialState wave)
          (finiteStateVorticityGenerator
            modes nu.coeff initialState wave) := by
  have stateAtZero :
      (actualWholeProjectedTransversePath receipt 0).1 = initialState := by
    change receipt.wholePath
        (Set.projIcc (0 : Real) requestedTime
          receipt.requestedTimePos.le 0) = initialState
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact receipt.wholePath_initial
  unfold actualProjectedWholeNetEnstrophyPower
    actualProjectedWholeEnstrophyPower
    actualProjectedWholeViscousEnstrophyPower
  rw [stateAtZero]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [complexSharpSupportProjection_apply, if_pos waveMem]
  rw [wholeStateVorticityNonlinearCoefficientAt_eq_finite_of_supported
    modes initialState supported wave]
  rw [finiteStateVorticityGenerator_apply, if_pos waveMem]
  rw [_root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger.complexCoordinateRealInner_sub_right]
  ring

/-- Exact whole-ledger fold: projected nonlinear power minus the identical
projected viscous payment is precisely the finite endpoint mass change. -/
theorem actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeNetEnstrophyPower receipt modes actual) =
      finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy modes initialState := by
  have pairIntegral :=
    actualWholeFinitePairOccurrenceWork_eq_projectedPower_integral
      receipt modes zeroNotMem
  have viscousIntegral :=
    actualWholeFiniteViscousPayment_eq_projectedPower_integral
      receipt modes zeroNotMem
  have endpointLedger :=
    actualWholeFinitePairOccurrenceWork_eq_terminal_sub_initial_add_viscousPayment
      receipt modes zeroNotMem
  rw [pairIntegral, viscousIntegral] at endpointLedger
  unfold actualProjectedWholeNetEnstrophyPower
  rw [intervalIntegral.integral_sub
    ((actualProjectedWholeEnstrophyPower_continuous receipt modes
      ).intervalIntegrable 0 requestedTime)
    ((actualProjectedWholeViscousEnstrophyPower_continuous receipt modes)
      |>.intervalIntegrable 0 requestedTime)]
  linarith

/-- A finite projected debit on the complete fixed replay, stopped at its
source-generated terminal time, forces the contact compiler's own crossing
branch.  The theorem never mentions the internally selected contact time. -/
theorem nextCellEffect_oneCell_of_fullReceipt_projectedNetDebit
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (finiteDebit :
      (wholeRestartCoefficientLevel current.contact : Real) - 1 -
          finiteStateVorticityCoefficientEnstrophy modes
            current.contact.physicalState <
        ∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          actualProjectedWholeNetEnstrophyPower
            current.nextReceipt modes actual) :
    ∃ (debit : GeneratedWholeRestartCellDebitAt
          (generatedWholeRestartCanonicalReplay current.contact)
          current.nextContact)
        (exact : debit.ExactValuedOneCellAt),
      current.nextCellEffect = .oneCell debit exact := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      current.nextReceipt modes zeroNotMem
  have finiteTerminalCrossing :
      (wholeRestartCoefficientLevel current.contact : Real) - 1 <
        finiteStateVorticityCoefficientEnstrophy modes
          (current.nextReceipt.wholePath
            ⟨wholeRestartDuration current.contact,
              ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩) := by
    linarith
  have terminalCrossing :
      (wholeRestartCoefficientLevel current.contact : Real) - 1 <
        wholeVorticityEuclideanMass
          (current.nextReceipt.wholePath
            ⟨wholeRestartDuration current.contact,
              ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩) :=
    finiteTerminalCrossing.trans_le
      (finiteStateVorticityCoefficientEnstrophy_le_wholeMass modes _)
  exact
    current.nextKineticContact.cellEffect_oneCell_of_terminal_mass_crosses
      terminalCrossing

/-- The finite action row is exactly the integral of its source-generated
net-power projection on the same receipt. -/
theorem actualWholeFiniteNetWork_eq_netPower_integral
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    actualWholeFiniteNetWork receipt modes =
      ∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeNetEnstrophyPower receipt modes actual := by
  rw [actualWholeFiniteNetWork_eq_terminal_sub_initial]
  exact
    (actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      receipt modes zeroNotMem).symm

/-! ## Whole-row action readback for the emitter debit -/

/-- The exact row net works of one actual receipt form a summable whole
action row. -/
theorem summable_actualWholeRowNetWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    Summable fun wave : IntegerWavevector =>
      actualWholeRowNetWork receipt wave := by
  let terminalState := receipt.wholePath
    ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  have terminalSummable : Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq (terminalState wave) := by
    exact (summable_vorticityRowAmplitude_sq terminalState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have initialSummable : Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq (initialState wave) := by
    exact (summable_vorticityRowAmplitude_sq initialState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  exact (terminalSummable.sub initialSummable).congr fun wave =>
    (actualWholeRowNetWork_eq_terminal_sub_initial receipt wave).symm

/-- The complete action outside one finite inventory.  The complement is
typed into the row, so it cannot be silently discarded by a finite
projection. -/
def actualWholeTailNetWork
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) : Real :=
  ∑' wave : {wave : IntegerWavevector // wave ∉ modes},
    actualWholeRowNetWork receipt wave.1

/-- Complete coefficient mass outside one fixed finite inventory. -/
def wholeTailVorticityMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  ∑' wave : {wave : IntegerWavevector // wave ∉ modes},
    complexCoordinateAmplitudeSq (state wave.1)

theorem wholeTailVorticityMass_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ wholeTailVorticityMass modes state := by
  unfold wholeTailVorticityMass
  exact tsum_nonneg fun wave =>
    complexCoordinateAmplitudeSq_nonneg (state wave.1)

/-- Exact partition of whole coefficient mass into one finite inventory and
its typed complement. -/
theorem wholeVorticityEuclideanMass_eq_finite_add_tail
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass state =
      finiteStateVorticityCoefficientEnstrophy modes state +
        wholeTailVorticityMass modes state := by
  have amplitudeSummable : Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq (state wave) := by
    exact (summable_vorticityRowAmplitude_sq state).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have split := amplitudeSummable.sum_add_tsum_subtype_compl modes
  unfold wholeVorticityEuclideanMass
    finiteStateVorticityCoefficientEnstrophy wholeTailVorticityMass
  have wholeEq :
      (∑' wave : IntegerWavevector,
          vorticityRowAmplitude state wave ^ 2) =
        ∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (state wave) := by
    apply tsum_congr
    intro wave
    rw [vorticityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  rw [wholeEq]
  exact split.symm

theorem wholeTailVorticityMass_eq_whole_sub_finite
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    wholeTailVorticityMass modes state =
      wholeVorticityEuclideanMass state -
        finiteStateVorticityCoefficientEnstrophy modes state := by
  linarith [wholeVorticityEuclideanMass_eq_finite_add_tail modes state]

/-- Mass exposed when an actual finite inventory grows. -/
def wholeInventoryCaptureMass
    (sourceModes targetModes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  wholeTailVorticityMass sourceModes state -
    wholeTailVorticityMass targetModes state

theorem wholeInventoryCaptureMass_nonneg_of_subset
    {sourceModes targetModes : Finset IntegerWavevector}
    (subset : sourceModes ⊆ targetModes)
    (state : ComplexVorticityHilbertState) :
    0 ≤ wholeInventoryCaptureMass sourceModes targetModes state := by
  have finiteLe :
      finiteStateVorticityCoefficientEnstrophy sourceModes state ≤
        finiteStateVorticityCoefficientEnstrophy targetModes state := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_le_sum_of_subset_of_nonneg subset
      (fun wave _targetMem _sourceNotMem =>
        complexCoordinateAmplitudeSq_nonneg (state wave))
  unfold wholeInventoryCaptureMass
  rw [wholeTailVorticityMass_eq_whole_sub_finite,
    wholeTailVorticityMass_eq_whole_sub_finite]
  linarith

/-- The complement action is itself an exact endpoint ledger. -/
theorem actualWholeTailNetWork_eq_terminal_sub_initial
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeTailNetWork receipt modes =
      wholeTailVorticityMass modes
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        wholeTailVorticityMass modes initialState := by
  let terminalState := receipt.wholePath
    ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  have terminalWholeSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (terminalState wave) := by
    exact (summable_vorticityRowAmplitude_sq terminalState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have terminalSummable :
      Summable fun wave : {wave : IntegerWavevector // wave ∉ modes} =>
        complexCoordinateAmplitudeSq (terminalState wave.1) := by
    exact (terminalWholeSummable.comp_injective Subtype.val_injective).congr
      fun wave => rfl
  have initialWholeSummable :
      Summable fun wave : IntegerWavevector =>
        complexCoordinateAmplitudeSq (initialState wave) := by
    exact (summable_vorticityRowAmplitude_sq initialState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have initialSummable :
      Summable fun wave : {wave : IntegerWavevector // wave ∉ modes} =>
        complexCoordinateAmplitudeSq (initialState wave.1) := by
    exact (initialWholeSummable.comp_injective Subtype.val_injective).congr
      fun wave => rfl
  unfold actualWholeTailNetWork wholeTailVorticityMass
  simp_rw [actualWholeRowNetWork_eq_terminal_sub_initial]
  exact terminalSummable.tsum_sub initialSummable

/-- A genuinely finite-support source cannot hide a negative initial tail:
every complement row starts at zero, so its complete endpoint action is
nonnegative.  This property is intentionally source-local; after an actual
write-back the newly generated tail must itself be transported. -/
theorem actualWholeTailNetWork_nonneg_of_initial_supported
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → initialState wave = 0) :
    0 ≤ actualWholeTailNetWork receipt modes := by
  unfold actualWholeTailNetWork
  apply tsum_nonneg
  intro wave
  rw [actualWholeRowNetWork_eq_terminal_sub_initial,
    supported wave.1 wave.2]
  simpa [complexCoordinateAmplitudeSq] using
    complexCoordinateAmplitudeSq_nonneg
      (receipt.wholePath
        ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ wave.1)

/-- Exact core/tail partition of the complete whole action.  This is a
partition of the same actual receipt, not a limiting or projection
estimate. -/
theorem tsum_actualWholeRowNetWork_eq_finite_add_tail
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    (∑' wave : IntegerWavevector, actualWholeRowNetWork receipt wave) =
      actualWholeFiniteNetWork receipt modes +
        actualWholeTailNetWork receipt modes := by
  exact
    ((summable_actualWholeRowNetWork receipt
      ).sum_add_tsum_subtype_compl modes).symm

/-- Complete same-occurrence action factorization: the source-generated
finite physical power plus the explicitly retained complement is exactly
the whole endpoint action. -/
theorem tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (∑' wave : IntegerWavevector, actualWholeRowNetWork receipt wave) =
      (∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeNetEnstrophyPower receipt modes actual) +
          actualWholeTailNetWork receipt modes := by
  rw [tsum_actualWholeRowNetWork_eq_finite_add_tail,
    actualWholeFiniteNetWork_eq_netPower_integral receipt modes zeroNotMem]

/-- For a finite-support source occurrence, the finite physical net-power
integral is a certified lower projection of the complete whole action. -/
theorem netPowerIntegral_le_tsum_actualWholeRowNetWork_of_initial_supported
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (supported : ∀ wave : IntegerWavevector,
      wave ∉ modes → initialState wave = 0) :
    (∫ actual in (0 : Real)..requestedTime,
        actualProjectedWholeNetEnstrophyPower receipt modes actual) ≤
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork receipt wave := by
  rw [tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
    receipt modes zeroNotMem]
  exact le_add_of_nonneg_right
    (actualWholeTailNetWork_nonneg_of_initial_supported
      receipt modes supported)

/-- On the authoritative restart run, a fixed complement row is transported
without refill: all of its actual edge actions telescope to one terminal
balance. -/
theorem run_actualWholeTailNetWork_prefix_telescope
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
        actualWholeTailNetWork
          (run initial stage).contact.prefixReceipt modes) =
        wholeTailVorticityMass modes (run initial length).initialState -
          wholeTailVorticityMass modes initial.initialState := by
  intro length
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        actualWholeTailNetWork_eq_terminal_sub_initial,
        (run initial length).contact.prefixReceipt_terminal,
        run_succ_initialState]
      ring

/-- Whole-history commuting square for one fixed physical inventory: every
complete edge action is the finite net-power integral on that edge, while
the complement contributes only its exact terminal-minus-initial balance. -/
theorem run_tsum_actualWholeRowNetWork_prefix_factorization
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork
          (run initial stage).contact.prefixReceipt wave) =
      (∑ stage ∈ Finset.range length,
        ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial stage).contact.prefixReceipt modes actual) +
        wholeTailVorticityMass modes (run initial length).initialState -
          wholeTailVorticityMass modes initial.initialState := by
  calc
    (∑ stage ∈ Finset.range length,
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (run initial stage).contact.prefixReceipt wave) =
        (∑ stage ∈ Finset.range length,
          ((∫ actual in (0 : Real)..(run initial stage).contact.time.1,
              actualProjectedWholeNetEnstrophyPower
                (run initial stage).contact.prefixReceipt modes actual) +
            actualWholeTailNetWork
              (run initial stage).contact.prefixReceipt modes)) := by
      apply Finset.sum_congr rfl
      intro stage _stageMem
      exact tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
        (run initial stage).contact.prefixReceipt modes zeroNotMem
    _ =
        (∑ stage ∈ Finset.range length,
          ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
            actualProjectedWholeNetEnstrophyPower
              (run initial stage).contact.prefixReceipt modes actual) +
          (∑ stage ∈ Finset.range length,
            actualWholeTailNetWork
              (run initial stage).contact.prefixReceipt modes) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [run_actualWholeTailNetWork_prefix_telescope]
      ring

/-- The transported complement can tax the fixed finite action only once,
by its actual initial balance; it cannot create a fresh negative tail debt at
every restart. -/
theorem run_netPowerIntegral_prefix_sub_initialTail_le_tsum_action
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
        ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial stage).contact.prefixReceipt modes actual) -
        wholeTailVorticityMass modes initial.initialState ≤
      ∑ stage ∈ Finset.range length,
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (run initial stage).contact.prefixReceipt wave := by
  rw [run_tsum_actualWholeRowNetWork_prefix_factorization
    initial modes zeroNotMem length]
  linarith [wholeTailVorticityMass_nonneg
    modes (run initial length).initialState]

/-- Summing the complete actual row action gives exactly the whole endpoint
enstrophy change; no finite inventory or limiting certificate is supplied. -/
theorem tsum_actualWholeRowNetWork_eq_terminal_sub_initial
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    (∑' wave : IntegerWavevector, actualWholeRowNetWork receipt wave) =
      wholeVorticityEuclideanMass
          (receipt.wholePath
            ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        wholeVorticityEuclideanMass initialState := by
  let terminalState := receipt.wholePath
    ⟨requestedTime, ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
  have terminalSummable : Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq (terminalState wave) := by
    exact (summable_vorticityRowAmplitude_sq terminalState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have initialSummable : Summable fun wave : IntegerWavevector =>
      complexCoordinateAmplitudeSq (initialState wave) := by
    exact (summable_vorticityRowAmplitude_sq initialState).congr fun wave => by
      rw [vorticityRowAmplitude_sq,
        complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have terminalTsum :
      (∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (terminalState wave)) =
        wholeVorticityEuclideanMass terminalState := by
    unfold wholeVorticityEuclideanMass
    apply tsum_congr
    intro wave
    rw [vorticityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  have initialTsum :
      (∑' wave : IntegerWavevector,
          complexCoordinateAmplitudeSq (initialState wave)) =
        wholeVorticityEuclideanMass initialState := by
    unfold wholeVorticityEuclideanMass
    apply tsum_congr
    intro wave
    rw [vorticityRowAmplitude_sq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  calc
    (∑' wave : IntegerWavevector, actualWholeRowNetWork receipt wave) =
        ∑' wave : IntegerWavevector,
          (complexCoordinateAmplitudeSq (terminalState wave) -
            complexCoordinateAmplitudeSq (initialState wave)) := by
      apply tsum_congr
      intro wave
      exact actualWholeRowNetWork_eq_terminal_sub_initial receipt wave
    _ =
        (∑' wave : IntegerWavevector,
            complexCoordinateAmplitudeSq (terminalState wave)) -
          ∑' wave : IntegerWavevector,
            complexCoordinateAmplitudeSq (initialState wave) :=
      terminalSummable.tsum_sub initialSummable
    _ = _ := by
      rw [terminalTsum, initialTsum]

/-- The complete whole action along a finite native prefix is exactly the
whole coefficient-mass change between its physical endpoints. -/
theorem run_tsum_actualWholeRowNetWork_prefix_telescope
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (run initial stage).contact.prefixReceipt wave) =
        wholeVorticityEuclideanMass (run initial length).initialState -
          wholeVorticityEuclideanMass initial.initialState := by
  intro length
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        tsum_actualWholeRowNetWork_eq_terminal_sub_initial,
        (run initial length).contact.prefixReceipt_terminal,
        run_succ_initialState]
      ring

/-- Exact complement telescope for a recursively growing finite inventory.
Inventory enlargement exposes an explicit nonnegative capture row instead
of silently changing the meaning of `tail`. -/
theorem run_actualWholeMovingTailNetWork_prefix_telescope
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector) :
    ∀ length : Nat,
      (∑ stage ∈ Finset.range length,
        actualWholeTailNetWork
          (run initial stage).contact.prefixReceipt (modes stage)) =
        wholeTailVorticityMass (modes length)
            (run initial length).initialState -
          wholeTailVorticityMass (modes 0) initial.initialState +
          ∑ stage ∈ Finset.range length,
            wholeInventoryCaptureMass (modes stage) (modes (stage + 1))
              (run initial (stage + 1)).initialState := by
  intro length
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        actualWholeTailNetWork_eq_terminal_sub_initial,
        (run initial length).contact.prefixReceipt_terminal,
        run_succ_initialState, Finset.sum_range_succ]
      unfold wholeInventoryCaptureMass
      have nextInitialEq :
          (run initial (length + 1)).initialState =
            (run initial length).contact.physicalState :=
        run_succ_initialState initial length
      rw [nextInitialEq]
      ring

/-- Complete same-run action factorization for a moving finite inventory.
Every inventory change is retained as an exact capture at the common
successor boundary. -/
theorem run_tsum_actualWholeRowNetWork_prefix_movingFactorization
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (length : Nat) :
    (∑ stage ∈ Finset.range length,
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork
          (run initial stage).contact.prefixReceipt wave) =
      (∑ stage ∈ Finset.range length,
        ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial stage).contact.prefixReceipt
            (modes stage) actual) +
        wholeTailVorticityMass (modes length)
            (run initial length).initialState -
          wholeTailVorticityMass (modes 0) initial.initialState +
          ∑ stage ∈ Finset.range length,
            wholeInventoryCaptureMass (modes stage) (modes (stage + 1))
              (run initial (stage + 1)).initialState := by
  calc
    (∑ stage ∈ Finset.range length,
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (run initial stage).contact.prefixReceipt wave) =
        ∑ stage ∈ Finset.range length,
          ((∫ actual in (0 : Real)..(run initial stage).contact.time.1,
              actualProjectedWholeNetEnstrophyPower
                (run initial stage).contact.prefixReceipt
                (modes stage) actual) +
            actualWholeTailNetWork
              (run initial stage).contact.prefixReceipt
              (modes stage)) := by
      apply Finset.sum_congr rfl
      intro stage _stageMem
      exact tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
        (run initial stage).contact.prefixReceipt
        (modes stage) (zeroNotMem stage)
    _ =
        (∑ stage ∈ Finset.range length,
          ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
            actualProjectedWholeNetEnstrophyPower
              (run initial stage).contact.prefixReceipt
              (modes stage) actual) +
          (∑ stage ∈ Finset.range length,
            actualWholeTailNetWork
              (run initial stage).contact.prefixReceipt
              (modes stage)) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [run_actualWholeMovingTailNetWork_prefix_telescope]
      ring

/-- Paid action exposed by a moving finite inventory: the physical net-power
integrals on the inventory present at each edge plus the exact mass exposed
when the next source-generated inventory grows. -/
def runMovingInventoryPaidActionPrefix
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (length : Nat) : Real :=
  (∑ stage ∈ Finset.range length,
    ∫ actual in (0 : Real)..(run initial stage).contact.time.1,
      actualProjectedWholeNetEnstrophyPower
        (run initial stage).contact.prefixReceipt (modes stage) actual) +
    ∑ stage ∈ Finset.range length,
      wholeInventoryCaptureMass (modes stage) (modes (stage + 1))
        (run initial (stage + 1)).initialState

/-- Local payment generated by one actual run edge and one recursively
transported inventory update. -/
def runMovingInventoryEdgePayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (stage : Nat) : Real :=
  (∫ actual in (0 : Real)..(run initial stage).contact.time.1,
      actualProjectedWholeNetEnstrophyPower
        (run initial stage).contact.prefixReceipt (modes stage) actual) +
    wholeInventoryCaptureMass (modes stage) (modes (stage + 1))
      (run initial (stage + 1)).initialState

/-- Exact local commuting square: physical action on the current inventory
plus newly exposed material is the finite-mass change across that same
actual successor boundary. -/
theorem runMovingInventoryEdgePayment_eq_nextFiniteMass_sub_current
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (stage : Nat) :
    runMovingInventoryEdgePayment initial modes stage =
      finiteStateVorticityCoefficientEnstrophy (modes (stage + 1))
          (run initial (stage + 1)).initialState -
        finiteStateVorticityCoefficientEnstrophy (modes stage)
          (run initial stage).initialState := by
  have action := actualWholeFiniteNetWork_eq_netPower_integral
    (run initial stage).contact.prefixReceipt
    (modes stage) (zeroNotMem stage)
  rw [actualWholeFiniteNetWork_eq_terminal_sub_initial,
    (run initial stage).contact.prefixReceipt_terminal,
    ← run_succ_initialState initial stage] at action
  have sourceSplit := wholeVorticityEuclideanMass_eq_finite_add_tail
    (modes stage) (run initial (stage + 1)).initialState
  have targetSplit := wholeVorticityEuclideanMass_eq_finite_add_tail
    (modes (stage + 1)) (run initial (stage + 1)).initialState
  unfold runMovingInventoryEdgePayment wholeInventoryCaptureMass
  linarith

/-- The prefix paid ledger is the ordinary finite fold of its actual local
edge payments. -/
theorem runMovingInventoryPaidActionPrefix_eq_sum_edgePayment
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (length : Nat) :
    runMovingInventoryPaidActionPrefix initial modes length =
      ∑ stage ∈ Finset.range length,
        runMovingInventoryEdgePayment initial modes stage := by
  unfold runMovingInventoryPaidActionPrefix
    runMovingInventoryEdgePayment
  rw [Finset.sum_add_distrib]

/-- Canonical finite inventory generated recursively from the actual local
kernel core at every run occurrence.  The union retains all prior material;
there is no completed future table and no caller-selected cutoff. -/
noncomputable def sourceGeneratedRunKernelInventory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    Nat → Finset IntegerWavevector
  | 0 =>
      (sourceOwnedLocalKernelCore nu
        (restartCoefficientCeiling initial 0)).erase 0
  | stage + 1 =>
      sourceGeneratedRunKernelInventory initial stage ∪
        (sourceOwnedLocalKernelCore nu
          (restartCoefficientCeiling initial (stage + 1))).erase 0

theorem sourceGeneratedRunKernelInventory_zeroNotMem
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ stage,
      (0 : IntegerWavevector) ∉
        sourceGeneratedRunKernelInventory initial stage := by
  intro stage
  induction stage with
  | zero => simp [sourceGeneratedRunKernelInventory]
  | succ stage inductionHypothesis =>
      simp [sourceGeneratedRunKernelInventory, inductionHypothesis]

theorem sourceGeneratedRunKernelInventory_nested
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (stage : Nat) :
    sourceGeneratedRunKernelInventory initial stage ⊆
      sourceGeneratedRunKernelInventory initial (stage + 1) := by
  rw [sourceGeneratedRunKernelInventory]
  exact Finset.subset_union_left

theorem sourceGeneratedRunKernelCore_subset_inventory
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    ∀ stage : Nat,
      (sourceOwnedLocalKernelCore nu
          (restartCoefficientCeiling initial stage)).erase 0 ⊆
        sourceGeneratedRunKernelInventory initial stage := by
  intro stage
  cases stage with
  | zero => exact Finset.Subset.rfl
  | succ stage =>
      rw [sourceGeneratedRunKernelInventory]
      exact Finset.subset_union_right

/-- The moving paid-action ledger is not an extra budget: after exact tail
transport and inventory capture it is definitionally the finite mass gained
by the current generated inventory between the two prefix boundaries. -/
theorem runMovingInventoryPaidActionPrefix_eq_terminalFiniteMass_sub_initial
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (length : Nat) :
    runMovingInventoryPaidActionPrefix initial modes length =
      finiteStateVorticityCoefficientEnstrophy (modes length)
          (run initial length).initialState -
        finiteStateVorticityCoefficientEnstrophy (modes 0)
          initial.initialState := by
  have factorization :=
    run_tsum_actualWholeRowNetWork_prefix_movingFactorization
      initial modes zeroNotMem length
  have wholeTelescope :=
    run_tsum_actualWholeRowNetWork_prefix_telescope initial length
  have initialSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail
      (modes 0) initial.initialState
  have terminalSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail
      (modes length) (run initial length).initialState
  unfold runMovingInventoryPaidActionPrefix
  linarith

/-- A nested source-generated moving inventory can tax its accumulated paid
action only by the actual initial complement balance.  Capture mass is
retained in the payment rather than discarded as a representation change. -/
theorem run_movingPaidActionPrefix_sub_initialTail_le_tsum_action
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (nested : ∀ stage, modes stage ⊆ modes (stage + 1))
    (length : Nat) :
    runMovingInventoryPaidActionPrefix initial modes length -
        wholeTailVorticityMass (modes 0) initial.initialState ≤
      ∑ stage ∈ Finset.range length,
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            (run initial stage).contact.prefixReceipt wave := by
  rw [run_tsum_actualWholeRowNetWork_prefix_movingFactorization
    initial modes zeroNotMem length]
  have _captureNonneg : 0 ≤
      ∑ stage ∈ Finset.range length,
        wholeInventoryCaptureMass (modes stage) (modes (stage + 1))
          (run initial (stage + 1)).initialState := by
    exact Finset.sum_nonneg fun stage _stageMem =>
      wholeInventoryCaptureMass_nonneg_of_subset
        (nested stage) (run initial (stage + 1)).initialState
  unfold runMovingInventoryPaidActionPrefix
  linarith [wholeTailVorticityMass_nonneg
    (modes length) (run initial length).initialState]

/-- Linear whole-history action growth on a nested source inventory forces
the actual quantized restart level to grow at least once every two stages. -/
theorem index_div_two_le_restartCoefficientLevelNat_of_movingActionPrefixGrowth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (nested : ∀ stage, modes stage ⊆ modes (stage + 1))
    (growth : ∀ length : Nat,
      ((length / 2 : Nat) : Real) +
          wholeTailVorticityMass (modes 0) initial.initialState -
          wholeVorticityEuclideanMass initial.initialState ≤
        runMovingInventoryPaidActionPrefix initial modes length) :
    ∀ index : Nat,
      index / 2 ≤ restartCoefficientLevelNat initial index := by
  intro index
  have actionLower :=
    run_movingPaidActionPrefix_sub_initialTail_le_tsum_action
      initial modes zeroNotMem nested (index + 1)
  have wholeTelescope :=
    run_tsum_actualWholeRowNetWork_prefix_telescope initial (index + 1)
  have prefixGrowth := growth (index + 1)
  have terminalMassLower :
      (((index + 1) / 2 : Nat) : Real) ≤
        wholeVorticityEuclideanMass (run initial (index + 1)).initialState := by
    linarith
  have halfLe : index / 2 ≤ (index + 1) / 2 := by omega
  have halfLeReal : ((index / 2 : Nat) : Real) ≤
      (((index + 1) / 2 : Nat) : Real) := by
    exact_mod_cast halfLe
  have contactMassLower :
      ((index / 2 : Nat) : Real) ≤
        wholeVorticityEuclideanMass
          (run initial index).contact.physicalState := by
    rw [run_succ_initialState] at terminalMassLower
    exact halfLeReal.trans terminalMassLower
  unfold restartCoefficientLevelNat
  have belowRaw :
      ((index / 2 : Nat) : Real) <
        wholeRestartRawCoefficientCeiling (run initial index).contact := by
    rw [wholeRestartRawCoefficientCeiling_eq]
    simp only [wholeRestartPhysicalState_generatedPositiveWholeRestartContact]
    linarith
  exact Nat.le_of_lt ((Nat.lt_ceil).2 belowRaw)

/-- Direct clock consumer for a source-generated moving-inventory invariant.
No branch, incidence, target level or summability witness is accepted. -/
theorem contactTime_summable_of_movingActionPrefixGrowth
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Nat → Finset IntegerWavevector)
    (zeroNotMem : ∀ stage, (0 : IntegerWavevector) ∉ modes stage)
    (nested : ∀ stage, modes stage ⊆ modes (stage + 1))
    (growth : ∀ length : Nat,
      ((length / 2 : Nat) : Real) +
          wholeTailVorticityMass (modes 0) initial.initialState -
          wholeVorticityEuclideanMass initial.initialState ≤
        runMovingInventoryPaidActionPrefix initial modes length) :
    Summable fun stage => (run initial stage).contact.time.1 := by
  exact (summable_contactTime_iff_reciprocalBarrier initial).2
    (summable_reciprocalBarrier_of_halfIndex_level_growth initial
      (index_div_two_le_restartCoefficientLevelNat_of_movingActionPrefixGrowth
        initial modes zeroNotMem nested growth))

/-- The emitter's endpoint debit is the exact complete action-row fold on
the same selected contact prefix. -/
theorem GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    debit.netEnstrophyDebit =
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork nextContact.prefixReceipt wave := by
  have ledger :=
    tsum_actualWholeRowNetWork_eq_terminal_sub_initial
      nextContact.prefixReceipt
  rw [nextContact.prefixReceipt_terminal] at ledger
  rw [debit.netEnstrophyDebit_eq, debit.sourcePhysicalState_eq,
    debit.targetPhysicalState_eq]
  exact ledger.symm

/-- Time, endpoint valuation and whole action are three projections of the
same valued arithmetic material. -/
theorem GeneratedWholeRestartCellDebitAt.physicalValuation_commutes
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    {replay : GeneratedWholeRestartCanonicalReplay contact}
    {nextContact : GeneratedPositiveWholeRestartContact
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)}
    (debit : GeneratedWholeRestartCellDebitAt replay nextContact) :
    debit.contactTime = nextContact.time.1 ∧
      debit.netEnstrophyDebit =
        (∑' wave : IntegerWavevector,
          actualWholeRowNetWork nextContact.prefixReceipt wave) ∧
      nextContact.prefixReceipt.wholePath
          ⟨debit.contactTime, ⟨debit.contactTime_pos.le, le_rfl⟩⟩ =
        debit.targetPhysicalState := by
  refine ⟨rfl, netEnstrophyDebit_eq_tsum_action debit, ?_⟩
  exact debit.target_eq_receipt_terminal

/-- The fixed full-replay terminal debit is exactly the complete whole-row
action of that receipt.  This identity is upstream of the good-time selector
and contains no finite projection or tail remainder. -/
theorem generatedWholeRestartTerminalNetEnstrophyDebit_eq_tsum_action
    {nu : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : Real}
    {receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime}
    {contact : GeneratedPositiveWholeRestartContact receipt}
    (replay : GeneratedWholeRestartCanonicalReplay contact) :
    generatedWholeRestartTerminalNetEnstrophyDebit replay =
      ∑' wave : IntegerWavevector,
        actualWholeRowNetWork
          (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)
          wave := by
  have ledger :=
    tsum_actualWholeRowNetWork_eq_terminal_sub_initial
      (generatedWholeRestartWholeContinuousMildSerrinReceipt replay)
  unfold generatedWholeRestartTerminalNetEnstrophyDebit
  exact ledger.symm

/-- Same-run readout of the emitter debit.  Both effect branches carry this
identical physical mass difference; residual is therefore a retained
settlement state, not a second kind of numerical payment. -/
theorem runCellEffect_debit_eq_physicalMassChange
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) :
    (runCellEffect initial index).debit.netEnstrophyDebit =
      restartPhysicalVorticityMass initial (index + 1) -
        restartPhysicalVorticityMass initial index := by
  rw [(runCellEffect initial index).debit.netEnstrophyDebit_eq,
    (runCellEffect initial index).debit.sourcePhysicalState_eq,
    (runCellEffect initial index).debit.targetPhysicalState_eq]
  unfold restartPhysicalVorticityMass
  rw [run_succ]
  rfl

/-- Nonnegative valuation on every exact emitted material makes the physical
endpoint mass monotone.  This is weaker than unit-cell recurrence: residual
payments may be arbitrarily small and need never cross a wall. -/
theorem restartPhysicalVorticityMass_monotone_of_cellEffectDebit_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (debitNonneg : ∀ index : Nat,
      0 ≤ (runCellEffect initial index).debit.netEnstrophyDebit) :
    Monotone (restartPhysicalVorticityMass initial) := by
  apply monotone_nat_of_le_succ
  intro index
  have debitEq := runCellEffect_debit_eq_physicalMassChange initial index
  have nonnegative := debitNonneg index
  rw [debitEq] at nonnegative
  linarith

/-- The kinetic clock only needs a source-generated positive lower floor for
the target whole-vorticity mass.  Individual valued debits may have either
sign: every successor contact is paid by the same fixed mass factor and the
summable kinetic defect. -/
theorem contactTime_summable_of_targetMass_floor
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (massFloor : Real)
    (massFloorPos : 0 < massFloor)
    (targetMassFloor : ∀ index : Nat,
      1 + massFloor ≤
        wholeVorticityEuclideanMass
          (run initial index).nextContact.physicalState) :
    Summable fun index ↦ (run initial index).contact.time.1 := by
  let coefficient : Real := 2 * nu.coeff * massFloor
  have coefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    exact mul_pos (mul_pos (by norm_num) nu.coeff_pos) massFloorPos
  have paymentDominates : ∀ index : Nat,
      coefficient * (run initial index).nextContact.time.1 ≤
        wholeRestartNextKineticDissipationPayment initial index := by
    intro index
    have floorLeTarget :
        massFloor ≤
          wholeVorticityEuclideanMass
              (run initial index).nextContact.physicalState - 1 := by
      linarith [targetMassFloor index]
    have rectangle :=
      (run initial index
        ).nextContact_terminalMass_sub_one_mul_time_le_prefix
    have clockFloorLePrefix :
        (run initial index).nextContact.time.1 * massFloor ≤
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit := by
      calc
        (run initial index).nextContact.time.1 * massFloor ≤
            (run initial index).nextContact.time.1 *
              (wholeVorticityEuclideanMass
                  (run initial index).nextContact.physicalState - 1) :=
          mul_le_mul_of_nonneg_left floorLeTarget
            (run initial index).nextContact.time_pos.le
        _ ≤ wholePrefixVorticityMass
              (run initial index).nextContact.time
              (run initial index).nextReceipt.stateLimit := rectangle
    unfold wholeRestartNextKineticDissipationPayment
    change
      (2 * nu.coeff * massFloor) *
          (run initial index).nextContact.time.1 ≤
        2 * nu.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit
    calc
      (2 * nu.coeff * massFloor) *
            (run initial index).nextContact.time.1 =
          (2 * nu.coeff) *
            ((run initial index).nextContact.time.1 * massFloor) := by ring
      _ ≤ (2 * nu.coeff) *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit :=
        mul_le_mul_of_nonneg_left clockFloorLePrefix
          (mul_nonneg (by norm_num) nu.coeff_pos.le)
  have scaledSummable :
      Summable fun index ↦
        coefficient * (run initial index).nextContact.time.1 :=
    (summable_wholeRestartNextKineticDissipationPayment initial
      ).of_nonneg_of_le
        (fun index ↦ mul_nonneg coefficientPos.le
          (run initial index).nextContact.time_pos.le)
        paymentDominates
  have successorSummable :
      Summable fun index ↦ (run initial index).nextContact.time.1 := by
    have unscaled := scaledSummable.mul_left coefficient⁻¹
    exact unscaled.congr fun index ↦ by
      change coefficient⁻¹ *
          (coefficient * (run initial index).nextContact.time.1) =
        (run initial index).nextContact.time.1
      rw [← mul_assoc, inv_mul_cancel₀ coefficientPos.ne', one_mul]
  have tailSummable :
      Summable fun index ↦ (run initial (index + 1)).contact.time.1 := by
    simpa only [run_succ, next_contact] using successorSummable
  exact (summable_nat_add_iff
    (f := fun index ↦ (run initial index).contact.time.1) 1).mp
      tailSummable

/-- Quantitative kinetic settlement of the complete clock.  If the same
valued material never emits a negative physical debit and the source mass
starts above the barrier's additive unit, the exact kinetic defect pays a
fixed positive multiple of every successor contact time.  No cell crossing,
bounded delay, scale recurrence or summability certificate is required. -/
theorem contactTime_summable_of_cellEffectDebit_nonneg
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (initialMass_gt_one :
      1 < wholeVorticityEuclideanMass initial.contact.physicalState)
    (debitNonneg : ∀ index : Nat,
      0 ≤ (runCellEffect initial index).debit.netEnstrophyDebit) :
    Summable fun index ↦ (run initial index).contact.time.1 := by
  let massFloor : Real :=
    wholeVorticityEuclideanMass initial.contact.physicalState - 1
  have massFloorPos : 0 < massFloor := by
    dsimp only [massFloor]
    linarith
  have massMonotone :=
    restartPhysicalVorticityMass_monotone_of_cellEffectDebit_nonneg
      initial debitNonneg
  apply contactTime_summable_of_targetMass_floor
    initial massFloor massFloorPos
  intro index
  have targetMassLower :
      wholeVorticityEuclideanMass initial.contact.physicalState ≤
        wholeVorticityEuclideanMass
          (run initial index).nextContact.physicalState := by
    have generated := massMonotone (Nat.zero_le (index + 1))
    unfold restartPhysicalVorticityMass at generated
    rw [run_zero, run_succ] at generated
    exact generated
  dsimp only [massFloor]
  linarith

/-- Run-indexed hybrid progress generated by one positive fixed-terminal
debit.  No branch or selected contact time appears in the theorem mouth. -/
theorem run_levelAdvance_or_retainedPayment_of_terminalDebit_pos
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (terminalPositive :
      0 < generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay
          (run initial index).contact)) :
    restartCoefficientLevelNat initial (index + 1) =
        restartCoefficientLevelNat initial index + 1 ∨
      (restartCoefficientLevelNat initial (index + 1) =
          restartCoefficientLevelNat initial index ∧
        generatedWholeRestartTerminalNetEnstrophyDebit
              (generatedWholeRestartCanonicalReplay
                (run initial index).contact) / 2 <
          (runCellEffect initial index).debit.netEnstrophyDebit) := by
  unfold restartCoefficientLevelNat
  rw [run_succ, next_contact]
  change
    wholeRestartCoefficientLevel
          (run initial index).nextKineticContact.nextContact =
        wholeRestartCoefficientLevel (run initial index).contact + 1 ∨
      (wholeRestartCoefficientLevel
            (run initial index).nextKineticContact.nextContact =
          wholeRestartCoefficientLevel (run initial index).contact ∧
        generatedWholeRestartTerminalNetEnstrophyDebit
              (generatedWholeRestartCanonicalReplay
                (run initial index).contact) / 2 <
          (run initial index).nextKineticContact.cellEffect.debit.netEnstrophyDebit)
  exact
    (run initial index).nextKineticContact
      |>.levelAdvance_or_retainedPayment_of_terminalDebit_pos
        terminalPositive

/-- The residual-aware runtime's settlement decision is the projection of
the same complete physical action row.  Thus a second edge cannot submit a
new residual or a caller-selected payment: it can only make this exact
same-debt action fold cross the retained deficit. -/
theorem generatedPendingCellDisposition_isSettled_iff_tsum_action
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    (generatedWholeRestartPendingCellDisposition pending).IsSettled ↔
      pending.cellDeficit <
        ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            current.nextContact.prefixReceipt wave := by
  rw [generatedPendingCellDisposition_isSettled_iff_paid,
    _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
      current.nextCellEffect.debit]
  rfl

/-- The pending decision after choosing any source-generated finite inventory
is exactly the finite physical net-power integral plus the explicitly
retained complement action.  This exposes the full recursive obligation:
neither the native flux nor the tail can be erased by a projected proof. -/
theorem generatedPendingCellDisposition_isSettled_iff_netPower_add_tail
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes) :
    (generatedWholeRestartPendingCellDisposition pending).IsSettled ↔
      pending.cellDeficit <
        (∫ actual in (0 : Real)..current.nextContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            current.nextContact.prefixReceipt modes actual) +
          actualWholeTailNetWork
            current.nextContact.prefixReceipt modes := by
  rw [generatedPendingCellDisposition_isSettled_iff_tsum_action,
    tsum_actualWholeRowNetWork_eq_netPowerIntegral_add_tail
      current.nextContact.prefixReceipt modes zeroNotMem]

/-- Complete action readout of residual residence.  A live residual either
settles, is transported with a strictly positive complete action and smaller
deficit, or emits a nonpositive obstruction while the exact row remains live
for the next actual action. -/
theorem pendingStanding_next_clear_or_paidSameDebt_or_nonpositiveObstruction_action
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    (pending : GeneratedWholeRestartPendingCellAt current) :
    (GeneratedWholeRestartCellStandingAt.pending pending).next = .clear ∨
      (∃ nextPending : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending pending).next =
            .pending nextPending ∧
          nextPending.origin = pending.origin ∧
          HEq nextPending.residual pending.residual ∧
          0 < (∑' wave : IntegerWavevector,
            actualWholeRowNetWork
              current.nextContact.prefixReceipt wave) ∧
          nextPending.cellDeficit = pending.cellDeficit -
            ∑' wave : IntegerWavevector,
              actualWholeRowNetWork
                current.nextContact.prefixReceipt wave) ∨
      ∃ nextPending : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending pending).next =
            .pending nextPending ∧
          nextPending.origin = pending.origin ∧
          HEq nextPending.residual pending.residual ∧
          ¬ 0 < current.nextCellEffect.debit.netEnstrophyDebit ∧
          nextPending.cellDeficit = pending.cellDeficit -
            current.nextCellEffect.debit.netEnstrophyDebit ∧
          (∑' wave : IntegerWavevector,
            actualWholeRowNetWork
              current.nextContact.prefixReceipt wave) ≤ 0 := by
  rcases pendingStanding_next_clear_or_paidSameDebt_or_nonpositiveObstruction
      pending with
    settled | paid | failed
  · exact Or.inl settled
  · rcases paid with
      ⟨nextPending, nextEq, originEq, residualEq, debitPos, deficitEq⟩
    right
    left
    refine ⟨nextPending, nextEq, originEq, residualEq, ?_, ?_⟩
    · calc
        0 < current.nextCellEffect.debit.netEnstrophyDebit := debitPos
        _ = ∑' wave : IntegerWavevector,
            actualWholeRowNetWork
              current.nextContact.prefixReceipt wave :=
          _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
            current.nextCellEffect.debit
    · rw [deficitEq,
        _root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
          current.nextCellEffect.debit]
      rfl
  · rcases failed with
      ⟨nextPending, nextEq, originEq, residualEq, notPositive, deficitEq⟩
    right
    right
    refine ⟨nextPending, nextEq, originEq, residualEq, notPositive,
      deficitEq, ?_⟩
    have nonpositive := le_of_not_gt notPositive
    calc
      (∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            current.nextContact.prefixReceipt wave) =
          current.nextCellEffect.debit.netEnstrophyDebit :=
        (_root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
          current.nextCellEffect.debit).symm
      _ ≤ 0 := nonpositive

/-- Positive complete Fourier action is exactly the no-free continuation
ticket for a retained cell debt. -/
theorem pendingStanding_next_clear_or_paidSameDebt_of_tsum_action_pos
    {nu : Viscosity}
    {current : GeneratedWholeRestartCurrent nu}
    (pending : GeneratedWholeRestartPendingCellAt current)
    (actionPos : 0 < ∑' wave : IntegerWavevector,
      actualWholeRowNetWork current.nextContact.prefixReceipt wave) :
    (GeneratedWholeRestartCellStandingAt.pending pending).next = .clear ∨
      ∃ nextPending : GeneratedWholeRestartPendingCellAt current.next,
        (GeneratedWholeRestartCellStandingAt.pending pending).next =
            .pending nextPending ∧
          nextPending.origin = pending.origin ∧
          HEq nextPending.residual pending.residual ∧
          nextPending.cellDeficit < pending.cellDeficit := by
  have debitPos : 0 <
      current.nextCellEffect.debit.netEnstrophyDebit := by
    calc
      0 < ∑' wave : IntegerWavevector,
          actualWholeRowNetWork
            current.nextContact.prefixReceipt wave := actionPos
      _ = current.nextCellEffect.debit.netEnstrophyDebit :=
        (_root_.SaturationMonoid.NavierStokes.ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger.GeneratedWholeRestartCellDebitAt.netEnstrophyDebit_eq_tsum_action
          current.nextCellEffect.debit).symm
  exact pendingStanding_next_clear_or_paidSameDebt_of_debit_pos
    pending debitPos

/-- The finite cell carrier generated by the quantized restart compiler at
one exact causal depth. -/
abbrev RestartCoefficientCellCarrierAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Type :=
  Fin (restartCoefficientLevelNat initial index)

abbrev RestartCoefficientOnePaidCell := Fin 1

/-- One exact paid-cell incidence between the actual current and successor
compiler carriers. -/
def RestartCoefficientCellIncidenceAt
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat) : Prop :=
  ParallelIncidenceAt
    (RestartCoefficientCellCarrierAt initial (index + 1))
    (RestartCoefficientCellCarrierAt initial index)
    RestartCoefficientOnePaidCell

/-- A same-successor finite net debit that clears the current quantized wall
generates the actual one-paid-cell incidence.  The endpoint carrier is
generated by the receipt ledger and is not accepted from the caller. -/
theorem restartCoefficientCellIncidenceAt_of_projectedNetDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (finiteDebit :
      (restartCoefficientLevelNat initial index : Real) - 1 -
          finiteStateVorticityCoefficientEnstrophy modes
            (run initial index).contact.physicalState <
        ∫ actual in (0 : Real)..
            (run initial index).nextContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial index).nextContact.prefixReceipt modes actual) :
    RestartCoefficientCellIncidenceAt initial index := by
  have ledger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      (run initial index).nextContact.prefixReceipt modes zeroNotMem
  rw [(run initial index).nextContact.prefixReceipt_terminal] at ledger
  have finiteEndpointGt :
      (restartCoefficientLevelNat initial index : Real) - 1 <
        finiteStateVorticityCoefficientEnstrophy modes
          (run initial index).nextContact.physicalState := by
    linarith
  have levelEq :
      restartCoefficientLevelNat initial (index + 1) =
        restartCoefficientLevelNat initial index + 1 := by
    rw [restartCoefficientLevelNat_succ_eq_add_one_iff_mass_crosses_cell]
    rw [restartPhysicalVorticityMass, run_succ]
    exact finiteEndpointGt.trans_le
      (finiteStateVorticityCoefficientEnstrophy_le_wholeMass
        modes (run initial index).nextContact.physicalState)
  exact ⟨(finCongr levelEq).trans finSumFinEquiv.symm⟩

/-- The exact `+1` equation is the cardinal readout of the source-generated
one-cell incidence, never the authority used to define that incidence. -/
theorem restartCoefficientLevelNat_succ_eq_add_one_of_projectedNetDebit
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : Nat)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (finiteDebit :
      (restartCoefficientLevelNat initial index : Real) - 1 -
          finiteStateVorticityCoefficientEnstrophy modes
            (run initial index).contact.physicalState <
        ∫ actual in (0 : Real)..
            (run initial index).nextContact.time.1,
          actualProjectedWholeNetEnstrophyPower
            (run initial index).nextContact.prefixReceipt modes actual) :
    restartCoefficientLevelNat initial (index + 1) =
      restartCoefficientLevelNat initial index + 1 := by
  have incidence := restartCoefficientCellIncidenceAt_of_projectedNetDebit
    initial index modes zeroNotMem finiteDebit
  have cardReadout := card_eq_add_of_parallel _ _ _ incidence
  simpa [RestartCoefficientCellCarrierAt,
    RestartCoefficientOnePaidCell] using cardReadout

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
end NavierStokes
end SaturationMonoid
