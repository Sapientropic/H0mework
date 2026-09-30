import H0mework.NavierStokes.Restart.HighFrequencyEscape

/-!
# Exact enstrophy-work transport on the native whole restart chain

Every row of an actual `WholeContinuousMildSerrinReceipt` already carries an
absolutely continuous real-line extension and its unforced tangent.  This
module first turns that same event into an exact endpoint energy identity,
then sums only over a finite canonical inventory and telescopes the result
along the actual restart endpoints.

Consequently finite accumulated physical time forces unbounded cumulative
nonlinear-minus-viscous work on source-generated finite inventories.  The
inventory and crossing occurrence are conclusion data: no cutoff, tail
witness, work bound, endpoint, path, or continuation certificate is accepted
from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork

open scoped BigOperators Interval Topology

open Set Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteTimeObstruction
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHighFrequencyEscape
open
  ThreeDimensionalVorticityCoefficientGeneratedShellGluingResidualNativeMacroWholeUnforcedPositiveTimeRestart.GeneratedPositiveWholeRestartContact

noncomputable section

/-! ## Same-receipt row and finite-inventory transport -/

/-- The complete receipt tangent has no zero Fourier row. -/
theorem receiptWholeTangent_zero_row_ae
    {nu : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt nu initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      receipt.wholeTangent time 0 = 0 := by
  filter_upwards [receipt.wholeTangent_eq_unforced_ae] with time tangentEq
  rw [tangentEq]
  classical
  unfold wholeSpaceTimeNonlinearNegativeOneFunction
    wholeSpaceTimeViscousNegativeOneFunction
  split <;> split <;>
    simp [wholeStateVorticityNonlinearNegativeOneState_apply,
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityViscousNegativeOneState_apply,
      wholeStateVorticityViscousNegativeOneWeightedCoefficient,
      integerWaveViscousMultiplier, integerWaveNormSq]
  all_goals
    change
      wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
        (receipt.transverseLimit time).1 0 = 0
    simp [wholeStateVorticityNonlinearNegativeOneWeightedCoefficient]

/-- Net nonlinear-minus-viscous work of one actual receipt row.  The zero
row is defined as zero; every nonzero row uses the receipt's own extension
and tangent on its own physical interval. -/
def actualWholeRowNetWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  if waveZero : wave = 0 then
    0
  else
    ∫ actual in (0 : ℝ)..requestedTime,
      2 * complexCoordinateRealInner
        (receipt.rowExtension wave waveZero actual)
        (commonTimeZeroExtension requestedTime
          (receipt.rowTangent wave waveZero) actual)

/-- One actual row pays exactly its endpoint coefficient-energy change.
Both sides belong to the same unforced receipt event. -/
theorem actualWholeRowNetWork_eq_terminal_sub_initial
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowNetWork receipt wave =
      complexCoordinateAmplitudeSq
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩ wave) -
        complexCoordinateAmplitudeSq (initialState wave) := by
  by_cases waveZero : wave = 0
  · subst wave
    have initialZero : initialState 0 = 0 := by
      rw [← receipt.wholePath_initial]
      exact receipt.wholePath_zero_row
        ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩
    simp [actualWholeRowNetWork, initialZero,
      receipt.wholePath_zero_row, complexCoordinateAmplitudeSq]
  · have energyIdentity :=
      AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
        (receipt.rowExtension_absolutelyContinuous wave waveZero)
        (receipt.rowExtension_ae_hasDerivAt wave waveZero)
    have terminalEq :=
      receipt.rowExtension_on_interval wave waveZero
        ⟨requestedTime,
          ⟨receipt.requestedTimePos.le, le_rfl⟩⟩
    have initialEq :=
      receipt.rowExtension_on_interval wave waveZero
        ⟨0, ⟨le_rfl, receipt.requestedTimePos.le⟩⟩
    rw [terminalEq, initialEq, receipt.wholePath_initial] at energyIdentity
    simpa [actualWholeRowNetWork, waveZero,
      complexCoordinateAmplitudeSq] using energyIdentity

/-- Positive viscous payment carried by the identical physical row event.
It is computed from the receipt's actual coefficient path; no shell proxy or
caller-selected payment is inserted. -/
def actualWholeRowViscousPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  if waveZero : wave = 0 then
    0
  else
    ∫ actual in (0 : ℝ)..requestedTime,
      2 * complexCoordinateRealInner
        (receipt.rowExtension wave waveZero actual)
        ((ν.coeff * integerWaveViscousMultiplier wave) •
          receipt.rowExtension wave waveZero actual)

/-- Viscosity pays a nonnegative amount on every actual receipt row. -/
theorem actualWholeRowViscousPayment_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    0 ≤ actualWholeRowViscousPayment receipt wave := by
  by_cases waveZero : wave = 0
  · simp [actualWholeRowViscousPayment, waveZero]
  · rw [actualWholeRowViscousPayment, dif_neg waveZero]
    apply intervalIntegral.integral_nonneg receipt.requestedTimePos.le
    intro actual _actualMem
    rw [complexCoordinateRealInner_real_smul_right,
      complexCoordinateRealInner_self,
      ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    have multiplierNonneg :
        0 ≤ integerWaveViscousMultiplier wave := by
      unfold integerWaveViscousMultiplier
      exact mul_nonneg (sq_nonneg _) (integerWaveNormSq_nonneg wave)
    exact mul_nonneg (by norm_num)
      (mul_nonneg
        (mul_nonneg ν.coeff_pos.le multiplierNonneg)
        (complexCoordinateAmplitudeSq_nonneg _))

/-- Actual nonlinear row work before viscous subtraction.  The definition
restores the two pieces already generated by the same unforced receipt; the
following theorem identifies its pointwise power with the receipt's whole
bilinear coefficient almost everywhere. -/
def actualWholeRowNonlinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) : ℝ :=
  actualWholeRowNetWork receipt wave +
    actualWholeRowViscousPayment receipt wave

@[simp] theorem actualWholeRowNetWork_add_viscousPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector) :
    actualWholeRowNetWork receipt wave +
        actualWholeRowViscousPayment receipt wave =
      actualWholeRowNonlinearWork receipt wave :=
  rfl

/-- On the receipt's common-time carrier, net power plus viscous payment is
the actual whole nonlinear power.  This is the same-event unforced equation,
not a name-based interpretation of the restored work. -/
theorem actualWholeRowPower_add_viscous_eq_nonlinear_ae
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (wave : IntegerWavevector)
    (waveNonzero : wave ≠ 0) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      2 * complexCoordinateRealInner
            (receipt.wholePath time wave)
            (receipt.rowTangent wave waveNonzero time) +
          2 * complexCoordinateRealInner
            (receipt.wholePath time wave)
            ((ν.coeff * integerWaveViscousMultiplier wave) •
              receipt.wholePath time wave) =
        2 * complexCoordinateRealInner
          (receipt.wholePath time wave)
          (wholeStateVorticityBilinearCoefficientAt
            (receipt.transverseLimit time).1
            (receipt.transverseLimit time).1 wave) := by
  filter_upwards [
    receipt.rowTangent_eq_unforced_ae
      wave waveNonzero] with time tangentEq
  rw [tangentEq]
  rw [complexCoordinateRealInner_sub_right]
  ring

/-- Net work paid by one finite Fourier inventory of the same receipt. -/
def actualWholeFiniteNetWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ wave ∈ modes, actualWholeRowNetWork receipt wave

/-- Finite row identities sum to the exact coefficient-enstrophy change on
the identical inventory. -/
theorem actualWholeFiniteNetWork_eq_terminal_sub_initial
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNetWork receipt modes =
      finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath
            ⟨requestedTime,
              ⟨receipt.requestedTimePos.le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy modes initialState := by
  unfold actualWholeFiniteNetWork
    finiteStateVorticityCoefficientEnstrophy
  simp_rw [actualWholeRowNetWork_eq_terminal_sub_initial]
  rw [Finset.sum_sub_distrib]

/-- Total nonnegative viscous payment on one generated finite inventory. -/
def actualWholeFiniteViscousPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ wave ∈ modes, actualWholeRowViscousPayment receipt wave

theorem actualWholeFiniteViscousPayment_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    0 ≤ actualWholeFiniteViscousPayment receipt modes := by
  unfold actualWholeFiniteViscousPayment
  exact Finset.sum_nonneg fun wave _waveMem =>
    actualWholeRowViscousPayment_nonneg receipt wave

/-- Actual nonlinear work on the identical finite inventory. -/
def actualWholeFiniteNonlinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) : ℝ :=
  ∑ wave ∈ modes, actualWholeRowNonlinearWork receipt wave

/-- Finite nonlinear work is exactly net endpoint work plus the actual
viscous payment, before any Fourier occurrence quotient is taken. -/
theorem actualWholeFiniteNetWork_add_viscousPayment
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNetWork receipt modes +
        actualWholeFiniteViscousPayment receipt modes =
      actualWholeFiniteNonlinearWork receipt modes := by
  unfold actualWholeFiniteNetWork
    actualWholeFiniteViscousPayment
    actualWholeFiniteNonlinearWork
  simp_rw [actualWholeRowNonlinearWork]
  rw [Finset.sum_add_distrib]

theorem actualWholeFiniteNetWork_le_nonlinearWork
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (modes : Finset IntegerWavevector) :
    actualWholeFiniteNetWork receipt modes ≤
      actualWholeFiniteNonlinearWork receipt modes := by
  rw [← actualWholeFiniteNetWork_add_viscousPayment]
  exact le_add_of_nonneg_right
    (actualWholeFiniteViscousPayment_nonneg receipt modes)

/-! ## Exact restart boundary and no-double-payment telescope -/

/-- Physical boundary states of the generated write-chain.  Boundary zero
is the first receipt's initial state; every successor is the actual contact
written by the preceding receipt. -/
def wholeRestartBoundaryState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ℕ → ComplexVorticityHilbertState
  | 0 => initial.initialState
  | index + 1 => (run initial index).contact.physicalState

@[simp] theorem wholeRestartBoundaryState_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    wholeRestartBoundaryState initial 0 = initial.initialState :=
  rfl

@[simp] theorem wholeRestartBoundaryState_succ
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartBoundaryState initial (index + 1) =
      (run initial index).contact.physicalState :=
  rfl

/-- The boundary at every stage is exactly that generated receipt's initial
state; restart coordinates introduce no extra physical state. -/
theorem wholeRestartBoundaryState_eq_run_initialState
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ index : ℕ,
      wholeRestartBoundaryState initial index =
        (run initial index).initialState
  | 0 => rfl
  | index + 1 => (run_succ_initialState initial index).symm

/-- Net work on one actual restart segment and one canonical native
inventory. -/
def wholeRestartSegmentNetWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFiniteNetWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- Viscous payment on the same segment and native inventory. -/
def wholeRestartSegmentViscousPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFiniteViscousPayment
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- Actual nonlinear work on the same segment and native inventory. -/
def wholeRestartSegmentNonlinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) : ℝ :=
  actualWholeFiniteNonlinearWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- Same-event segment ledger: nonlinear work is net boundary work plus its
nonnegative viscous payment. -/
theorem wholeRestartSegmentNetWork_add_viscousPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentNetWork initial index radius +
        wholeRestartSegmentViscousPayment initial index radius =
      wholeRestartSegmentNonlinearWork initial index radius := by
  exact actualWholeFiniteNetWork_add_viscousPayment
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

theorem wholeRestartSegmentViscousPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    0 ≤ wholeRestartSegmentViscousPayment initial index radius :=
  actualWholeFiniteViscousPayment_nonneg
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

theorem wholeRestartSegmentNetWork_le_nonlinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentNetWork initial index radius ≤
      wholeRestartSegmentNonlinearWork initial index radius :=
  actualWholeFiniteNetWork_le_nonlinearWork
    (run initial index).contact.prefixReceipt
    (wholeRestartModes radius)

/-- One generated segment pays exactly the finite-inventory mass change
between its actual start and contact endpoint. -/
theorem wholeRestartSegmentNetWork_eq_contact_sub_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentNetWork initial index radius =
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (run initial index).contact.physicalState -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (run initial index).initialState := by
  unfold wholeRestartSegmentNetWork
  rw [actualWholeFiniteNetWork_eq_terminal_sub_initial]
  rw [(run initial index).contact.prefixReceipt_terminal]

/-- Boundary form of the same segment payment. -/
theorem wholeRestartSegmentNetWork_eq_boundary_sub_boundary
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ) :
    wholeRestartSegmentNetWork initial index radius =
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (wholeRestartBoundaryState initial (index + 1)) -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (wholeRestartBoundaryState initial index) := by
  rw [wholeRestartSegmentNetWork_eq_contact_sub_initial,
    wholeRestartBoundaryState_succ,
    wholeRestartBoundaryState_eq_run_initialState]

/-- Actual chronological net work before one restart boundary. -/
def wholeRestartAccumulatedNetWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentNetWork initial index radius

/-- Chronological viscous payment before one restart boundary. -/
def wholeRestartAccumulatedViscousPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentViscousPayment initial index radius

/-- Chronological actual nonlinear work before one restart boundary. -/
def wholeRestartAccumulatedNonlinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) : ℝ :=
  ∑ index ∈ Finset.range length,
    wholeRestartSegmentNonlinearWork initial index radius

/-- The chronological ledger preserves the exact nonlinear/net/viscous
split and charges every actual segment once. -/
theorem wholeRestartAccumulatedNetWork_add_viscousPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedNetWork initial length radius +
        wholeRestartAccumulatedViscousPayment
          initial length radius =
      wholeRestartAccumulatedNonlinearWork initial length radius := by
  unfold wholeRestartAccumulatedNetWork
    wholeRestartAccumulatedViscousPayment
    wholeRestartAccumulatedNonlinearWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _indexMem
  exact wholeRestartSegmentNetWork_add_viscousPayment
    initial index radius

theorem wholeRestartAccumulatedViscousPayment_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    0 ≤ wholeRestartAccumulatedViscousPayment
      initial length radius := by
  unfold wholeRestartAccumulatedViscousPayment
  exact Finset.sum_nonneg fun index _indexMem =>
    wholeRestartSegmentViscousPayment_nonneg
      initial index radius

theorem wholeRestartAccumulatedNetWork_le_nonlinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length radius : ℕ) :
    wholeRestartAccumulatedNetWork initial length radius ≤
      wholeRestartAccumulatedNonlinearWork
        initial length radius := by
  rw [← wholeRestartAccumulatedNetWork_add_viscousPayment]
  exact le_add_of_nonneg_right
    (wholeRestartAccumulatedViscousPayment_nonneg
      initial length radius)

/-- All adjacent segment payments telescope on the physical boundary.
Overlapping restart coordinates are therefore charged exactly once. -/
theorem wholeRestartAccumulatedNetWork_eq_boundary_sub_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (radius : ℕ) :
    ∀ length : ℕ,
      wholeRestartAccumulatedNetWork initial length radius =
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius)
            (wholeRestartBoundaryState initial length) -
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius)
            initial.initialState
  | 0 => by
      simp [wholeRestartAccumulatedNetWork]
  | length + 1 => by
      rw [wholeRestartAccumulatedNetWork, Finset.sum_range_succ]
      change
        wholeRestartAccumulatedNetWork initial length radius +
            wholeRestartSegmentNetWork initial length radius = _
      rw [wholeRestartAccumulatedNetWork_eq_boundary_sub_initial
            initial radius length,
        wholeRestartSegmentNetWork_eq_boundary_sub_boundary]
      ring

/-! ## Canonical finite inventories exhaust the whole physical mass -/

/-- The Euclidean mass of a sharp finite projection is its literal finite
coefficient enstrophy. -/
theorem finiteStateVorticityCoefficientEnstrophy_eq_projectionMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes state =
      wholeVorticityEuclideanMass
        (complexSharpSupportProjection modes state) := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    modes (complexSharpSupportProjection modes state)
    (complexSharpSupportProjection_supported modes state)]
  exact
    (finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection
      modes state).symm

/-- Every finite inventory is a genuine nonnegative submass of the same
whole state. -/
theorem finiteStateVorticityCoefficientEnstrophy_le_wholeMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes state ≤
      wholeVorticityEuclideanMass state := by
  rw [finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
  exact wholeVorticityEuclideanMass_sharpSupportProjection_le modes state

/-- Canonical native inventories exhaust the exact Euclidean mass of every
zero-row whole state. -/
theorem finiteRestartInventoryMass_tendsto_wholeMass
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    Tendsto
      (fun radius =>
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) state)
      atTop
      (𝓝 (wholeVorticityEuclideanMass state)) := by
  have tailTendsto :=
    wholeVorticityEuclideanMass_puncturedProjection_sub_tendsto_zero
      state zeroRow
  have differenceTendsto :
      Tendsto
        (fun radius =>
          wholeVorticityEuclideanMass state -
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                  (wholeRestartModes radius) state - state))
        atTop
        (𝓝 (wholeVorticityEuclideanMass state - 0)) := by
    simpa only [wholeRestartModes] using
      (tendsto_const_nhds.sub tailTendsto)
  have pointwise :
      (fun radius =>
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) state) =
        (fun radius =>
          wholeVorticityEuclideanMass state -
            wholeVorticityEuclideanMass
              (complexSharpSupportProjection
                  (wholeRestartModes radius) state - state)) := by
    funext radius
    have split :=
      wholeVorticityEuclideanMass_eq_projection_add_complement
        (wholeRestartModes radius) state
    rw [finiteStateVorticityCoefficientEnstrophy_eq_projectionMass]
    linarith
  rw [pointwise]
  simpa using differenceTendsto

/-- A strict whole-vorticity gain between two actual contacts already
produces strictly positive signed nonlinear work on one canonical finite
inventory of the intervening source-generated receipts. -/
theorem contactMassGain_generates_finiteInventoryIcoNonlinearWork
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (start finish : ℕ)
    (startLeFinish : start ≤ finish)
    (gainPos :
      0 < restartPhysicalVorticityMass initial finish -
        restartPhysicalVorticityMass initial start) :
    ∃ radius : ℕ,
      (restartPhysicalVorticityMass initial finish -
          restartPhysicalVorticityMass initial start) / 2 <
        ∑ index ∈ Finset.Ico (start + 1) (finish + 1),
          wholeRestartSegmentNonlinearWork initial index radius := by
  let startState := (run initial start).contact.physicalState
  let finishState := (run initial finish).contact.physicalState
  let gain :=
    wholeVorticityEuclideanMass finishState -
      wholeVorticityEuclideanMass startState
  have gainEq :
      gain = restartPhysicalVorticityMass initial finish -
        restartPhysicalVorticityMass initial start := by
    rfl
  have gainPos' : 0 < gain := by
    simpa only [gainEq] using gainPos
  have terminalTendsto :=
    finiteRestartInventoryMass_tendsto_wholeMass finishState
      (run initial finish).contact.physicalState_zero
  have terminalEventually :
      ∀ᶠ radius : ℕ in atTop,
        wholeVorticityEuclideanMass finishState - gain / 2 <
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) finishState := by
    apply terminalTendsto.eventually
    exact Ioi_mem_nhds (sub_lt_self _ (half_pos gainPos'))
  rcases (eventually_atTop.1 terminalEventually) with
    ⟨radius, radiusSpec⟩
  refine ⟨radius, ?_⟩
  have terminalLower := radiusSpec radius le_rfl
  have startFiniteLe :
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) startState ≤
        wholeVorticityEuclideanMass startState :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (wholeRestartModes radius) startState
  have netWorkEq :
      (∑ index ∈ Finset.Ico (start + 1) (finish + 1),
          wholeRestartSegmentNetWork initial index radius) =
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) finishState -
          finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) startState := by
    rw [Finset.sum_Ico_eq_sub _
      (Nat.add_le_add_right startLeFinish 1)]
    change
      wholeRestartAccumulatedNetWork initial (finish + 1) radius -
          wholeRestartAccumulatedNetWork initial (start + 1) radius = _
    rw [wholeRestartAccumulatedNetWork_eq_boundary_sub_initial,
      wholeRestartAccumulatedNetWork_eq_boundary_sub_initial,
      wholeRestartBoundaryState_succ,
      wholeRestartBoundaryState_succ]
    dsimp only [startState, finishState]
    ring
  have gainHalf_lt_net :
      gain / 2 <
        ∑ index ∈ Finset.Ico (start + 1) (finish + 1),
          wholeRestartSegmentNetWork initial index radius := by
    rw [netWorkEq]
    linarith
  have net_le_nonlinear :
      (∑ index ∈ Finset.Ico (start + 1) (finish + 1),
          wholeRestartSegmentNetWork initial index radius) ≤
        ∑ index ∈ Finset.Ico (start + 1) (finish + 1),
          wholeRestartSegmentNonlinearWork initial index radius := by
    exact Finset.sum_le_sum fun index _indexMem =>
      wholeRestartSegmentNetWork_le_nonlinearWork initial index radius
  rw [← gainEq]
  exact gainHalf_lt_net.trans_le net_le_nonlinear

/-- A common ceiling on every generated finite inventory is already a
ceiling on the whole physical mass. -/
theorem wholeVorticityEuclideanMass_le_of_finiteRestartInventory_le
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (bound : ℝ)
    (finiteLe :
      ∀ radius : ℕ,
        finiteStateVorticityCoefficientEnstrophy
            (wholeRestartModes radius) state ≤
          bound) :
    wholeVorticityEuclideanMass state ≤ bound := by
  exact le_of_tendsto
    (finiteRestartInventoryMass_tendsto_wholeMass state zeroRow)
    (Filter.Eventually.of_forall finiteLe)

/-! ## Finite-time accumulation forces unbounded actual net work -/

/-- Whole physical mass at one chronological restart boundary. -/
def wholeRestartBoundaryMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) : ℝ :=
  wholeVorticityEuclideanMass
    (wholeRestartBoundaryState initial length)

/-- Every actual boundary state retains the source-owned zero row. -/
theorem wholeRestartBoundaryState_zero_row
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    ∀ length : ℕ,
      wholeRestartBoundaryState initial length 0 = 0
  | 0 => by
      rw [wholeRestartBoundaryState_zero,
        ← initial.receipt.wholePath_initial]
      exact initial.receipt.wholePath_zero_row
        ⟨0, ⟨le_rfl, initial.receipt.requestedTimePos.le⟩⟩
  | length + 1 => by
      rw [wholeRestartBoundaryState_succ]
      exact (run initial length).contact.physicalState_zero

/-- The contact-mass cascade is a literal subsequence of the chronological
boundary mass. -/
theorem elapsedTime_bddAbove_forces_boundaryMass_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove (Set.range (wholeRestartBoundaryMass initial)) := by
  intro boundaryBounded
  apply
    (elapsedTime_bddAbove_forces_physicalVorticityMass_unbounded
      initial elapsedBounded)
  rcases boundaryBounded with ⟨bound, boundSpec⟩
  refine ⟨bound, ?_⟩
  intro mass massMem
  rcases massMem with ⟨index, rfl⟩
  apply boundSpec
  refine ⟨index + 1, ?_⟩
  simp [wholeRestartBoundaryMass,
    restartPhysicalVorticityMass]

/-- If chronological boundary mass is unbounded, then the actual
finite-inventory net-work ledger is unbounded.  The inventory radius is
generated by canonical exhaustion rather than accepted as a coverage
premise. -/
theorem boundaryMass_unbounded_forces_accumulatedNetWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (boundaryUnbounded :
      ¬ BddAbove (Set.range (wholeRestartBoundaryMass initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedNetWork
          initial index.1 index.2) := by
  intro workBounded
  apply boundaryUnbounded
  rcases workBounded with ⟨workBound, workBoundSpec⟩
  let initialMass :=
    wholeVorticityEuclideanMass initial.initialState
  refine ⟨initialMass + workBound, ?_⟩
  intro mass massMem
  rcases massMem with ⟨length, rfl⟩
  apply
    wholeVorticityEuclideanMass_le_of_finiteRestartInventory_le
      (wholeRestartBoundaryState initial length)
      (wholeRestartBoundaryState_zero_row initial length)
  intro radius
  have workLe :
      wholeRestartAccumulatedNetWork initial length radius ≤
        workBound :=
    workBoundSpec ⟨(length, radius), rfl⟩
  rw [wholeRestartAccumulatedNetWork_eq_boundary_sub_initial]
    at workLe
  have initialFiniteLe :
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius) initial.initialState ≤
        initialMass := by
    exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (wholeRestartModes radius) initial.initialState
  dsimp only [initialMass]
  linarith

/-- Main hard-gate reduction: finite accumulated physical time forces
unbounded cumulative nonlinear-minus-viscous work on actual finite
inventories of the same whole-flow chain.  No crossing occurrence or
frequency cutoff appears in the mouth. -/
theorem elapsedTime_bddAbove_forces_accumulatedNetWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedNetWork
          initial index.1 index.2) :=
  boundaryMass_unbounded_forces_accumulatedNetWork_unbounded initial
    (elapsedTime_bddAbove_forces_boundaryMass_unbounded
      initial elapsedBounded)

/-- Unbounded net endpoint work cannot hide behind viscosity: the same
chronological nonlinear ledger dominates it pointwise because every viscous
payment is nonnegative. -/
theorem accumulatedNetWork_unbounded_forces_nonlinearWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (netUnbounded :
      ¬ BddAbove
        (Set.range fun index : ℕ × ℕ =>
          wholeRestartAccumulatedNetWork
            initial index.1 index.2)) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedNonlinearWork
          initial index.1 index.2) := by
  intro nonlinearBounded
  apply netUnbounded
  rcases nonlinearBounded with ⟨bound, boundSpec⟩
  refine ⟨bound, ?_⟩
  intro netWork netWorkMem
  rcases netWorkMem with ⟨index, rfl⟩
  exact le_trans
    (wholeRestartAccumulatedNetWork_le_nonlinearWork
      initial index.1 index.2)
    (boundSpec ⟨index, rfl⟩)

/-- PDE hard-gate reduction on the actual source-generated restart chain:
if its physical time accumulates finitely, then its same-event whole
nonlinear work is unbounded over internally generated chronological prefixes
and canonical Fourier inventories.  No external cutoff, work certificate,
crossing choice, or continuation oracle occurs in the theorem mouth. -/
theorem elapsedTime_bddAbove_forces_accumulatedNonlinearWork_unbounded
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ¬ BddAbove
      (Set.range fun index : ℕ × ℕ =>
        wholeRestartAccumulatedNonlinearWork
          initial index.1 index.2) :=
  accumulatedNetWork_unbounded_forces_nonlinearWork_unbounded initial
    (elapsedTime_bddAbove_forces_accumulatedNetWork_unbounded
      initial elapsedBounded)

end

end ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
end NavierStokes
end SaturationMonoid
