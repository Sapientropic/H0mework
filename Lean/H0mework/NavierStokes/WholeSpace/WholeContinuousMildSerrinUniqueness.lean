import H0mework.NavierStokes.Energy.StrongContinuationKineticDifferenceGronwall

/-!
# Domain-generic whole mild/Serrin uniqueness interface

This module separates the target-side analytic content of the existing
source-indexed strong-continuation proof from its integer-shell lineage.

`WholeContinuousMildSerrinReceipt` records one actual unforced solution on
the whole Fourier carrier: a continuous Hilbert path, its common space-time
state, transverse/reality/zero-mode responsibility, the rowwise mild and
derivative laws, and the whole gradient budget.  It deliberately contains no
lineage, critical threshold, prefix receipt, coverage statement, or generated
numerical ceiling.

The actual rowwise laws are converted below into the complete whole-carrier
kinetic inequality and then into same-initial uniqueness.  In particular,
the final theorem does not accept an energy-payment certificate: viscosity,
incompressibility, Fourier reality, and the generated whole gradient budget
produce that payment internally.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

open scoped ENNReal Topology InnerProductSpace

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeGradientLowerSemicontinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteMildDuhamel
open ThreeDimensionalVorticityCoefficientWholeTangentEnergyTransport
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeNonlinearNegativeOne
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeContinuousMild
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptSquareContinuation
open ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

/--
One whole continuous mild Navier--Stokes path with exactly the target-side
data used by the strong-continuation energy argument.

The row extension is kept on the real line because the existing energy proof
uses absolute continuity there.  Its derivative is first recorded as an
actual source-independent tangent and then identified, on the physical
interval, with the unforced nonlinear-minus-viscous row.
-/
structure WholeContinuousMildSerrinReceipt
    (ν : Viscosity)
    (initialState : ComplexVorticityHilbertState)
    (requestedTime : ℝ) where
  requestedTimePos : 0 < requestedTime
  stateLimit : SpaceTimeState requestedTime
  transverseLimit : TransverseSpaceTimeState requestedTime
  stateLimit_eq_transverse :
    transverseSpaceTimeInclusion requestedTime transverseLimit = stateLimit
  wholePath :
    BoundedContinuousFunction
      (Icc (0 : ℝ) requestedTime)
      ComplexVorticityHilbertState
  wholePath_toLp_eq_stateLimit :
    BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ wholePath = stateLimit
  wholePath_initial :
    wholePath ⟨0, ⟨le_rfl, requestedTimePos.le⟩⟩ = initialState
  wholePath_zero_row :
    ∀ time : Icc (0 : ℝ) requestedTime, wholePath time 0 = 0
  transverse_fourierReality_ae :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      FiniteStateFourierReality (transverseLimit time).1
  gradient_summable :
    Summable fun wave : IntegerWavevector =>
      wholeSpaceTimeVorticityGradientDensity requestedTime stateLimit wave
  wholeTangent : SpaceTimeState requestedTime
  wholeTangent_eq_unforced_ae :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      wholeTangent time =
        wholeSpaceTimeNonlinearNegativeOneFunction transverseLimit time -
          wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff stateLimit time
  rowExtension :
    ∀ wave : IntegerWavevector, wave ≠ 0 → ℝ → ComplexCoordinateVector
  rowExtension_on_interval :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      rowExtension wave waveNe time.1 = wholePath time wave
  rowTangent :
    ∀ wave : IntegerWavevector, wave ≠ 0 →
      Icc (0 : ℝ) requestedTime → ComplexCoordinateVector
  rowTangent_eq_unforced_ae :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        rowTangent wave waveNe time =
          wholeStateVorticityBilinearCoefficientAt
              (transverseLimit time).1 (transverseLimit time).1 wave -
            (ν.coeff * integerWaveViscousMultiplier wave) •
              wholePath time wave
  rowTangent_eq_wholeTangent_ae :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        (Real.sqrt (integerWaveViscousMultiplier wave) : ℂ) •
            (wholeTangent time) wave = rowTangent wave waveNe time
  rowExtension_absolutelyContinuous :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      AbsolutelyContinuousOnInterval
        (rowExtension wave waveNe) 0 requestedTime
  rowExtension_ae_hasDerivAt :
    ∀ (wave : IntegerWavevector) (waveNe : wave ≠ 0),
      ∀ᵐ actual : ℝ,
        actual ∈ uIcc (0 : ℝ) requestedTime →
          HasDerivAt
            (rowExtension wave waveNe)
            (commonTimeZeroExtension requestedTime
              (rowTangent wave waveNe) actual)
            actual
  row_mild_identity :
    ∀ (wave : IntegerWavevector) (_waveNe : wave ≠ 0)
      (time : Icc (0 : ℝ) requestedTime),
      wholePath time wave =
        fixedWaveHeatDuhamelValue requestedTime ν.coeff wave
          (initialState wave)
          (transverseSpaceTimeNonlinearRow transverseLimit wave) time

/-- The intrinsic critical Serrin density of a whole mild receipt. -/
def WholeContinuousMildSerrinReceipt.serrinDensity
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    Icc (0 : ℝ) requestedTime → ℝ :=
  fun time =>
    wholeStateVelocityMajorant
      ((BoundedContinuousFunction.toLp 2
        (commonTimeMeasure requestedTime) ℂ receipt.wholePath) time) ^ 2

/--
The whole gradient carrier, rather than source lineage bookkeeping, supplies
the critical Serrin integrability used by the difference-energy consumer.
-/
theorem WholeContinuousMildSerrinReceipt.serrinDensity_integrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    Integrable receipt.serrinDensity (commonTimeMeasure requestedTime) := by
  change Integrable
    (fun time =>
      wholeStateVelocityMajorant
        ((BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ receipt.wholePath) time) ^ 2)
    (commonTimeMeasure requestedTime)
  rw [receipt.wholePath_toLp_eq_stateLimit]
  exact wholeVelocityMajorantSq_integrable
    requestedTime receipt.stateLimit receipt.gradient_summable

/--
The intrinsic real-line Grönwall coefficient generated by one actual whole
mild path.  Its only scalar factor is the reciprocal of the already fixed
physical viscosity; no cutoff, ceiling, or caller-selected absorption
constant enters this definition.
-/
def actualWholeDifferenceSerrinCoefficient
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    ν.coeff⁻¹ * receipt.serrinDensity time

theorem actualWholeDifferenceSerrinCoefficient_nonneg
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (time : ℝ) (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    0 ≤ actualWholeDifferenceSerrinCoefficient receipt time := by
  rw [actualWholeDifferenceSerrinCoefficient,
    commonTimeZeroExtension_of_mem requestedTime _ time timeMem]
  exact mul_nonneg (inv_nonneg.2 ν.coeff_pos.le)
    (sq_nonneg _)

/--
Reusable scalar kinetic Grönwall consumer.  The whole mild theorem below
derives `energyPayment` from its actual unforced row laws before invoking this
lemma.  No target equality, continuation endpoint, lineage, coverage, or
generated coefficient is accepted.
-/
theorem kineticMass_eq_zero_of_actual_energy_payment
    {coefficient kineticMass : ℝ → ℝ}
    {requestedTime bound : ℝ}
    (requestedTimeNonneg : 0 ≤ requestedTime)
    (coefficientIntegrable :
      IntervalIntegrable coefficient volume 0 requestedTime)
    (coefficientNonneg :
      ∀ time ∈ Icc (0 : ℝ) requestedTime, 0 ≤ coefficient time)
    (kineticMassContinuous :
      ContinuousOn kineticMass (Icc (0 : ℝ) requestedTime))
    (kineticMassNonneg :
      ∀ time ∈ Icc (0 : ℝ) requestedTime, 0 ≤ kineticMass time)
    (kineticMassLeBound :
      ∀ time ∈ Icc (0 : ℝ) requestedTime, kineticMass time ≤ bound)
    (energyPayment :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        kineticMass time ≤
          ∫ earlier in (0 : ℝ)..time,
            coefficient earlier * kineticMass earlier) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime, kineticMass time = 0 := by
  exact eq_zero_of_nonneg_le_integral_mul
    requestedTimeNonneg coefficientIntegrable coefficientNonneg
    kineticMassContinuous kineticMassNonneg kineticMassLeBound energyPayment

private theorem commonTimeZeroExtension_intervalIntegrable_of_integrable
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (requestedTime : ℝ) (requestedTimeNonneg : 0 ≤ requestedTime)
    (value : Icc (0 : ℝ) requestedTime → E)
    (valueIntegrable : Integrable value (commonTimeMeasure requestedTime)) :
    IntervalIntegrable
      (commonTimeZeroExtension requestedTime value) volume 0 requestedTime := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le requestedTimeNonneg,
    integrableOn_iff_comap_subtypeVal measurableSet_Icc]
  have measureEq : commonTimeMeasure requestedTime =
      Measure.comap (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ) volume := by
    unfold commonTimeMeasure
    rw [MeasurableEmbedding.comap_restrict
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
    simp
  rw [← measureEq]
  apply valueIntegrable.congr
  filter_upwards with time
  simp only [Function.comp_apply]
  rw [commonTimeZeroExtension_of_mem requestedTime value time.1 time.property]

theorem actualWholeDifferenceSerrinCoefficient_intervalIntegrable
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime) :
    IntervalIntegrable
      (actualWholeDifferenceSerrinCoefficient receipt)
      volume 0 requestedTime := by
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable
    requestedTime receipt.requestedTimePos.le
  exact receipt.serrinDensity_integrable.const_mul ν.coeff⁻¹

/-! ## Source-free row difference transport -/

/-- The real-line row difference of two actual whole mild paths. -/
def actualRowDifferencePath
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    ℝ → ComplexCoordinateVector :=
  left.rowExtension wave waveNe - right.rowExtension wave waveNe

/-- The exact unforced tangent of `actualRowDifferencePath`. -/
def actualRowDifferenceTangent
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    ℝ → ComplexCoordinateVector :=
  fun actual =>
    commonTimeZeroExtension requestedTime (left.rowTangent wave waveNe) actual -
      commonTimeZeroExtension requestedTime (right.rowTangent wave waveNe) actual

theorem actualRowDifferencePath_absolutelyContinuous
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    AbsolutelyContinuousOnInterval
      (actualRowDifferencePath left right wave waveNe) 0 requestedTime := by
  exact
    (left.rowExtension_absolutelyContinuous wave waveNe).sub
      (right.rowExtension_absolutelyContinuous wave waveNe)

theorem actualRowDifferencePath_ae_hasDerivAt
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) requestedTime →
        HasDerivAt
          (actualRowDifferencePath left right wave waveNe)
          (actualRowDifferenceTangent left right wave waveNe actual)
          actual := by
  filter_upwards [
    left.rowExtension_ae_hasDerivAt wave waveNe,
    right.rowExtension_ae_hasDerivAt wave waveNe] with
      actual leftDeriv rightDeriv
  intro actualMem
  exact (leftDeriv actualMem).sub (rightDeriv actualMem)

theorem actualRowDifferencePath_initial
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0) :
    actualRowDifferencePath left right wave waveNe 0 = 0 := by
  have leftAtZero := left.rowExtension_on_interval wave waveNe
    ⟨0, ⟨le_rfl, left.requestedTimePos.le⟩⟩
  have rightAtZero := right.rowExtension_on_interval wave waveNe
    ⟨0, ⟨le_rfl, right.requestedTimePos.le⟩⟩
  change left.rowExtension wave waveNe 0 - right.rowExtension wave waveNe 0 = 0
  rw [leftAtZero, rightAtZero,
    left.wholePath_initial, right.wholePath_initial, sub_self]

/--
Exact endpoint energy transport for one nonzero row.  This is the
source-free replacement for the rowwise part of the old
`StrongContinuationDifferenceEnergy` ledger.
-/
theorem actualRowDifference_endpointEnergy_identity
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : IntegerWavevector) (waveNe : wave ≠ 0)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∫ actual in (0 : ℝ)..terminal.1,
        2 * complexCoordinateRealInner
          (actualRowDifferencePath left right wave waveNe actual)
          (actualRowDifferenceTangent left right wave waveNe actual)) =
      complexCoordinateAmplitudeSq
        (left.wholePath terminal wave - right.wholePath terminal wave) := by
  have pathAC :=
    (actualRowDifferencePath_absolutelyContinuous left right wave waveNe).mono <| by
      rw [uIcc_of_le terminal.2.1, uIcc_of_le left.requestedTimePos.le]
      exact Icc_subset_Icc le_rfl terminal.2.2
  have pathDerivative :
      ∀ᵐ actual : ℝ,
        actual ∈ uIcc (0 : ℝ) terminal.1 →
          HasDerivAt
            (actualRowDifferencePath left right wave waveNe)
            (actualRowDifferenceTangent left right wave waveNe actual)
            actual := by
    filter_upwards [
      actualRowDifferencePath_ae_hasDerivAt left right wave waveNe] with
        actual derivative
    intro actualMem
    apply derivative
    have actualMemIcc : actual ∈ Icc (0 : ℝ) terminal.1 := by
      simpa only [uIcc_of_le terminal.2.1] using actualMem
    simpa only [uIcc_of_le terminal.2.1,
      uIcc_of_le left.requestedTimePos.le] using
      (Icc_subset_Icc le_rfl terminal.2.2 actualMemIcc)
  have energyIdentity :=
    AbsolutelyContinuousOnInterval.complexCoordinateAmplitudeSq_energy_identity
      pathAC pathDerivative
  have endpointEq :
      actualRowDifferencePath left right wave waveNe terminal.1 =
        left.wholePath terminal wave - right.wholePath terminal wave := by
    change left.rowExtension wave waveNe terminal.1 -
      right.rowExtension wave waveNe terminal.1 = _
    rw [left.rowExtension_on_interval wave waveNe terminal,
      right.rowExtension_on_interval wave waveNe terminal]
  rw [endpointEq,
    actualRowDifferencePath_initial left right wave waveNe] at energyIdentity
  simpa [complexCoordinateAmplitudeSq] using energyIdentity

/-! ## Whole kinetic carrier -/

/-- The complete kinetic mass of two actual whole paths, zero-extended only
outside their common physical interval. -/
def actualWholeDifferenceKineticMass
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → ℝ :=
  commonTimeZeroExtension requestedTime fun time =>
    puncturedWholeVorticityKineticMass
      (left.wholePath time - right.wholePath time)

@[simp] theorem actualWholeDifferenceKineticMass_of_mem
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ) (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    actualWholeDifferenceKineticMass left right time =
      puncturedWholeVorticityKineticMass
        (left.wholePath ⟨time, timeMem⟩ -
          right.wholePath ⟨time, timeMem⟩) := by
  rw [actualWholeDifferenceKineticMass,
    commonTimeZeroExtension_of_mem requestedTime _ time timeMem]

theorem actualWholeDifferenceKineticMass_nonneg
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : ℝ) (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    0 ≤ actualWholeDifferenceKineticMass left right time := by
  rw [actualWholeDifferenceKineticMass_of_mem left right time timeMem]
  exact puncturedWholeVorticityKineticMass_nonneg _

theorem actualWholeDifferenceKineticMass_continuousOn
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ContinuousOn
      (actualWholeDifferenceKineticMass left right)
      (Icc (0 : ℝ) requestedTime) := by
  rw [continuousOn_iff_continuous_restrict]
  have pathContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        left.wholePath time - right.wholePath time :=
    left.wholePath.continuous.sub right.wholePath.continuous
  have massContinuous :
      Continuous fun time : Icc (0 : ℝ) requestedTime =>
        puncturedWholeVorticityKineticMass
          (left.wholePath time - right.wholePath time) :=
    continuous_puncturedWholeVorticityKineticMass.comp pathContinuous
  convert massContinuous using 1
  funext time
  exact actualWholeDifferenceKineticMass_of_mem
    left right time.1 time.2

theorem actualWholeDifferenceKineticMass_bounded
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∃ bound : ℝ,
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        actualWholeDifferenceKineticMass left right time ≤ bound := by
  obtain ⟨bound, boundUpper⟩ :=
    isCompact_Icc.bddAbove_image
      (actualWholeDifferenceKineticMass_continuousOn left right)
  exact ⟨bound, fun time timeMem =>
    boundUpper (mem_image_of_mem _ timeMem)⟩

/-- One nonzero row's exact kinetic-scale work, before any lattice sum. -/
def actualRowDifferenceKineticWork
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) : ℝ :=
  (∫ actual in (0 : ℝ)..terminal.1,
      2 * complexCoordinateRealInner
        (actualRowDifferencePath left right wave.1 wave.2 actual)
        (actualRowDifferenceTangent left right wave.1 wave.2 actual)) /
    integerWaveViscousMultiplier wave.1

theorem actualRowDifferenceKineticWork_eq
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime)
    (wave : NonzeroIntegerWavevector) :
    actualRowDifferenceKineticWork left right terminal wave =
      complexCoordinateAmplitudeSq
          (left.wholePath terminal wave.1 - right.wholePath terminal wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  rw [actualRowDifferenceKineticWork,
    actualRowDifference_endpointEnergy_identity left right wave.1 wave.2 terminal]

theorem finiteRowDifferenceKinetic_endpointEnergy_identity
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime)
    (waves : Finset NonzeroIntegerWavevector) :
    (∑ wave ∈ waves,
      actualRowDifferenceKineticWork left right terminal wave) =
      ∑ wave ∈ waves,
        complexCoordinateAmplitudeSq
            (left.wholePath terminal wave.1 - right.wholePath terminal wave.1) /
          integerWaveViscousMultiplier wave.1 := by
  apply Finset.sum_congr rfl
  intro wave _
  exact actualRowDifferenceKineticWork_eq left right terminal wave

theorem tsum_actualRowDifferenceKineticWork_eq
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∑' wave : NonzeroIntegerWavevector,
      actualRowDifferenceKineticWork left right terminal wave) =
      actualWholeDifferenceKineticMass left right terminal.1 := by
  rw [actualWholeDifferenceKineticMass_of_mem left right terminal.1 terminal.2]
  apply tsum_congr
  intro wave
  exact actualRowDifferenceKineticWork_eq left right terminal wave

theorem WholeContinuousMildSerrinReceipt.wholePath_eq_transverse_ae
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt : WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      receipt.wholePath time = (receipt.transverseLimit time).1 := by
  have pathAE :=
    BoundedContinuousFunction.coeFn_toLp
      (p := (2 : ℝ≥0∞))
      (μ := commonTimeMeasure requestedTime) ℂ receipt.wholePath
  have inclusionAE := transverseSpaceTimeInclusion_coeFn
    requestedTime receipt.transverseLimit
  filter_upwards [pathAE, inclusionAE] with time pathEq inclusionEq
  calc
    receipt.wholePath time =
        (BoundedContinuousFunction.toLp 2
          (commonTimeMeasure requestedTime) ℂ receipt.wholePath) time :=
      pathEq.symm
    _ = receipt.stateLimit time := by rw [receipt.wholePath_toLp_eq_stateLimit]
    _ = (transverseSpaceTimeInclusion requestedTime receipt.transverseLimit) time := by
      rw [receipt.stateLimit_eq_transverse]
    _ = (receipt.transverseLimit time).1 := inclusionEq

/-- The complete `L²_t H⁻¹_x` tangent difference before any coordinate
projection. -/
def actualWholeDifferenceTangent
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    SpaceTimeState requestedTime :=
  left.wholeTangent - right.wholeTangent

theorem actualWholeDifferenceTangent_eq_unforced_ae
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWholeDifferenceTangent left right time =
        (wholeSpaceTimeNonlinearNegativeOneFunction
            left.transverseLimit time -
          wholeSpaceTimeNonlinearNegativeOneFunction
            right.transverseLimit time) -
        (wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff left.stateLimit time -
          wholeSpaceTimeViscousNegativeOneFunction
            ν.coeff right.stateLimit time) := by
  filter_upwards [
    MeasureTheory.Lp.coeFn_sub left.wholeTangent right.wholeTangent,
    left.wholeTangent_eq_unforced_ae,
    right.wholeTangent_eq_unforced_ae] with time tangentEq leftEq rightEq
  rw [actualWholeDifferenceTangent, tangentEq, Pi.sub_apply, leftEq, rightEq]
  abel

/-- One `L²_t` kinetic coordinate of the complete difference tangent. -/
def actualWholeDifferenceKineticCoordinateTangentLp
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    MeasureTheory.Lp (lp (fun _ : IntegerWavevector => ℂ) 2) 2
      (commonTimeMeasure requestedTime) :=
  ((wholePuncturedCoordinateSliceCLM coordinate).compLpL 2
    (commonTimeMeasure requestedTime))
    (actualWholeDifferenceTangent left right)

/-- One real-line kinetic coordinate of the complete difference tangent. -/
def actualWholeDifferenceKineticCoordinateTangent
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → lp (fun _ : IntegerWavevector => ℂ) 2 :=
  commonTimeZeroExtension requestedTime
    (actualWholeDifferenceKineticCoordinateTangentLp
      coordinate left right)

theorem actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    IntervalIntegrable
      (actualWholeDifferenceKineticCoordinateTangent coordinate left right)
      volume 0 requestedTime := by
  change IntervalIntegrable
    (commonTimeZeroExtension requestedTime
      (actualWholeDifferenceKineticCoordinateTangentLp
        coordinate left right))
    volume 0 requestedTime
  apply commonTimeZeroExtension_intervalIntegrable_of_integrable
    requestedTime left.requestedTimePos.le
  have onUniv := integrableOn_Lp_of_measure_ne_top
    (actualWholeDifferenceKineticCoordinateTangentLp
      coordinate left right)
    fact_one_le_two_ennreal.elim
    (measure_ne_top (commonTimeMeasure requestedTime) Set.univ)
  simpa only [integrableOn_univ] using onUniv

theorem actualWholeDifferenceKineticCoordinateTangentLp_apply_ae
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWholeDifferenceKineticCoordinateTangentLp
          coordinate left right time wave.1 =
        ((Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹ *
          (left.rowTangent wave.1 wave.2 time -
            right.rowTangent wave.1 wave.2 time) coordinate) := by
  have projectedAE :=
    (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
      (actualWholeDifferenceTangent left right)
  have tangentDifferenceAE :=
    MeasureTheory.Lp.coeFn_sub left.wholeTangent right.wholeTangent
  filter_upwards [
    projectedAE,
    tangentDifferenceAE,
    left.rowTangent_eq_wholeTangent_ae wave.1 wave.2,
    right.rowTangent_eq_wholeTangent_ae wave.1 wave.2] with
      time projectedEq tangentDifferenceEq leftRowEq rightRowEq
  have unweightedEq :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) •
          (actualWholeDifferenceTangent left right time) wave.1 =
        left.rowTangent wave.1 wave.2 time -
          right.rowTangent wave.1 wave.2 time := by
    rw [actualWholeDifferenceTangent, tangentDifferenceEq]
    change
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) •
          ((left.wholeTangent time) wave.1 -
            (right.wholeTangent time) wave.1) =
        _
    rw [smul_sub, leftRowEq, rightRowEq]
  have sqrtNe :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Real.sqrt_pos.2
        (integerWaveViscousMultiplier_pos wave)).ne'
  rw [actualWholeDifferenceKineticCoordinateTangentLp,
    projectedEq,
    wholePuncturedCoordinateSliceCLM_apply_of_ne
      coordinate (actualWholeDifferenceTangent left right time)
      wave.1 wave.2]
  have coordinateEq := congrFun unweightedEq coordinate
  simp only [Pi.smul_apply, smul_eq_mul] at coordinateEq
  rw [← coordinateEq]
  field_simp

private theorem actualRowDifferenceTangent_subtype_integrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    Integrable
      (fun time : Icc (0 : ℝ) requestedTime =>
        left.rowTangent wave.1 wave.2 time -
          right.rowTangent wave.1 wave.2 time)
      (commonTimeMeasure requestedTime) := by
  rw [MeasureTheory.integrable_pi_iff]
  intro coordinate
  let tangentCoordinateLp :
      MeasureTheory.Lp ℂ 2 (commonTimeMeasure requestedTime) :=
    ((lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ℂ) 2 wave.1).compLpL
        2 (commonTimeMeasure requestedTime))
      (actualWholeDifferenceKineticCoordinateTangentLp
        coordinate left right)
  have coordinateIntegrable :
      Integrable (fun time => tangentCoordinateLp time)
        (commonTimeMeasure requestedTime) := by
    have onUniv :=
      integrableOn_Lp_of_measure_ne_top
        tangentCoordinateLp fact_one_le_two_ennreal.elim
        (measure_ne_top
          (commonTimeMeasure requestedTime) Set.univ)
    simpa only [integrableOn_univ] using onUniv
  have scaledIntegrable :=
    coordinateIntegrable.const_mul
      (Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ)
  apply scaledIntegrable.congr
  have evaluatedAE :=
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ℂ) 2 wave.1).coeFn_compLpL
        (actualWholeDifferenceKineticCoordinateTangentLp
          coordinate left right)
  filter_upwards [
    evaluatedAE,
    actualWholeDifferenceKineticCoordinateTangentLp_apply_ae
      coordinate left right wave] with time evaluatedEq tangentEq
  have sqrtNe :
      (Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Real.sqrt_pos.2
        (integerWaveViscousMultiplier_pos wave)).ne'
  change
    (Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ) *
        tangentCoordinateLp time =
      (left.rowTangent wave.1 wave.2 time -
        right.rowTangent wave.1 wave.2 time) coordinate
  rw [evaluatedEq]
  change
    (Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ) *
        actualWholeDifferenceKineticCoordinateTangentLp
          coordinate left right time wave.1 =
      _
  rw [tangentEq]
  field_simp

theorem actualRowDifferenceTangent_intervalIntegrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : NonzeroIntegerWavevector) :
    IntervalIntegrable
      (actualRowDifferenceTangent
        left right wave.1 wave.2)
      volume 0 requestedTime := by
  have generated :=
    commonTimeZeroExtension_intervalIntegrable_of_integrable
      requestedTime left.requestedTimePos.le
      (fun time : Icc (0 : ℝ) requestedTime =>
        left.rowTangent wave.1 wave.2 time -
          right.rowTangent wave.1 wave.2 time)
      (actualRowDifferenceTangent_subtype_integrable
        left right wave)
  have tangentEq :
      actualRowDifferenceTangent
          left right wave.1 wave.2 =
        commonTimeZeroExtension requestedTime
          (fun time : Icc (0 : ℝ) requestedTime =>
            left.rowTangent wave.1 wave.2 time -
              right.rowTangent wave.1 wave.2 time) := by
    funext actual
    by_cases actualMem :
        actual ∈ Icc (0 : ℝ) requestedTime
    · simp only [actualRowDifferenceTangent,
        commonTimeZeroExtension_of_mem
          requestedTime _ actual actualMem]
    · simp [actualRowDifferenceTangent,
        commonTimeZeroExtension, actualMem]
  rw [tangentEq]
  exact generated

theorem actualRowDifferencePath_eq_intervalIntegral
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (wave : NonzeroIntegerWavevector)
    (time : ℝ)
    (timeMem : time ∈ Icc (0 : ℝ) requestedTime) :
    actualRowDifferencePath left right wave.1 wave.2 time =
      ∫ earlier in (0 : ℝ)..time,
        actualRowDifferenceTangent
          left right wave.1 wave.2 earlier := by
  have update :=
    path_sub_eq_intervalIntegral
      (actualRowDifferencePath_absolutelyContinuous
        left right wave.1 wave.2)
      (actualRowDifferenceTangent_intervalIntegrable
        left right wave)
      (actualRowDifferencePath_ae_hasDerivAt
        left right wave.1 wave.2)
      time
      (by
        simpa [uIcc_of_le left.requestedTimePos.le] using
          timeMem)
  rw [actualRowDifferencePath_initial
    left right wave.1 wave.2, sub_zero] at update
  exact update

/-- Bochner primitive of one whole kinetic-coordinate tangent. -/
def actualWholeDifferenceKineticCoordinateIntegralPath
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → lp (fun _ : IntegerWavevector => ℂ) 2 :=
  fun time => ∫ earlier in (0 : ℝ)..time,
    actualWholeDifferenceKineticCoordinateTangent coordinate left right earlier

theorem actualWholeDifferenceKineticCoordinateIntegralPath_absolutelyContinuous
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    AbsolutelyContinuousOnInterval
      (actualWholeDifferenceKineticCoordinateIntegralPath coordinate left right)
      0 requestedTime := by
  exact IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
    (actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right)
    (by
      rw [uIcc_of_le left.requestedTimePos.le]
      exact ⟨le_rfl, left.requestedTimePos.le⟩)

theorem actualWholeDifferenceKineticCoordinateIntegralPath_ae_hasDerivAt
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ actual : ℝ,
      actual ∈ uIcc (0 : ℝ) requestedTime →
        HasDerivAt
          (actualWholeDifferenceKineticCoordinateIntegralPath
            coordinate left right)
          (actualWholeDifferenceKineticCoordinateTangent
            coordinate left right actual)
          actual := by
  filter_upwards [
    (actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right).ae_hasDerivAt_integral] with actual derivative
  intro actualMem
  exact derivative actualMem 0 (by simp)

/--
The Bochner primitive of the complete weighted tangent is exactly the
canonical kinetic weighting of the whole path difference.
-/
theorem actualWholeDifferenceKineticCoordinateIntegralPath_eq
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    actualWholeDifferenceKineticCoordinateIntegralPath
        coordinate left right time.1 =
      wholeKineticCoordinateSliceCLM coordinate
        (left.wholePath time - right.wholePath time) := by
  apply lp.ext
  funext wave
  have tangentIntegrableAt :
      IntervalIntegrable
        (actualWholeDifferenceKineticCoordinateTangent
          coordinate left right)
        volume 0 time.1 :=
    (actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right).mono_set <| by
        rw [uIcc_of_le time.property.1,
          uIcc_of_le left.requestedTimePos.le]
        exact Icc_subset_Icc le_rfl time.property.2
  have evaluatedIntegral :=
    (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave)
      |>.intervalIntegral_comp_comm tangentIntegrableAt
  change
    (lp.evalCLM ℂ (fun _ : IntegerWavevector => ℂ) 2 wave)
        (actualWholeDifferenceKineticCoordinateIntegralPath
          coordinate left right time.1) =
      _
  rw [actualWholeDifferenceKineticCoordinateIntegralPath,
    ← evaluatedIntegral]
  change
    (∫ earlier in (0 : ℝ)..time.1,
        actualWholeDifferenceKineticCoordinateTangent
          coordinate left right earlier wave) =
      _
  by_cases waveNe : wave ≠ 0
  · let indexedWave : NonzeroIntegerWavevector :=
      ⟨wave, waveNe⟩
    have converted :=
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime left.requestedTimePos.le time
        (fun earlier =>
          actualWholeDifferenceKineticCoordinateTangent
            coordinate left right earlier wave)
    have tangentAE :=
      actualWholeDifferenceKineticCoordinateTangentLp_apply_ae
        coordinate left right indexedWave
    have setIntegralEq :
        (∫ actual in Iic time,
            actualWholeDifferenceKineticCoordinateTangent
              coordinate left right actual.1 wave
            ∂(commonTimeMeasure requestedTime)) =
          ∫ actual in Iic time,
            ((Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
              (left.rowTangent wave waveNe actual -
                right.rowTangent wave waveNe actual) coordinate)
            ∂(commonTimeMeasure requestedTime) := by
      apply MeasureTheory.integral_congr_ae
      have restricted :
          ∀ᵐ actual ∂
              (commonTimeMeasure requestedTime).restrict (Iic time),
            actualWholeDifferenceKineticCoordinateTangentLp
                coordinate left right actual wave =
              ((Real.sqrt
                  (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
                (left.rowTangent wave waveNe actual -
                  right.rowTangent wave waveNe actual) coordinate) :=
        MeasureTheory.ae_restrict_le tangentAE
      filter_upwards [restricted] with actual equality
      rw [actualWholeDifferenceKineticCoordinateTangent,
        commonTimeZeroExtension_of_mem
          requestedTime _ actual.1 actual.property]
      exact equality
    have coordinateIntegral :=
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[ℂ] ℂ)
        |>.intervalIntegral_comp_comm
          ((actualRowDifferenceTangent_intervalIntegrable
            left right indexedWave).mono_set <| by
              rw [uIcc_of_le time.property.1,
                uIcc_of_le left.requestedTimePos.le]
              exact Icc_subset_Icc le_rfl time.property.2)
    have coordinateIntegral' :
        (∫ earlier in (0 : ℝ)..time.1,
            actualRowDifferenceTangent
              left right wave waveNe earlier coordinate) =
          (∫ earlier in (0 : ℝ)..time.1,
            actualRowDifferenceTangent
              left right wave waveNe earlier) coordinate :=
      coordinateIntegral
    rw [← converted, setIntegralEq]
    have setIntegralEqReal :
        (∫ actual in Iic time,
            ((Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
              (left.rowTangent wave waveNe actual -
                right.rowTangent wave waveNe actual) coordinate)
            ∂(commonTimeMeasure requestedTime)) =
          ∫ earlier in (0 : ℝ)..time.1,
            ((Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ)⁻¹ *
              actualRowDifferenceTangent
                left right wave waveNe earlier coordinate) := by
      rw [← commonTime_integral_Iic_eq_intervalIntegral
        requestedTime left.requestedTimePos.le time]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with earlier
      rw [actualRowDifferenceTangent,
        commonTimeZeroExtension_of_mem
          requestedTime _ earlier.1 earlier.property,
        commonTimeZeroExtension_of_mem
          requestedTime _ earlier.1 earlier.property]
    rw [setIntegralEqReal,
      intervalIntegral.integral_const_mul,
      coordinateIntegral',
      ← actualRowDifferencePath_eq_intervalIntegral
        left right indexedWave time.1 time.property]
    have pathEq :
        actualRowDifferencePath
            left right wave waveNe time.1 =
          left.wholePath time wave -
            right.wholePath time wave := by
      change
        left.rowExtension wave waveNe time.1 -
            right.rowExtension wave waveNe time.1 =
          left.wholePath time wave -
            right.wholePath time wave
      rw [left.rowExtension_on_interval wave waveNe time,
        right.rowExtension_on_interval wave waveNe time]
    rw [pathEq]
    simp [wholeKineticCoordinateSliceCLM_apply,
      wholeKineticFourierWeight, waveNe]
    ring
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    have projectedAE :=
      (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
        (actualWholeDifferenceTangent left right)
    have converted :=
      commonTime_integral_Iic_eq_intervalIntegral
        requestedTime left.requestedTimePos.le time
        (fun earlier =>
          actualWholeDifferenceKineticCoordinateTangent
            coordinate left right earlier 0)
    have setIntegralZero :
        (∫ actual in Iic time,
            actualWholeDifferenceKineticCoordinateTangent
              coordinate left right actual.1 0
            ∂(commonTimeMeasure requestedTime)) = 0 := by
      calc
        (∫ actual in Iic time,
            actualWholeDifferenceKineticCoordinateTangent
              coordinate left right actual.1 0
            ∂(commonTimeMeasure requestedTime)) =
            ∫ actual in Iic time, (0 : ℂ)
              ∂(commonTimeMeasure requestedTime) := by
          apply MeasureTheory.integral_congr_ae
          have restricted :
              ∀ᵐ actual ∂
                  (commonTimeMeasure requestedTime).restrict (Iic time),
                actualWholeDifferenceKineticCoordinateTangentLp
                    coordinate left right actual =
                  wholePuncturedCoordinateSliceCLM coordinate
                    (actualWholeDifferenceTangent
                      left right actual) :=
            MeasureTheory.ae_restrict_le projectedAE
          filter_upwards [restricted] with actual equality
          rw [actualWholeDifferenceKineticCoordinateTangent,
            commonTimeZeroExtension_of_mem
              requestedTime _ actual.1 actual.property,
            equality,
            wholePuncturedCoordinateSliceCLM_apply_zero]
        _ = 0 := by simp
    rw [← converted, setIntegralZero]
    simp [wholeKineticCoordinateSliceCLM_apply,
      wholeKineticFourierWeight]

private theorem
    wholeMildPuncturedCoordinateSlice_eq_coordinateSlice_of_zero_row
    (coordinate : Coordinate)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    wholePuncturedCoordinateSliceCLM coordinate state =
      wholeCoordinateSliceCLM coordinate state := by
  apply lp.ext
  funext wave
  by_cases waveNe : wave ≠ 0
  · rw [wholePuncturedCoordinateSliceCLM_apply_of_ne
      coordinate state wave waveNe,
    wholeCoordinateSliceCLM_apply]
  · have waveZero : wave = 0 := not_ne_iff.mp waveNe
    subst wave
    rw [wholePuncturedCoordinateSliceCLM_apply_zero,
      wholeCoordinateSliceCLM_apply, zeroRow]
    simp

private theorem wholeMildViscousNegativeOneState_sub
    (ν : ℝ)
    (left right : ComplexVorticityHilbertState)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    wholeStateVorticityViscousNegativeOneState
          ν left leftGradientSummable -
        wholeStateVorticityViscousNegativeOneState
          ν right rightGradientSummable =
      wholeStateVorticityViscousNegativeOneState
        ν (left - right)
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) := by
  apply lp.ext
  funext wave
  change
    wholeStateVorticityViscousNegativeOneState
          ν left leftGradientSummable wave -
        wholeStateVorticityViscousNegativeOneState
          ν right rightGradientSummable wave =
      wholeStateVorticityViscousNegativeOneState
        ν (left - right)
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) wave
  simp only [
    wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient]
  change
    (ν * Real.sqrt (integerWaveViscousMultiplier wave)) • left wave -
        (ν * Real.sqrt (integerWaveViscousMultiplier wave)) • right wave =
      (ν * Real.sqrt (integerWaveViscousMultiplier wave)) •
        (left wave - right wave)
  exact (smul_sub _ _ _).symm

private theorem wholeMildNonlinearNegativeOneState_sub
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          left leftTransverse leftGradientSummable -
        ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          right rightTransverse rightGradientSummable =
      wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) := by
  apply lp.ext
  funext wave
  change
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          left leftTransverse leftGradientSummable wave -
        ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
          right rightTransverse rightGradientSummable wave =
      wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) wave
  simp only [
    ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState_apply,
    wholeStateVorticityNonlinearDifferenceNegativeOneState_apply]
  by_cases waveZero : wave = 0
  · simp [
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient,
      waveZero]
  · simp only [
      ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient,
      if_neg waveZero]
    rw [smul_sub]

private theorem wholeMildWeightedCoordinateInnerSum_viscous_eq
    (ν : ℝ)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (vector : ComplexCoordinateVector) :
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave * vector coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave) : ℝ) : ℂ) *
          vector coordinate)).re) =
      ν * complexCoordinateAmplitudeSq vector := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave :=
    integerWaveViscousMultiplier_pos ⟨wave, waveNe⟩
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave) :=
    Real.sqrt_pos.2 multiplierPos
  have weighted :=
    weightedCoordinateInnerSum_eq_realInner_div
      wave waveNe vector
        ((ν * integerWaveViscousMultiplier wave) • vector)
  calc
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave * vector coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave) : ℝ) : ℂ) *
          vector coordinate)).re) =
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticFourierWeight wave * vector coordinate)
            (((Real.sqrt
                (integerWaveViscousMultiplier wave))⁻¹ : ℝ) *
              ((ν * integerWaveViscousMultiplier wave) •
                vector) coordinate)).re := by
      apply Finset.sum_congr rfl
      intro coordinate coordinateMem
      congr 2
      simp only [Pi.smul_apply, Complex.real_smul]
      rw [Complex.ofReal_mul, Complex.ofReal_mul,
        Complex.ofReal_inv]
      rw [show
          (integerWaveViscousMultiplier wave : ℂ) =
            (Real.sqrt
                (integerWaveViscousMultiplier wave) : ℂ) *
              Real.sqrt
                (integerWaveViscousMultiplier wave) by
        exact_mod_cast
          (Real.mul_self_sqrt multiplierPos.le).symm]
      field_simp [sqrtPos.ne']
    _ =
        complexCoordinateRealInner vector
            ((ν * integerWaveViscousMultiplier wave) • vector) /
          integerWaveViscousMultiplier wave :=
      weighted
    _ = ν * complexCoordinateAmplitudeSq vector := by
      rw [complexCoordinateRealInner_real_smul_right,
        complexCoordinateRealInner_self,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      field_simp [ne_of_gt multiplierPos]

private theorem wholeMildViscousDifferenceKineticPairing_eq
    (ν : ℝ)
    (left right : ComplexVorticityHilbertState)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate (left - right))
        (wholeCoordinateSliceCLM coordinate
          (wholeStateVorticityViscousNegativeOneState
                ν left leftGradientSummable -
            wholeStateVorticityViscousNegativeOneState
                ν right rightGradientSummable))).re) =
      ν * puncturedWholeVorticityEuclideanMass (left - right) := by
  rw [wholeMildViscousNegativeOneState_sub
    ν left right leftGradientSummable rightGradientSummable]
  let difference := left - right
  let differenceGradientSummable :=
    summable_wholeStateVorticityGradientDensity_sub
      left right leftGradientSummable rightGradientSummable
  let viscousState :=
    wholeStateVorticityViscousNegativeOneState
      ν difference differenceGradientSummable
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate difference)
        (wholeCoordinateSliceCLM coordinate viscousState)).re) =
      ν * puncturedWholeVorticityEuclideanMass difference
  simp_rw [lp.inner_eq_tsum]
  have innerSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave) :=
    fun coordinate =>
      (lp.hasSum_inner
        (wholeKineticCoordinateSliceCLM coordinate difference)
        (wholeCoordinateSliceCLM coordinate viscousState)).summable
  simp_rw [Complex.re_tsum (innerSummable _)]
  have reSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave)).re := by
    intro coordinate
    simpa [Function.comp_def] using
      (innerSummable coordinate).map
        Complex.reCLM Complex.continuous_re
  rw [← Summable.tsum_finsetSum
    (fun coordinate _ => reSummable coordinate)]
  have fullSummable :
      Summable fun wave : IntegerWavevector =>
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave)).re := by
    exact summable_sum (s := Finset.univ) fun coordinate _ =>
      reSummable coordinate
  have complementZero :
      (∑' wave :
          ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
            Set IntegerWavevector),
        ∑ coordinate : Coordinate,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate difference wave.1)
            (wholeCoordinateSliceCLM
              coordinate viscousState wave.1)).re) = 0 := by
    rw [show
        (fun wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector) =>
          ∑ coordinate : Coordinate,
            (inner ℂ
              (wholeKineticCoordinateSliceCLM
                coordinate difference wave.1)
              (wholeCoordinateSliceCLM
                coordinate viscousState wave.1)).re) =
          0 by
      funext wave
      have waveZero : wave.1 = 0 := by simpa using wave.2
      simp [wholeKineticCoordinateSliceCLM_apply,
        wholeKineticFourierWeight, waveZero]]
    exact tsum_zero
  have split :=
    fullSummable.tsum_subtype_add_tsum_subtype_compl
      { wave : IntegerWavevector | wave ≠ 0 }
  rw [← split, complementZero, add_zero]
  unfold puncturedWholeVorticityEuclideanMass
  rw [← tsum_mul_left]
  apply tsum_congr
  intro wave
  simp only [wholeKineticCoordinateSliceCLM_apply,
    wholeCoordinateSliceCLM_apply]
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave.1 *
          difference wave.1 coordinate)
        (((ν * Real.sqrt
            (integerWaveViscousMultiplier wave.1) : ℝ) : ℂ) *
          difference wave.1 coordinate)).re) =
      ν * complexCoordinateAmplitudeSq (difference wave.1)
  exact wholeMildWeightedCoordinateInnerSum_viscous_eq
    ν wave.1 wave.2 (difference wave.1)

private theorem wholeMildNonlinearDifferenceNegativeOneState_zero_row
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    wholeStateVorticityNonlinearDifferenceNegativeOneState
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) 0 = 0 := by
  simp [wholeStateVorticityNonlinearDifferenceNegativeOneState_apply,
    wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient]

private theorem wholeMildViscousNegativeOneState_zero_row
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVorticityViscousNegativeOneState
        ν state gradientSummable 0 = 0 := by
  simp [wholeStateVorticityViscousNegativeOneState_apply,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient,
    integerWaveViscousMultiplier, integerWaveNormSq]

private theorem wholeMildScalarLp_real_inner_eq_re_inner
    (left right : lp (fun _ : IntegerWavevector => ℂ) 2) :
    ⟪left, right⟫_ℝ = (inner ℂ left right).re := by
  have innerSummable :
      Summable fun wave : IntegerWavevector =>
        inner ℂ (left wave) (right wave) :=
    (lp.hasSum_inner left right).summable
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    Complex.re_tsum innerSummable]
  apply tsum_congr
  intro wave
  rfl

/-- Complete kinetic power of the actual whole tangent difference. -/
def actualWholeDifferenceKineticPower
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right : WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ℝ → ℝ :=
  fun time =>
    ∑ coordinate : Coordinate,
      2 * inner ℝ
        (actualWholeDifferenceKineticCoordinateIntegralPath
          coordinate left right time)
        (actualWholeDifferenceKineticCoordinateTangent
          coordinate left right time)

/--
The actual unforced row laws pay the complete kinetic power.  The coefficient
is generated from the left whole path and the fixed viscosity; the theorem
has no external energy-payment or absorption premise.
-/
theorem actualWholeDifferenceKineticPower_ae_le
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      actualWholeDifferenceKineticPower left right time.1 ≤
        actualWholeDifferenceSerrinCoefficient left time.1 *
          actualWholeDifferenceKineticMass left right time.1 := by
  let wholeTangent := actualWholeDifferenceTangent left right
  have coordinateProjectionAE :
      ∀ coordinate : Coordinate,
        ∀ᵐ time ∂(commonTimeMeasure requestedTime),
          actualWholeDifferenceKineticCoordinateTangentLp
              coordinate left right time =
            wholePuncturedCoordinateSliceCLM coordinate
              (wholeTangent time) :=
    fun coordinate =>
      (wholePuncturedCoordinateSliceCLM coordinate).coeFn_compLpL
        wholeTangent
  have leftStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        left.stateLimit time = (left.transverseLimit time).1 := by
    filter_upwards [
      transverseSpaceTimeInclusion_coeFn
        requestedTime left.transverseLimit] with time inclusionEq
    calc
      left.stateLimit time =
          (transverseSpaceTimeInclusion
            requestedTime left.transverseLimit) time := by
        rw [left.stateLimit_eq_transverse]
      _ = (left.transverseLimit time).1 := inclusionEq
  have rightStateAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        right.stateLimit time = (right.transverseLimit time).1 := by
    filter_upwards [
      transverseSpaceTimeInclusion_coeFn
        requestedTime right.transverseLimit] with time inclusionEq
    calc
      right.stateLimit time =
          (transverseSpaceTimeInclusion
            requestedTime right.transverseLimit) time := by
        rw [right.stateLimit_eq_transverse]
      _ = (right.transverseLimit time).1 := inclusionEq
  have leftTransverseGradientCarrier :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion
            requestedTime left.transverseLimit) wave := by
    rw [left.stateLimit_eq_transverse]
    exact left.gradient_summable
  have rightTransverseGradientCarrier :
      Summable fun wave : IntegerWavevector =>
        wholeSpaceTimeVorticityGradientDensity requestedTime
          (transverseSpaceTimeInclusion
            requestedTime right.transverseLimit) wave := by
    rw [right.stateLimit_eq_transverse]
    exact right.gradient_summable
  have leftZeroRowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        (left.transverseLimit time).1 0 = 0 := by
    filter_upwards [left.wholePath_eq_transverse_ae] with time pathEq
    rw [← pathEq]
    exact left.wholePath_zero_row time
  have rightZeroRowAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        (right.transverseLimit time).1 0 = 0 := by
    filter_upwards [right.wholePath_eq_transverse_ae] with time pathEq
    rw [← pathEq]
    exact right.wholePath_zero_row time
  have coefficientAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        actualWholeDifferenceSerrinCoefficient left time.1 =
          ν.coeff⁻¹ *
            wholeStateVelocityMajorant
              ((left.transverseLimit time).1) ^ 2 := by
    filter_upwards [leftStateAE] with time stateEq
    rw [actualWholeDifferenceSerrinCoefficient,
      commonTimeZeroExtension_of_mem
        requestedTime _ time.1 time.property]
    change
      ν.coeff⁻¹ *
          wholeStateVelocityMajorant
            ((BoundedContinuousFunction.toLp 2
              (commonTimeMeasure requestedTime) ℂ left.wholePath) time) ^ 2 =
        _
    rw [left.wholePath_toLp_eq_stateLimit, stateEq]
  have kineticMassAE :
      ∀ᵐ time ∂(commonTimeMeasure requestedTime),
        actualWholeDifferenceKineticMass left right time.1 =
          puncturedWholeVorticityKineticMass
            ((left.transverseLimit time).1 -
              (right.transverseLimit time).1) := by
    filter_upwards [
      left.wholePath_eq_transverse_ae,
      right.wholePath_eq_transverse_ae] with
        time leftPathEq rightPathEq
    rw [actualWholeDifferenceKineticMass_of_mem
      left right time.1 time.property, leftPathEq, rightPathEq]
  filter_upwards [
    eventually_countable_forall.2 coordinateProjectionAE,
    actualWholeDifferenceTangent_eq_unforced_ae left right,
    left.wholePath_eq_transverse_ae,
    right.wholePath_eq_transverse_ae,
    wholePointwiseGradientDensity_ae_summable
      requestedTime left.stateLimit left.gradient_summable,
    wholePointwiseGradientDensity_ae_summable
      requestedTime right.stateLimit right.gradient_summable,
    transversePointwiseGradient_ae_summable
      left.transverseLimit leftTransverseGradientCarrier,
    transversePointwiseGradient_ae_summable
      right.transverseLimit rightTransverseGradientCarrier,
    leftZeroRowAE, rightZeroRowAE,
    left.transverse_fourierReality_ae,
    right.transverse_fourierReality_ae,
    coefficientAE, kineticMassAE,
    leftStateAE, rightStateAE] with
      time coordinateProjection tangentFunctionEq
      leftPathEq rightPathEq
      leftStateGradient rightStateGradient
      leftGradient rightGradient
      leftZeroRow rightZeroRow
      leftReality rightReality
      coefficientEq kineticMassEq
      leftStateEq rightStateEq
  let leftState := (left.transverseLimit time).1
  let rightState := (right.transverseLimit time).1
  let difference := leftState - rightState
  have leftTransverse : WholeStateTransverse leftState := by
    have membership := (left.transverseLimit time).2
    change WholeStateTransverse
      ((left.transverseLimit time).1 : ComplexVorticityHilbertState) at membership
    exact membership
  have rightTransverse : WholeStateTransverse rightState := by
    have membership := (right.transverseLimit time).2
    change WholeStateTransverse
      ((right.transverseLimit time).1 : ComplexVorticityHilbertState) at membership
    exact membership
  let differenceGradient :=
    summable_wholeStateVorticityGradientDensity_sub
      leftState rightState leftGradient rightGradient
  let nonlinearDifference :=
    wholeStateVorticityNonlinearDifferenceNegativeOneState
      leftState rightState
      leftTransverse rightTransverse
      leftGradient rightGradient differenceGradient
  let viscousDifference :=
    wholeStateVorticityViscousNegativeOneState
      ν.coeff difference differenceGradient
  have tangentPointwise :
      wholeTangent time =
        nonlinearDifference - viscousDifference := by
    rw [tangentFunctionEq,
      wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
        left.transverseLimit time leftGradient,
      wholeSpaceTimeNonlinearNegativeOneFunction_of_summable
        right.transverseLimit time rightGradient,
      wholeSpaceTimeViscousNegativeOneFunction_of_summable
        ν.coeff left.stateLimit time leftStateGradient,
      wholeSpaceTimeViscousNegativeOneFunction_of_summable
        ν.coeff right.stateLimit time rightStateGradient]
    simp only [leftStateEq, rightStateEq]
    change
      (ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
            leftState leftTransverse leftGradient -
          ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev.wholeStateVorticityNonlinearNegativeOneState
            rightState rightTransverse rightGradient) -
        (wholeStateVorticityViscousNegativeOneState
            ν.coeff leftState leftGradient -
          wholeStateVorticityViscousNegativeOneState
            ν.coeff rightState rightGradient) =
          nonlinearDifference - viscousDifference
    rw [wholeMildNonlinearNegativeOneState_sub
          leftState rightState leftTransverse rightTransverse
            leftGradient rightGradient,
      wholeMildViscousNegativeOneState_sub
        ν.coeff leftState rightState leftGradient rightGradient]
  have nonlinearZero :
      nonlinearDifference 0 = 0 := by
    exact
      wholeMildNonlinearDifferenceNegativeOneState_zero_row
        leftState rightState
        leftTransverse rightTransverse
        leftGradient rightGradient
  have viscousZero :
      viscousDifference 0 = 0 := by
    exact
      wholeMildViscousNegativeOneState_zero_row
        ν.coeff difference differenceGradient
  have pathCoordinateEq :
      ∀ coordinate : Coordinate,
        actualWholeDifferenceKineticCoordinateIntegralPath
            coordinate left right time.1 =
          wholeKineticCoordinateSliceCLM
            coordinate difference := by
    intro coordinate
    rw [actualWholeDifferenceKineticCoordinateIntegralPath_eq
      coordinate left right time, leftPathEq, rightPathEq]
  have tangentCoordinateEq :
      ∀ coordinate : Coordinate,
        actualWholeDifferenceKineticCoordinateTangent
            coordinate left right time.1 =
          wholeCoordinateSliceCLM coordinate nonlinearDifference -
            wholeCoordinateSliceCLM coordinate viscousDifference := by
    intro coordinate
    rw [actualWholeDifferenceKineticCoordinateTangent,
      commonTimeZeroExtension_of_mem
        requestedTime _ time.1 time.property,
      coordinateProjection coordinate,
      tangentPointwise, map_sub,
      wholeMildPuncturedCoordinateSlice_eq_coordinateSlice_of_zero_row
        coordinate nonlinearDifference nonlinearZero,
      wholeMildPuncturedCoordinateSlice_eq_coordinateSlice_of_zero_row
        coordinate viscousDifference viscousZero]
  have nonlinearPairingEq :
      (∑ coordinate : Coordinate,
        ⟪wholeKineticCoordinateSliceCLM coordinate difference,
          wholeCoordinateSliceCLM coordinate nonlinearDifference⟫_ℝ) =
        wholeStateVorticityNonlinearDifferenceKineticPairing
          leftState rightState
          leftTransverse rightTransverse
          leftGradient rightGradient differenceGradient := by
    unfold wholeStateVorticityNonlinearDifferenceKineticPairing
    simp_rw [wholeMildScalarLp_real_inner_eq_re_inner]
    rfl
  have viscousPairingEq :
      (∑ coordinate : Coordinate,
        ⟪wholeKineticCoordinateSliceCLM coordinate difference,
          wholeCoordinateSliceCLM coordinate viscousDifference⟫_ℝ) =
        ν.coeff *
          puncturedWholeVorticityEuclideanMass difference := by
    have viscousDifferenceEq :
        viscousDifference =
          wholeStateVorticityViscousNegativeOneState
              ν.coeff leftState leftGradient -
            wholeStateVorticityViscousNegativeOneState
              ν.coeff rightState rightGradient := by
      exact
        (wholeMildViscousNegativeOneState_sub
          ν.coeff leftState rightState
          leftGradient rightGradient).symm
    rw [viscousDifferenceEq]
    simp_rw [wholeMildScalarLp_real_inner_eq_re_inner]
    simpa only [difference] using
      wholeMildViscousDifferenceKineticPairing_eq
        ν.coeff leftState rightState leftGradient rightGradient
  have powerEq :
      actualWholeDifferenceKineticPower left right time.1 =
        2 *
            wholeStateVorticityNonlinearDifferenceKineticPairing
              leftState rightState
              leftTransverse rightTransverse
              leftGradient rightGradient differenceGradient -
          2 * ν.coeff *
            puncturedWholeVorticityEuclideanMass difference := by
    unfold actualWholeDifferenceKineticPower
    simp_rw [pathCoordinateEq, tangentCoordinateEq, inner_sub_right]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      nonlinearPairingEq, viscousPairingEq]
    ring
  have young :=
    wholeStateVorticityNonlinearDifferenceKineticPairing_le_young
      leftState rightState leftZeroRow rightZeroRow
      leftTransverse rightTransverse
      leftReality rightReality leftGradient rightGradient
      ν.coeff ν.coeff_pos
  have euclideanNonneg :
      0 ≤ puncturedWholeVorticityEuclideanMass difference := by
    unfold puncturedWholeVorticityEuclideanMass
    exact tsum_nonneg fun wave =>
      complexCoordinateAmplitudeSq_nonneg _
  rw [powerEq, coefficientEq, kineticMassEq]
  dsimp [leftState, rightState, difference] at young ⊢
  nlinarith [mul_nonneg ν.coeff_pos.le euclideanNonneg]

/--
Exact kinetic energy transport for one coordinate of the complete
nonzero-frequency carrier.
-/
theorem actualWholeDifferenceKineticCoordinate_energy_identity
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime) :
    (∫ time in (0 : ℝ)..terminal.1,
        2 * ⟪
          actualWholeDifferenceKineticCoordinateIntegralPath
            coordinate left right time,
          actualWholeDifferenceKineticCoordinateTangent
            coordinate left right time⟫_ℝ) =
      ‖wholeKineticCoordinateSliceCLM coordinate
          (left.wholePath terminal - right.wholePath terminal)‖ ^ 2 := by
  have tangentIntegrableAt :
      IntervalIntegrable
        (actualWholeDifferenceKineticCoordinateTangent
          coordinate left right)
        volume 0 terminal.1 :=
    (actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right).mono_set <| by
        rw [uIcc_of_le terminal.property.1,
          uIcc_of_le left.requestedTimePos.le]
        exact Icc_subset_Icc le_rfl terminal.property.2
  have pathAC :
      AbsolutelyContinuousOnInterval
        (actualWholeDifferenceKineticCoordinateIntegralPath
          coordinate left right)
        0 terminal.1 := by
    exact
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
        tangentIntegrableAt
        (by
          rw [uIcc_of_le terminal.property.1]
          exact ⟨le_rfl, terminal.property.1⟩)
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) terminal.1 →
          HasDerivAt
            (actualWholeDifferenceKineticCoordinateIntegralPath
              coordinate left right)
            (actualWholeDifferenceKineticCoordinateTangent
              coordinate left right time)
            time := by
    filter_upwards [
      tangentIntegrableAt.ae_hasDerivAt_integral] with
        time integralDerivative
    intro timeMem
    exact integralDerivative timeMem 0 (by simp)
  have energyIdentity :=
    ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall.AbsolutelyContinuousOnInterval.norm_sq_energy_identity
      pathAC pathDerivative
  have initialPath :
      actualWholeDifferenceKineticCoordinateIntegralPath
          coordinate left right 0 = 0 := by
    simp [actualWholeDifferenceKineticCoordinateIntegralPath]
  rw [actualWholeDifferenceKineticCoordinateIntegralPath_eq
      coordinate left right terminal,
    initialPath, norm_zero] at energyIdentity
  norm_num at energyIdentity
  simpa only [intervalIntegral.integral_const_mul, map_sub] using
    energyIdentity

private theorem
    actualWholeDifferenceKineticCoordinatePower_intervalIntegrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (coordinate : Coordinate)
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    IntervalIntegrable
      (fun time =>
        2 * ⟪
          actualWholeDifferenceKineticCoordinateIntegralPath
            coordinate left right time,
          actualWholeDifferenceKineticCoordinateTangent
            coordinate left right time⟫_ℝ)
      volume 0 requestedTime := by
  have tangentIntegrable :=
    actualWholeDifferenceKineticCoordinateTangent_intervalIntegrable
      coordinate left right
  have pathAC :
      AbsolutelyContinuousOnInterval
        (actualWholeDifferenceKineticCoordinateIntegralPath
          coordinate left right)
        0 requestedTime := by
    exact
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
        tangentIntegrable
        (by
          rw [uIcc_of_le left.requestedTimePos.le]
          exact ⟨le_rfl, left.requestedTimePos.le⟩)
  have pathDerivative :
      ∀ᵐ time : ℝ,
        time ∈ uIcc (0 : ℝ) requestedTime →
          HasDerivAt
            (actualWholeDifferenceKineticCoordinateIntegralPath
              coordinate left right)
            (actualWholeDifferenceKineticCoordinateTangent
              coordinate left right time)
            time := by
    filter_upwards [
      tangentIntegrable.ae_hasDerivAt_integral] with
        time integralDerivative
    intro timeMem
    exact integralDerivative timeMem 0 (by simp)
  have energyAC :
      AbsolutelyContinuousOnInterval
        (fun time =>
          ‖actualWholeDifferenceKineticCoordinateIntegralPath
            coordinate left right time‖ ^ 2)
        0 requestedTime := by
    simpa only [real_inner_self_eq_norm_sq] using
      ThreeDimensionalVorticityCoefficientStrongContinuationKineticDifferenceGronwall.absolutelyContinuousOnInterval_real_inner
        pathAC pathAC
  apply energyAC.intervalIntegrable_deriv.congr_ae
  filter_upwards [
    ae_restrict_mem measurableSet_uIoc,
    ae_mono Measure.restrict_le_self pathDerivative] with
      time timeMem derivative
  exact
    ((derivative (uIoc_subset_uIcc timeMem)).norm_sq).deriv

theorem actualWholeDifferenceKineticPower_intervalIntegrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    IntervalIntegrable
      (actualWholeDifferenceKineticPower left right)
      volume 0 requestedTime := by
  unfold actualWholeDifferenceKineticPower
  exact IntervalIntegrable.sum Finset.univ fun coordinate _ =>
    actualWholeDifferenceKineticCoordinatePower_intervalIntegrable
      coordinate left right

private theorem
    actualWholeDifferenceCoefficientMulKineticMass_intervalIntegrable
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    IntervalIntegrable
      (fun time =>
        actualWholeDifferenceSerrinCoefficient left time *
          actualWholeDifferenceKineticMass left right time)
      volume 0 requestedTime :=
  (actualWholeDifferenceSerrinCoefficient_intervalIntegrable left)
    |>.mul_continuousOn
      (by
        rw [uIcc_of_le left.requestedTimePos.le]
        exact actualWholeDifferenceKineticMass_continuousOn left right)

theorem actualWholeDifferenceKineticMass_eq_integral_power
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime) :
    actualWholeDifferenceKineticMass left right terminal.1 =
      ∫ time in (0 : ℝ)..terminal.1,
        actualWholeDifferenceKineticPower left right time := by
  rw [actualWholeDifferenceKineticMass_of_mem
      left right terminal.1 terminal.property,
    puncturedWholeVorticityKineticMass_eq_coordinateSlices]
  simp only [actualWholeDifferenceKineticPower]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro coordinate coordinateMem
    exact
      (actualWholeDifferenceKineticCoordinate_energy_identity
        coordinate left right terminal).symm
  · intro coordinate coordinateMem
    exact
      (actualWholeDifferenceKineticCoordinatePower_intervalIntegrable
        coordinate left right).mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le left.requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2

private theorem wholeMildCommonTimeMeasure_eq_comap_volume
    (requestedTime : ℝ) :
    commonTimeMeasure requestedTime =
      Measure.comap
        (Subtype.val : Icc (0 : ℝ) requestedTime → ℝ)
        volume := by
  unfold commonTimeMeasure
  rw [MeasurableEmbedding.comap_restrict
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)]
  simp

private theorem
    actualWholeDifferenceKineticPower_ae_le_volume_restrict
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ᵐ time ∂volume.restrict (Icc (0 : ℝ) requestedTime),
      actualWholeDifferenceKineticPower left right time ≤
        actualWholeDifferenceSerrinCoefficient left time *
          actualWholeDifferenceKineticMass left right time := by
  apply (ae_restrict_iff_subtype measurableSet_Icc).2
  have inequality :=
    actualWholeDifferenceKineticPower_ae_le left right
  rw [wholeMildCommonTimeMeasure_eq_comap_volume] at inequality
  exact inequality

theorem actualWholeDifferenceKineticMass_le_integral
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime)
    (terminal : Icc (0 : ℝ) requestedTime) :
    actualWholeDifferenceKineticMass left right terminal.1 ≤
      ∫ time in (0 : ℝ)..terminal.1,
        actualWholeDifferenceSerrinCoefficient left time *
          actualWholeDifferenceKineticMass left right time := by
  rw [actualWholeDifferenceKineticMass_eq_integral_power
    left right terminal]
  apply intervalIntegral.integral_mono_ae_restrict terminal.property.1
  · exact
      (actualWholeDifferenceKineticPower_intervalIntegrable left right)
        |>.mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le left.requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2
  · exact
      (actualWholeDifferenceCoefficientMulKineticMass_intervalIntegrable
        left right)
        |>.mono_set <| by
          rw [uIcc_of_le terminal.property.1,
            uIcc_of_le left.requestedTimePos.le]
          exact Icc_subset_Icc le_rfl terminal.property.2
  · exact ae_mono
      (Measure.restrict_mono
        (Icc_subset_Icc le_rfl terminal.property.2) le_rfl)
      (actualWholeDifferenceKineticPower_ae_le_volume_restrict
        left right)

theorem actualWholeDifferenceKineticMass_eq_zero
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    ∀ time ∈ Icc (0 : ℝ) requestedTime,
      actualWholeDifferenceKineticMass left right time = 0 := by
  obtain ⟨bound, boundUpper⟩ :=
    actualWholeDifferenceKineticMass_bounded left right
  apply eq_zero_of_nonneg_le_integral_mul
    left.requestedTimePos.le
    (actualWholeDifferenceSerrinCoefficient_intervalIntegrable left)
    (actualWholeDifferenceSerrinCoefficient_nonneg left)
    (actualWholeDifferenceKineticMass_continuousOn left right)
    (actualWholeDifferenceKineticMass_nonneg left right)
    boundUpper
  intro time timeMem
  exact
    actualWholeDifferenceKineticMass_le_integral
      left right ⟨time, timeMem⟩

/--
Two complete unforced mild/Serrin receipts with the same dependent initial
state carry exactly the same whole path.  The proof consumes only their
actual row update laws, Fourier reality, and generated whole gradient budget.
-/
theorem wholeContinuousMildSerrin_sameInitial_unique
    {ν : Viscosity} {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (left right :
      WholeContinuousMildSerrinReceipt ν initialState requestedTime) :
    left.wholePath = right.wholePath := by
  apply DFunLike.ext _ _
  intro time
  have massZero :=
    actualWholeDifferenceKineticMass_eq_zero
      left right time.1 time.property
  rw [actualWholeDifferenceKineticMass_of_mem
    left right time.1 time.property] at massZero
  have differenceZeroRow :
      (left.wholePath time - right.wholePath time) 0 = 0 := by
    rw [lp.coeFn_sub, Pi.sub_apply,
      left.wholePath_zero_row time,
      right.wholePath_zero_row time,
      sub_zero]
  have differenceZero :
      left.wholePath time - right.wholePath time = 0 :=
    (puncturedWholeVorticityKineticMass_eq_zero_iff_of_zero_row
      (left.wholePath time - right.wholePath time)
      differenceZeroRow).1 massZero
  exact sub_eq_zero.mp differenceZero

end

end ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
end NavierStokes
end SaturationMonoid
