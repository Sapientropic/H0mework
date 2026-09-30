import H0mework.NavierStokes.Restart.CumulativeCriticalDissipation
import H0mework.NavierStokes.KineticRestart.CumulativeKineticDissipation
import H0mework.NavierStokes.Crossing.FiniteCore
import H0mework.NavierStokes.Restart.FinitePrefixDualSquareLedger

/-!
# Physical mass persistence at an actual restart crossing

An actual half-critical crossing selects a finite set of nonzero Fourier
rows whose physical vorticity mass exceeds a fixed viscosity-generated
quantum.  The quantitative finite-observation law retained by the final
whole mild path then gives a source-owned positive lifetime on which at
least one quarter of that quantum remains visible.

The carrier, lifetime, and lower bound are all generated from the same
native restart current.  No cutoff, modulus, time window, branch, target
path, or payment certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence

open scoped BigOperators Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedWaveWeakCarrier
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFiniteObservedCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness

noncomputable section

/-! ## Continuous receipt payment identity -/

/-- The abstract prefix payment of any actual whole receipt is the ordinary
physical-time integral of its continuous whole path. -/
theorem wholePrefixVorticityMass_receipt_eq_intervalIntegral
    {ν : Viscosity}
    {initialState : ComplexVorticityHilbertState}
    {requestedTime : ℝ}
    (receipt :
      WholeContinuousMildSerrinReceipt
        ν initialState requestedTime)
    (time : Icc (0 : ℝ) requestedTime) :
    wholePrefixVorticityMass time receipt.stateLimit =
      ∫ actual in (0 : ℝ)..time.1,
        wholeVorticityEuclideanMass
          (wholeRestartReceiptPhysicalTrajectory receipt actual) := by
  let trajectory : ℝ → ComplexVorticityHilbertState :=
    wholeRestartReceiptPhysicalTrajectory receipt
  have trajectoryContinuous : Continuous trajectory := by
    exact wholeRestartReceiptPhysicalTrajectory_continuous receipt
  have stateLimitEq :
      receipt.stateLimit =
        wholeTrajectorySpaceTimePath requestedTime trajectory
          trajectoryContinuous.continuousOn := by
    rw [← receipt.wholePath_toLp_eq_stateLimit]
    unfold wholeTrajectorySpaceTimePath
    congr 1
    apply BoundedContinuousFunction.ext
    intro actual
    change
      receipt.wholePath actual =
        wholeRestartReceiptPhysicalTrajectory receipt actual.1
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem receipt.requestedTimePos.le actual.2]
  rw [stateLimitEq,
    wholePrefixVorticityMass_wholeTrajectorySpaceTimePath_eq_intervalIntegral]

/-! ## Fixed crossing quantum on the source-native finite core -/

/-- The coefficient-mass quantum forced by the fixed half-critical crossing
threshold. -/
def wholeRestartCrossingMassQuantum (ν : Viscosity) : ℝ :=
  ((1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) /
    criticalEnstrophyLatticeConstant

theorem wholeRestartCrossingMassQuantum_pos (ν : Viscosity) :
    0 < wholeRestartCrossingMassQuantum ν := by
  unfold wholeRestartCrossingMassQuantum
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) (sq_pos_of_pos ν.coeff_pos))
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)))
    criticalEnstrophyLatticeConstant_pos

theorem wholeRestartCrossingMassQuantum_lt_wholeMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassQuantum ν <
      wholeVorticityEuclideanMass
        (run initial index).contact.physicalState := by
  unfold wholeRestartCrossingMassQuantum
  apply
    (div_lt_iff₀ criticalEnstrophyLatticeConstant_pos).2
  unfold wholeRestartHalfCriticalCrossed at crossed
  simpa only [mul_comm] using crossed

/-- The already-generated least canonical crossing core exceeds the fixed
coefficient-mass quantum.  No arbitrary finite inventory is selected here. -/
theorem wholeRestartCrossingMassQuantum_lt_finiteCoreMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassQuantum ν <
      finiteStateVorticityCoefficientEnstrophy
        (wholeRestartCrossingFiniteCoreModes initial index crossed)
        (run initial index).contact.physicalState :=
  (div_lt_iff₀ criticalEnstrophyLatticeConstant_pos).2 (by
    simpa only [wholeRestartCrossingMassQuantum, mul_comm] using
      wholeRestartCrossingFiniteCoreRadius_crossed
        initial index crossed)

private theorem zero_not_mem_wholeRestartCrossingFiniteCoreModes
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (0 : IntegerWavevector) ∉
      wholeRestartCrossingFiniteCoreModes initial index crossed := by
  simpa only [wholeRestartCrossingFiniteCoreModes, wholeRestartModes] using
    zero_not_mem_puncturedIntegerWaveFrequencyCube
      (wholeRestartCrossingFiniteCoreRadius initial index crossed)

/-! ## Quantitative persistence on the actual whole receipt -/

/-- Sum of the already-generated rowwise square-increment constants on the
crossing-selected physical carrier. -/
def wholeRestartCrossingMassHolderBudget
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℝ :=
  ∑ wave ∈ wholeRestartCrossingFiniteCoreModes initial index crossed,
    wholeRestartFiniteObservedHalfHolderEnergy
      (generatedWholeRestartCanonicalReplay
        (run initial index).contact) {wave}

theorem wholeRestartCrossingMassHolderBudget_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 ≤ wholeRestartCrossingMassHolderBudget initial index crossed := by
  unfold wholeRestartCrossingMassHolderBudget
  exact Finset.sum_nonneg fun wave _waveMem =>
    wholeRestartFiniteObservedHalfHolderEnergy_nonneg
      (generatedWholeRestartCanonicalReplay
        (run initial index).contact) {wave}

/-- The retained modulus budget is exactly the viscous multiplier mass of
the source-generated least frequency cube times the actual whole-carrier
negative-one ceiling.  Thus its growth has no hidden cutoff parameter. -/
theorem wholeRestartCrossingMassHolderBudget_eq_nativeMultiplierMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassHolderBudget initial index crossed =
      finiteObservedMultiplierMass
          (wholeRestartCrossingFiniteCoreModes initial index crossed) *
        wholeRestartNegativeOneCeiling (run initial index).contact := by
  unfold wholeRestartCrossingMassHolderBudget
    wholeRestartFiniteObservedHalfHolderEnergy
    finiteObservedMultiplierMass
  simp only [Finset.sum_singleton]
  rw [Finset.sum_mul]

/-- Physical finite-carrier displacement from the exact restart state. -/
def wholeRestartCrossingMassDifference
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (time : Icc (0 : ℝ)
      (wholeRestartDuration (run initial index).contact)) : ℝ :=
  finiteStateVorticityCoefficientEnstrophy
    (wholeRestartCrossingFiniteCoreModes initial index crossed)
    ((run initial index).nextReceipt.wholePath time -
      (run initial index).contact.physicalState)

theorem wholeRestartCrossingMassDifference_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (time : Icc (0 : ℝ)
      (wholeRestartDuration (run initial index).contact)) :
    wholeRestartCrossingMassDifference initial index crossed time ≤
      3 * time.1 *
        wholeRestartCrossingMassHolderBudget initial index crossed := by
  let current := run initial index
  let replay := generatedWholeRestartCanonicalReplay current.contact
  let modes :=
    wholeRestartCrossingFiniteCoreModes initial index crossed
  let zeroTime : Icc (0 : ℝ) (wholeRestartDuration current.contact) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
  have zeroPath :
      current.nextReceipt.wholePath zeroTime =
        current.contact.physicalState := by
    exact current.nextReceipt_initial
  have distanceEq : dist time zeroTime = time.1 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    simp only [zeroTime, sub_zero, abs_of_nonneg time.2.1]
  unfold wholeRestartCrossingMassDifference
    finiteStateVorticityCoefficientEnstrophy
    wholeRestartCrossingMassHolderBudget
  change
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          ((current.nextReceipt.wholePath time -
            current.contact.physicalState) wave)) ≤
      3 * time.1 *
        ∑ wave ∈ modes,
          wholeRestartFiniteObservedHalfHolderEnergy replay {wave}
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq
          ((current.nextReceipt.wholePath time -
            current.contact.physicalState) wave)) ≤
        ∑ wave ∈ modes,
          3 * time.1 *
            wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
      apply Finset.sum_le_sum
      intro wave waveMem
      have waveNe : wave ≠ 0 := by
        intro waveZero
        subst wave
        exact
          (zero_not_mem_wholeRestartCrossingFiniteCoreModes
            initial index crossed) waveMem
      have zeroCoordinate :
          current.nextReceipt.wholePath zeroTime wave =
            current.contact.physicalState wave :=
        congrArg (fun state => state wave) zeroPath
      have holder :=
        generatedWholeRestartWholeContinuousMildSerrinReceipt_fixedWave_increment_sq_le
          replay wave waveNe time zeroTime
      change
        complexCoordinateAmplitudeSq
            (current.nextReceipt.wholePath time wave -
              current.contact.physicalState wave) ≤
          3 * time.1 *
            wholeRestartFiniteObservedHalfHolderEnergy replay {wave}
      rw [← zeroCoordinate]
      calc
        complexCoordinateAmplitudeSq
            (current.nextReceipt.wholePath time wave -
              current.nextReceipt.wholePath zeroTime wave) ≤
            3 *
              ‖current.nextReceipt.wholePath time wave -
                current.nextReceipt.wholePath zeroTime wave‖ ^ 2 :=
          complexCoordinateAmplitudeSq_le_three_mul_norm_sq _
        _ = 3 *
              dist
                (current.nextReceipt.wholePath time wave)
                (current.nextReceipt.wholePath zeroTime wave) ^ 2 := by
          rw [dist_eq_norm]
        _ ≤ 3 *
              (dist time zeroTime *
                wholeRestartFiniteObservedHalfHolderEnergy replay
                  {wave}) :=
          mul_le_mul_of_nonneg_left holder (by norm_num)
        _ = 3 * time.1 *
              wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
          rw [distanceEq]
          ring
    _ = 3 * time.1 *
        ∑ wave ∈ modes,
          wholeRestartFiniteObservedHalfHolderEnergy replay {wave} := by
      rw [Finset.mul_sum]

/-- Canonical physical lifetime forced jointly by the actual selected
contact and the retained finite-observation modulus. -/
def wholeRestartCrossingMassPersistenceTime
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) : ℝ :=
  min
    ((run initial index).nextContact.time.1 / 2)
    (wholeRestartCrossingMassQuantum ν /
      (12 * wholeRestartCrossingMassHolderBudget
        initial index crossed + 1))

theorem wholeRestartCrossingMassPersistenceTime_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 < wholeRestartCrossingMassPersistenceTime
      initial index crossed := by
  unfold wholeRestartCrossingMassPersistenceTime
  apply lt_min
  · exact div_pos (run initial index).nextContact.time_pos (by norm_num)
  · apply div_pos (wholeRestartCrossingMassQuantum_pos ν)
    have budgetNonneg :=
      wholeRestartCrossingMassHolderBudget_nonneg
        initial index crossed
    positivity

theorem wholeRestartCrossingMassPersistenceTime_lt_contact
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassPersistenceTime initial index crossed <
      (run initial index).nextContact.time.1 := by
  have halfLe :
      wholeRestartCrossingMassPersistenceTime initial index crossed ≤
        (run initial index).nextContact.time.1 / 2 :=
    min_le_left _ _
  have contactPos := (run initial index).nextContact.time_pos
  linarith

/-- The canonical persistence interval sits inside the actual whole receipt. -/
noncomputable def wholeRestartCrossingMassPersistencePoint
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    Icc (0 : ℝ) (wholeRestartDuration (run initial index).contact) :=
  ⟨wholeRestartCrossingMassPersistenceTime initial index crossed,
    ⟨(wholeRestartCrossingMassPersistenceTime_pos
      initial index crossed).le,
    (wholeRestartCrossingMassPersistenceTime_lt_contact
      initial index crossed).le.trans
        (run initial index).nextContact.time.2.2⟩⟩

theorem wholeRestartCrossingMassDifference_le_quarterQuantum
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (time : Icc (0 : ℝ)
      (wholeRestartDuration (run initial index).contact))
    (timeLe : time.1 ≤
      wholeRestartCrossingMassPersistenceTime initial index crossed) :
    wholeRestartCrossingMassDifference initial index crossed time ≤
      wholeRestartCrossingMassQuantum ν / 4 := by
  let budget :=
    wholeRestartCrossingMassHolderBudget initial index crossed
  let quantum := wholeRestartCrossingMassQuantum ν
  have budgetNonneg : 0 ≤ budget := by
    simpa only [budget] using
      wholeRestartCrossingMassHolderBudget_nonneg
        initial index crossed
  have denominatorPos : 0 < 12 * budget + 1 := by positivity
  have persistenceLe :
      wholeRestartCrossingMassPersistenceTime initial index crossed ≤
        quantum / (12 * budget + 1) := by
    exact min_le_right _ _
  have timeLeQuotient : time.1 ≤ quantum / (12 * budget + 1) :=
    timeLe.trans persistenceLe
  have scaled : time.1 * (12 * budget + 1) ≤ quantum :=
    (le_div_iff₀ denominatorPos).mp timeLeQuotient
  have differenceLe :=
    wholeRestartCrossingMassDifference_le
      initial index crossed time
  change
    wholeRestartCrossingMassDifference initial index crossed time ≤
      quantum / 4
  change
    wholeRestartCrossingMassDifference initial index crossed time ≤
      3 * time.1 * budget at differenceLe
  have timeNonneg : 0 ≤ time.1 := time.2.1
  nlinarith

private theorem norm_sub_sq_le_two_mul
    {E : Type*}
    [NormedAddCommGroup E]
    (left right : E) :
    ‖left - right‖ ^ 2 ≤
      2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have normLe : ‖left - right‖ ≤ ‖left‖ + ‖right‖ :=
    norm_sub_le left right
  have squareLe :
      ‖left - right‖ ^ 2 ≤ (‖left‖ + ‖right‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 normLe
  nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

private theorem complexCoordinateAmplitudeSq_sub_le_two_mul
    (left right : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (left - right) ≤
      2 * complexCoordinateAmplitudeSq left +
        2 * complexCoordinateAmplitudeSq right := by
  unfold complexCoordinateAmplitudeSq
  calc
    (∑ coordinate : Coordinate,
        Complex.normSq ((left - right) coordinate)) ≤
        ∑ coordinate : Coordinate,
          (2 * Complex.normSq (left coordinate) +
            2 * Complex.normSq (right coordinate)) := by
      apply Finset.sum_le_sum
      intro coordinate _coordinateMem
      simpa only [Pi.sub_apply, Complex.normSq_eq_norm_sq] using
        norm_sub_sq_le_two_mul (left coordinate) (right coordinate)
    _ =
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (left coordinate)) +
        2 * (∑ coordinate : Coordinate,
          Complex.normSq (right coordinate)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem finiteVorticityCoefficientEnstrophy_initial_le
    (modes : Finset IntegerWavevector)
    (initial current : ComplexVorticityHilbertState) :
    finiteStateVorticityCoefficientEnstrophy modes initial ≤
      2 * finiteStateVorticityCoefficientEnstrophy modes current +
        2 * finiteStateVorticityCoefficientEnstrophy
          modes (current - initial) := by
  unfold finiteStateVorticityCoefficientEnstrophy
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (initial wave)) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (current wave -
              (current wave - initial wave)) := by
      apply Finset.sum_congr rfl
      intro wave _waveMem
      rw [sub_sub_cancel]
    _ ≤
        ∑ wave ∈ modes,
          (2 * complexCoordinateAmplitudeSq (current wave) +
            2 * complexCoordinateAmplitudeSq
              (current wave - initial wave)) := by
      apply Finset.sum_le_sum
      intro wave _waveMem
      exact
        complexCoordinateAmplitudeSq_sub_le_two_mul
          (current wave) (current wave - initial wave)
    _ =
        2 * (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (current wave)) +
        2 * (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            ((current - initial) wave)) := by
      simp only [Pi.sub_apply, Finset.sum_add_distrib,
        Finset.mul_sum, lp.coeFn_sub]

/-- On the complete source-owned persistence interval, the actual whole
unforced path retains a fixed positive physical vorticity mass. -/
theorem wholeRestartCrossingMass_persists
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (time : Icc (0 : ℝ)
      (wholeRestartDuration (run initial index).contact))
    (timeLe : time.1 ≤
      wholeRestartCrossingMassPersistenceTime initial index crossed) :
    wholeRestartCrossingMassQuantum ν / 4 <
      wholeVorticityEuclideanMass
        ((run initial index).nextReceipt.wholePath time) := by
  let modes :=
    wholeRestartCrossingFiniteCoreModes initial index crossed
  let initialState := (run initial index).contact.physicalState
  let currentState := (run initial index).nextReceipt.wholePath time
  let quantum := wholeRestartCrossingMassQuantum ν
  have initialGt :
      quantum <
        finiteStateVorticityCoefficientEnstrophy modes initialState := by
    simpa only [modes, initialState, quantum] using
      wholeRestartCrossingMassQuantum_lt_finiteCoreMass
        initial index crossed
  have differenceLe :
      finiteStateVorticityCoefficientEnstrophy
          modes (currentState - initialState) ≤
        quantum / 4 := by
    simpa only [wholeRestartCrossingMassDifference,
      modes, currentState, initialState, quantum] using
      wholeRestartCrossingMassDifference_le_quarterQuantum
        initial index crossed time timeLe
  have initialLe :=
    finiteVorticityCoefficientEnstrophy_initial_le
      modes initialState currentState
  have currentQuarterLt :
      quantum / 4 <
        finiteStateVorticityCoefficientEnstrophy modes currentState := by
    nlinarith
  have finiteLeWhole :=
    finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes currentState
  calc
    quantum / 4 <
        finiteStateVorticityCoefficientEnstrophy modes currentState :=
      currentQuarterLt
    _ ≤ wholeVorticityEuclideanMass currentState := finiteLeWhole

/-! ## Same-receipt physical payment -/

/-- Pointwise persistence on the ordinary real-time representative of the
same actual successor receipt. -/
theorem wholeRestartCrossingMassPersistence_pointwise
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (actual : ℝ)
    (actualMem : actual ∈ Icc (0 : ℝ)
      (wholeRestartCrossingMassPersistenceTime
        initial index crossed)) :
    wholeRestartCrossingMassQuantum ν / 4 ≤
      wholeVorticityEuclideanMass
        (wholeRestartReceiptPhysicalTrajectory
          (run initial index).nextReceipt actual) := by
  let current := run initial index
  let localTime :=
    wholeRestartCrossingMassPersistenceTime initial index crossed
  have actualLeDuration :
      actual ≤ wholeRestartDuration current.contact := by
    exact actualMem.2.trans
      ((wholeRestartCrossingMassPersistenceTime_lt_contact
        initial index crossed).le.trans current.nextContact.time.2.2)
  let time : Icc (0 : ℝ) (wholeRestartDuration current.contact) :=
    ⟨actual, ⟨actualMem.1, actualLeDuration⟩⟩
  have pathEq :
      wholeRestartReceiptPhysicalTrajectory current.nextReceipt actual =
        current.nextReceipt.wholePath time := by
    unfold wholeRestartReceiptPhysicalTrajectory
    rw [projIcc_of_mem current.nextReceipt.requestedTimePos.le time.2]
  have retained :=
    wholeRestartCrossingMass_persists
      initial index crossed time actualMem.2
  change
    wholeRestartCrossingMassQuantum ν / 4 ≤
      wholeVorticityEuclideanMass
        (wholeRestartReceiptPhysicalTrajectory current.nextReceipt actual)
  rw [pathEq]
  exact retained.le

/-- The fixed mass quantum pays a positive amplitude--time rectangle on the
same actual unforced successor receipt. -/
theorem wholeRestartCrossingMassPersistence_amplitudeTime_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassPersistenceTime initial index crossed *
          (wholeRestartCrossingMassQuantum ν / 4) ≤
      ∫ actual in (0 : ℝ)..
          wholeRestartCrossingMassPersistenceTime initial index crossed,
        wholeVorticityEuclideanMass
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).nextReceipt actual) := by
  let localTime :=
    wholeRestartCrossingMassPersistenceTime initial index crossed
  let trajectory :=
    wholeRestartReceiptPhysicalTrajectory
      (run initial index).nextReceipt
  let density : ℝ → ℝ := fun actual =>
    wholeVorticityEuclideanMass (trajectory actual)
  have localTimePos : 0 < localTime :=
    wholeRestartCrossingMassPersistenceTime_pos
      initial index crossed
  have trajectoryContinuous : Continuous trajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous
      (run initial index).nextReceipt
  have densityContinuous : Continuous density := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact
      tendsto_wholeVorticityEuclideanMass
        trajectoryContinuous.continuousAt
  have integratedLower :=
    intervalIntegral.integral_mono_on
      (μ := volume)
      localTimePos.le
      (continuous_const.intervalIntegrable 0 localTime)
      (densityContinuous.intervalIntegrable 0 localTime)
      (wholeRestartCrossingMassPersistence_pointwise
        initial index crossed)
  have normalizedLower :
      localTime * wholeRestartCrossingMassQuantum ν / 4 ≤
        ∫ actual in (0 : ℝ)..localTime, density actual := by
    simpa [localTime, trajectory, density,
      intervalIntegral.integral_const, smul_eq_mul] using integratedLower
  calc
    wholeRestartCrossingMassPersistenceTime initial index crossed *
          (wholeRestartCrossingMassQuantum ν / 4) =
        localTime * wholeRestartCrossingMassQuantum ν / 4 := by
      dsimp [localTime]
      ring
    _ ≤ ∫ actual in (0 : ℝ)..localTime, density actual := normalizedLower
    _ = ∫ actual in (0 : ℝ)..
          wholeRestartCrossingMassPersistenceTime initial index crossed,
        wholeVorticityEuclideanMass
          (wholeRestartReceiptPhysicalTrajectory
            (run initial index).nextReceipt actual) := rfl

/-- The amplitude--time rectangle is charged to the existing physical
kinetic-dissipation ledger of the same generated successor receipt. -/
theorem wholeRestartCrossingMassPersistence_le_prefixVorticityMass
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassPersistenceTime initial index crossed *
          (wholeRestartCrossingMassQuantum ν / 4) ≤
      wholePrefixVorticityMass
        (run initial index).nextContact.time
        (run initial index).nextReceipt.stateLimit := by
  let current := run initial index
  let localTime :=
    wholeRestartCrossingMassPersistenceTime initial index crossed
  let contactTime := current.nextContact.time.1
  let trajectory :=
    wholeRestartReceiptPhysicalTrajectory current.nextReceipt
  let density : ℝ → ℝ := fun actual =>
    wholeVorticityEuclideanMass (trajectory actual)
  have localTimePos : 0 < localTime :=
    wholeRestartCrossingMassPersistenceTime_pos
      initial index crossed
  have localTimeLe : localTime ≤ contactTime :=
    (wholeRestartCrossingMassPersistenceTime_lt_contact
      initial index crossed).le
  have trajectoryContinuous : Continuous trajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous current.nextReceipt
  have densityContinuous : Continuous density := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact
      tendsto_wholeVorticityEuclideanMass
        trajectoryContinuous.continuousAt
  have localIntegralLeFull :
      (∫ actual in (0 : ℝ)..localTime, density actual) ≤
        ∫ actual in (0 : ℝ)..contactTime, density actual :=
    intervalIntegral.integral_mono_interval
      (μ := volume) (c := (0 : ℝ)) (d := contactTime)
      le_rfl localTimePos.le localTimeLe
      (Filter.Eventually.of_forall fun actual => by
        unfold density wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      (densityContinuous.intervalIntegrable 0 contactTime)
  have amplitudeTimeLe :=
    wholeRestartCrossingMassPersistence_amplitudeTime_le
      initial index crossed
  have integralEq :
      wholePrefixVorticityMass current.nextContact.time
          current.nextReceipt.stateLimit =
        ∫ actual in (0 : ℝ)..contactTime, density actual := by
    simpa only [current, contactTime, trajectory, density] using
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        current.nextReceipt current.nextContact.time
  calc
    wholeRestartCrossingMassPersistenceTime initial index crossed *
          (wholeRestartCrossingMassQuantum ν / 4) ≤
        ∫ actual in (0 : ℝ)..localTime, density actual := by
      simpa only [localTime, trajectory, density] using amplitudeTimeLe
    _ ≤ ∫ actual in (0 : ℝ)..contactTime, density actual :=
      localIntegralLeFull
    _ = wholePrefixVorticityMass current.nextContact.time
          current.nextReceipt.stateLimit := integralEq.symm

theorem wholeRestartCrossingMassPersistence_payment_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 < wholeRestartCrossingMassPersistenceTime initial index crossed *
      (wholeRestartCrossingMassQuantum ν / 4) :=
  mul_pos
    (wholeRestartCrossingMassPersistenceTime_pos
      initial index crossed)
    (div_pos (wholeRestartCrossingMassQuantum_pos ν) (by norm_num))

/-! ## Global same-run charge -/

/-- Total source readout: a crossing contributes its generated lifetime;
the faithful noncrossing branch contributes zero. -/
noncomputable def wholeRestartCrossingMassPersistenceDuration
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ := by
  classical
  exact if crossed : wholeRestartHalfCriticalCrossed initial index then
    wholeRestartCrossingMassPersistenceTime initial index crossed
  else
    0

theorem wholeRestartCrossingMassPersistenceDuration_of_crossed
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassPersistenceDuration initial index =
      wholeRestartCrossingMassPersistenceTime initial index crossed := by
  classical
  simp [wholeRestartCrossingMassPersistenceDuration, crossed]

theorem wholeRestartCrossingMassPersistenceDuration_of_not_crossed
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (notCrossed : ¬ wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingMassPersistenceDuration initial index = 0 := by
  classical
  simp [wholeRestartCrossingMassPersistenceDuration, notCrossed]

theorem wholeRestartCrossingMassPersistenceDuration_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartCrossingMassPersistenceDuration initial index := by
  classical
  by_cases crossed : wholeRestartHalfCriticalCrossed initial index
  · rw [wholeRestartCrossingMassPersistenceDuration_of_crossed
      initial index crossed]
    exact
      (wholeRestartCrossingMassPersistenceTime_pos
        initial index crossed).le
  · rw [wholeRestartCrossingMassPersistenceDuration_of_not_crossed
      initial index crossed]

/-- Kinetic charge of the generated persistence rectangle.  Its coefficient
is the exact viscous factor already used by the native kinetic ledger. -/
def wholeRestartCrossingMassKineticCharge
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) : ℝ :=
  (2 * ν.coeff * (wholeRestartCrossingMassQuantum ν / 4)) *
    wholeRestartCrossingMassPersistenceDuration initial index

theorem wholeRestartCrossingMassKineticCharge_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    0 ≤ wholeRestartCrossingMassKineticCharge initial index := by
  unfold wholeRestartCrossingMassKineticCharge
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) ν.coeff_pos.le)
      (div_nonneg (wholeRestartCrossingMassQuantum_pos ν).le (by norm_num)))
    (wholeRestartCrossingMassPersistenceDuration_nonneg initial index)

/-- Every generated crossing rectangle is paid once by the kinetic
dissipation of the same actual successor receipt. -/
theorem wholeRestartCrossingMassKineticCharge_le_nextPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ) :
    wholeRestartCrossingMassKineticCharge initial index ≤
      wholeRestartNextKineticDissipationPayment initial index := by
  classical
  by_cases crossed : wholeRestartHalfCriticalCrossed initial index
  · have persistenceLe :=
      wholeRestartCrossingMassPersistence_le_prefixVorticityMass
        initial index crossed
    rw [wholeRestartCrossingMassKineticCharge,
      wholeRestartCrossingMassPersistenceDuration_of_crossed
        initial index crossed]
    unfold wholeRestartNextKineticDissipationPayment
    calc
      (2 * ν.coeff * (wholeRestartCrossingMassQuantum ν / 4)) *
          wholeRestartCrossingMassPersistenceTime initial index crossed =
          (2 * ν.coeff) *
            (wholeRestartCrossingMassPersistenceTime initial index crossed *
              (wholeRestartCrossingMassQuantum ν / 4)) := by ring
      _ ≤ (2 * ν.coeff) *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit :=
        mul_le_mul_of_nonneg_left persistenceLe
          (mul_nonneg (by norm_num) ν.coeff_pos.le)
      _ = 2 * ν.coeff *
          wholePrefixVorticityMass
            (run initial index).nextContact.time
            (run initial index).nextReceipt.stateLimit := by ring
  · rw [wholeRestartCrossingMassKineticCharge,
      wholeRestartCrossingMassPersistenceDuration_of_not_crossed
        initial index crossed, mul_zero]
    exact wholeRestartNextKineticDissipationPayment_nonneg initial index

/-- Every finite prefix of generated crossing rectangles is paid by the
initial physical kinetic mass. -/
theorem wholeRestartAccumulatedCrossingMassKineticCharge_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (length : ℕ) :
    (∑ index ∈ Finset.range length,
        wholeRestartCrossingMassKineticCharge initial index) ≤
      puncturedWholeVorticityKineticMass
        initial.contact.physicalState := by
  calc
    (∑ index ∈ Finset.range length,
        wholeRestartCrossingMassKineticCharge initial index) ≤
        ∑ index ∈ Finset.range length,
          wholeRestartNextKineticDissipationPayment initial index := by
      apply Finset.sum_le_sum
      intro index _indexMem
      exact
        wholeRestartCrossingMassKineticCharge_le_nextPayment
          initial index
    _ = wholeRestartAccumulatedKineticDissipationPayment
        initial length := rfl
    _ ≤ puncturedWholeVorticityKineticMass
        initial.contact.physicalState :=
      wholeRestartAccumulatedKineticDissipationPayment_le_initial
        initial length

theorem summable_wholeRestartCrossingMassKineticCharge
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    Summable (wholeRestartCrossingMassKineticCharge initial) :=
  (summable_wholeRestartNextKineticDissipationPayment initial).of_nonneg_of_le
    (wholeRestartCrossingMassKineticCharge_nonneg initial)
    (wholeRestartCrossingMassKineticCharge_le_nextPayment initial)

theorem tsum_wholeRestartCrossingMassKineticCharge_le_initial
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    (∑' index : ℕ,
        wholeRestartCrossingMassKineticCharge initial index) ≤
      puncturedWholeVorticityKineticMass
        initial.contact.physicalState := by
  exact
    (summable_wholeRestartCrossingMassKineticCharge initial).tsum_le_of_sum_range_le
      (wholeRestartAccumulatedCrossingMassKineticCharge_le_initial initial)

/-- Since the coefficient multiplying every crossing lifetime is fixed and
strictly positive, the complete source-generated crossing lifetime family
is summable. -/
theorem summable_wholeRestartCrossingMassPersistenceDuration
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    Summable (wholeRestartCrossingMassPersistenceDuration initial) := by
  let coefficient : ℝ :=
    2 * ν.coeff * (wholeRestartCrossingMassQuantum ν / 4)
  have coefficientPos : 0 < coefficient := by
    exact mul_pos
      (mul_pos (by norm_num) ν.coeff_pos)
      (div_pos (wholeRestartCrossingMassQuantum_pos ν) (by norm_num))
  have scaled :=
    (summable_wholeRestartCrossingMassKineticCharge initial).mul_left
      coefficient⁻¹
  exact scaled.congr fun index => by
    change
      coefficient⁻¹ *
          (coefficient *
            wholeRestartCrossingMassPersistenceDuration initial index) =
        wholeRestartCrossingMassPersistenceDuration initial index
    rw [← mul_assoc, inv_mul_cancel₀ coefficientPos.ne', one_mul]

/-- On the authoritative native run, finite total kinetic dissipation forces
the actual crossing-persistence lifetimes to collapse to zero.  Combined
with the explicit lifetime formula, this is the exact frequency--amplitude--
time obstruction left to the regularity consumer. -/
theorem tendsto_wholeRestartCrossingMassPersistenceDuration_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν) :
    Tendsto
      (wholeRestartCrossingMassPersistenceDuration initial)
      atTop (𝓝 0) :=
  (summable_wholeRestartCrossingMassPersistenceDuration
    initial).tendsto_atTop_zero

/-! ## Native frequency--time regularity obstruction -/

/-- Along the authoritative run, an actual crossing can eventually retain
neither both a uniform positive physical restart time and a uniform bound on
the least-core observation budget.  Every sufficiently late crossing must
therefore collapse its actual time step or escape through the source-native
frequency/negative-one budget.

The theorem consumes the already-proved finite kinetic ledger; it accepts no
crossing subsequence, cutoff, continuation witness, or payment certificate. -/
theorem eventually_wholeRestartCrossing_contact_lt_or_holderBudget_gt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (contactFloor holderCeiling : ℝ)
    (contactFloorPos : 0 < contactFloor)
    (holderCeilingNonneg : 0 ≤ holderCeiling) :
    ∀ᶠ index : ℕ in atTop,
      ∀ crossed : wholeRestartHalfCriticalCrossed initial index,
        (run initial index).nextContact.time.1 < contactFloor ∨
          holderCeiling <
            wholeRestartCrossingMassHolderBudget
              initial index crossed := by
  let quantum := wholeRestartCrossingMassQuantum ν
  let lowerLifetime :=
    min (contactFloor / 2)
      (quantum / (12 * holderCeiling + 1))
  have quantumPos : 0 < quantum := by
    simpa only [quantum] using wholeRestartCrossingMassQuantum_pos ν
  have holderDenominatorPos : 0 < 12 * holderCeiling + 1 := by
    positivity
  have lowerLifetimePos : 0 < lowerLifetime := by
    exact lt_min
      (div_pos contactFloorPos (by norm_num))
      (div_pos quantumPos holderDenominatorPos)
  have eventuallySmall :
      ∀ᶠ index : ℕ in atTop,
        wholeRestartCrossingMassPersistenceDuration initial index <
          lowerLifetime :=
    (tendsto_wholeRestartCrossingMassPersistenceDuration_zero initial).eventually
      (eventually_lt_nhds lowerLifetimePos)
  filter_upwards [eventuallySmall] with index durationLt
  intro crossed
  by_contra bothRetained
  rw [not_or] at bothRetained
  have contactFloorLe :
      contactFloor ≤ (run initial index).nextContact.time.1 :=
    le_of_not_gt bothRetained.1
  have budgetLe :
      wholeRestartCrossingMassHolderBudget initial index crossed ≤
        holderCeiling :=
    le_of_not_gt bothRetained.2
  have budgetNonneg :
      0 ≤ wholeRestartCrossingMassHolderBudget initial index crossed :=
    wholeRestartCrossingMassHolderBudget_nonneg initial index crossed
  have budgetDenominatorPos :
      0 <
        12 * wholeRestartCrossingMassHolderBudget initial index crossed + 1 := by
    positivity
  have quotientLe :
      quantum / (12 * holderCeiling + 1) ≤
        quantum /
          (12 * wholeRestartCrossingMassHolderBudget
            initial index crossed + 1) := by
    apply
      (div_le_div_iff₀ holderDenominatorPos budgetDenominatorPos).2
    nlinarith
  have lowerLifetimeLe :
      lowerLifetime ≤
        wholeRestartCrossingMassPersistenceTime initial index crossed := by
    unfold lowerLifetime wholeRestartCrossingMassPersistenceTime
    exact min_le_min
      (div_le_div_of_nonneg_right contactFloorLe (by norm_num))
      quotientLe
  have durationEq :
      wholeRestartCrossingMassPersistenceDuration initial index =
        wholeRestartCrossingMassPersistenceTime initial index crossed :=
    wholeRestartCrossingMassPersistenceDuration_of_crossed
      initial index crossed
  rw [durationEq] at durationLt
  exact (not_lt_of_ge lowerLifetimeLe) durationLt

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
end NavierStokes
end SaturationMonoid
