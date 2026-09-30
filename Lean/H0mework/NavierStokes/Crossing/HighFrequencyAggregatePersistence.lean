import H0mework.NavierStokes.Crossing.FiniteNegativeOneDisplacement
import H0mework.NavierStokes.Crossing.HighFrequencyAggregateResponsibility

/-!
# Source-generated persistence of an aggregate high-frequency responsibility

The inverse-Laplacian weighted displacement estimate is combined here with
frequency-weighted Cauchy--Schwarz.  A finite family selected from one actual
restart current therefore carries its own common persistence time

```text
min (T / 2) (M^2 / (48 W N)),
```

where `M` is its coefficient mass, `W` its frequency-weighted mass, and `N`
the square norm of the same outgoing whole-receipt tangent.  No modulus,
cutoff, time, or absorption certificate is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregatePersistence

open scoped BigOperators Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open
  ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellWholeReceiptEnergyWriteBack
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeKineticDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticDissipationLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartFinitePrefixDualSquareLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartComponentGluingResidualNativeProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingGluingNegativeOneBridge
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingMassPersistence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteNegativeOneDisplacement
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregateResponsibility
open AffineRelaxation

noncomputable section

private theorem complexCoordinateRealInner_sq_le_weighted_displacement
    (multiplier : ℝ)
    (multiplierPos : 0 < multiplier)
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right ^ 2 ≤
      (multiplier * complexCoordinateAmplitudeSq left) *
        complexCoordinateAmplitudeSq
          (((Real.sqrt multiplier : ℂ)⁻¹) • right) := by
  have base := complexCoordinateRealInner_sq_le left right
  have rootSq : Real.sqrt multiplier * Real.sqrt multiplier = multiplier := by
    nlinarith [Real.sq_sqrt multiplierPos.le]
  have rhsEq :
      (multiplier * complexCoordinateAmplitudeSq left) *
          complexCoordinateAmplitudeSq
            (((Real.sqrt multiplier : ℂ)⁻¹) • right) =
        complexCoordinateAmplitudeSq left *
          complexCoordinateAmplitudeSq right := by
    simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq,
      complexCoordinateVectorNormSq_smul, Complex.normSq_inv,
      Complex.normSq_ofReal]
    rw [rootSq]
    field_simp [ne_of_gt multiplierPos]
  rwa [rhsEq]

private theorem complexCoordinateAmplitudeSq_add
    (left right : ComplexCoordinateVector) :
    complexCoordinateAmplitudeSq (left + right) =
      complexCoordinateAmplitudeSq left +
        2 * complexCoordinateRealInner left right +
        complexCoordinateAmplitudeSq right := by
  unfold complexCoordinateAmplitudeSq complexCoordinateRealInner
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate coordinateMem
  simp only [Pi.add_apply, Complex.normSq_apply,
    Complex.add_re, Complex.add_im]
  ring

/-- Weighted Cauchy--Schwarz on the original finite coefficient carrier.
The inverse-square-root displacement is kept before coefficient quotient. -/
theorem finiteAggregateMass_persists_of_weighted_displacement
    {indexType : Type*}
    [DecidableEq indexType]
    (indices : Finset indexType)
    (multiplier : indexType → ℝ)
    (multiplierPos : ∀ index ∈ indices, 0 < multiplier index)
    (initialState currentState : indexType → ComplexCoordinateVector)
    (initialMassPos :
      0 < ∑ index ∈ indices,
        complexCoordinateAmplitudeSq (initialState index))
    (displacementSmall :
      (∑ index ∈ indices,
          multiplier index *
            complexCoordinateAmplitudeSq (initialState index)) *
          (∑ index ∈ indices,
            complexCoordinateAmplitudeSq
              (((Real.sqrt (multiplier index) : ℂ)⁻¹) •
                (currentState index - initialState index))) ≤
        (∑ index ∈ indices,
          complexCoordinateAmplitudeSq (initialState index)) ^ 2 / 16) :
    (∑ index ∈ indices,
        complexCoordinateAmplitudeSq (initialState index)) / 2 ≤
      ∑ index ∈ indices,
        complexCoordinateAmplitudeSq (currentState index) := by
  let initialMass :=
    ∑ index ∈ indices,
      complexCoordinateAmplitudeSq (initialState index)
  let weightedMass :=
    ∑ index ∈ indices,
      multiplier index *
        complexCoordinateAmplitudeSq (initialState index)
  let displacement :=
    ∑ index ∈ indices,
      complexCoordinateAmplitudeSq
        (((Real.sqrt (multiplier index) : ℂ)⁻¹) •
          (currentState index - initialState index))
  let crossTerm :=
    ∑ index ∈ indices,
      complexCoordinateRealInner
        (initialState index)
        (currentState index - initialState index)
  let remainderMass :=
    ∑ index ∈ indices,
      complexCoordinateAmplitudeSq
        (currentState index - initialState index)
  have cauchy :
      crossTerm ^ 2 ≤ weightedMass * displacement := by
    dsimp [crossTerm, weightedMass, displacement]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul indices
      (fun index indexMem =>
        mul_nonneg (multiplierPos index indexMem).le
          (complexCoordinateAmplitudeSq_nonneg _))
      (fun index indexMem => complexCoordinateAmplitudeSq_nonneg _)
      (fun index indexMem =>
        complexCoordinateRealInner_sq_le_weighted_displacement
          (multiplier index) (multiplierPos index indexMem) _ _)
  have crossSq : crossTerm ^ 2 ≤ initialMass ^ 2 / 16 :=
    cauchy.trans (by
      simpa [initialMass, weightedMass, displacement] using
        displacementSmall)
  have crossLower : -initialMass / 4 ≤ crossTerm := by
    have initialMassPos' : 0 < initialMass := by
      simpa [initialMass] using initialMassPos
    nlinarith [sq_nonneg (crossTerm + initialMass / 4),
      sq_nonneg (crossTerm - initialMass / 4)]
  have massIdentity :
      (∑ index ∈ indices,
          complexCoordinateAmplitudeSq (currentState index)) =
        initialMass + 2 * crossTerm + remainderMass := by
    dsimp [initialMass, crossTerm, remainderMass]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro index indexMem
    calc
      complexCoordinateAmplitudeSq (currentState index) =
          complexCoordinateAmplitudeSq
            (initialState index +
              (currentState index - initialState index)) := by
        congr 1
        abel
      _ = _ := complexCoordinateAmplitudeSq_add _ _
  have remainderNonneg : 0 ≤ remainderMass := by
    dsimp [remainderMass]
    exact Finset.sum_nonneg fun index indexMem =>
      complexCoordinateAmplitudeSq_nonneg _
  rw [massIdentity]
  nlinarith

/-- The common persistence time generated by the actual coefficient family
and the same outgoing whole-receipt tangent. -/
def wholeRestartCrossingFiniteAggregatePersistenceTime
    { ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector) : ℝ :=
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  let tangentSq :=
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
  min
    ((run initial index).nextContact.time.1 / 2)
    (initialMass ^ 2 / (48 * weightedInitialMass * tangentSq))

theorem wholeRestartCrossingFiniteAggregateWeightedInitialMass_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    0 < ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) := by
  have spectralPos : 0 < (2 * Real.pi) ^ 2 :=
    sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos)
  have scaledInitialPos :
      0 < (2 * Real.pi) ^ 2 *
        ∑ output ∈ modes,
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output) :=
    mul_pos spectralPos initialMassPos
  apply scaledInitialPos.trans_le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro output outputMem
  exact mul_le_mul_of_nonneg_right
    (twoPiSq_le_integerWaveViscousMultiplier
      ⟨output, modesNonzero output outputMem⟩)
    (complexCoordinateAmplitudeSq_nonneg _)

theorem wholeRestartCrossingPrefixWholeTangent_norm_sq_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    0 <
      ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  exact (wholeRestartCrossingTangentPayment_pos_of_crossed
    initial index crossed).trans_le
      (wholeRestartCrossingTangentPayment_le_wholeTangent
        initial index)

theorem wholeRestartCrossingFiniteAggregatePersistenceTime_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    0 < wholeRestartCrossingFiniteAggregatePersistenceTime
      initial index modes := by
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  let tangentSq :=
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
  have initialMassPos' : 0 < initialMass := by
    simpa only [initialMass] using initialMassPos
  have weightedInitialMassPos : 0 < weightedInitialMass := by
    simpa only [weightedInitialMass] using
      wholeRestartCrossingFiniteAggregateWeightedInitialMass_pos
        initial index modes modesNonzero initialMassPos
  have tangentSqPos : 0 < tangentSq := by
    simpa only [tangentSq] using
      wholeRestartCrossingPrefixWholeTangent_norm_sq_pos
        initial index crossed
  unfold wholeRestartCrossingFiniteAggregatePersistenceTime
  dsimp only
  apply lt_min
  · exact div_pos (run initial index).nextContact.time_pos (by norm_num)
  · exact div_pos (sq_pos_of_pos initialMassPos')
      (mul_pos (mul_pos (by norm_num) weightedInitialMassPos)
        tangentSqPos)

theorem wholeRestartCrossingFiniteAggregatePersistenceTime_lt_contact
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector) :
    wholeRestartCrossingFiniteAggregatePersistenceTime
        initial index modes <
      (run initial index).nextContact.time.1 := by
  have halfLe :
      wholeRestartCrossingFiniteAggregatePersistenceTime
          initial index modes ≤
        (run initial index).nextContact.time.1 / 2 := by
    unfold wholeRestartCrossingFiniteAggregatePersistenceTime
    exact min_le_left _ _
  linarith [(run initial index).nextContact.time_pos]

/-- Up to the source-generated common time, at least half of the selected
finite coefficient mass remains on the same actual whole receipt.  The
frequency sum enters only through its genuine weighted initial mass; there
is no mode-count or largest-frequency constant. -/
theorem wholeRestartCrossingFiniteAggregateMass_persists
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output))
    (time : Icc (0 : ℝ) (run initial index).nextContact.time.1)
    (timeLe :
      time.1 ≤ wholeRestartCrossingFiniteAggregatePersistenceTime
        initial index modes) :
    (∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) / 2 ≤
      ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).nextContact.prefixReceipt.wholePath
            time output) := by
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  let tangentSq :=
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
  let displacement :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        (((Real.sqrt
          (integerWaveViscousMultiplier output) : ℂ)⁻¹) •
          ((run initial index).nextContact.prefixReceipt.wholePath
              time output -
            (run initial index).contact.physicalState output))
  have weightedInitialMassPos : 0 < weightedInitialMass := by
    simpa only [weightedInitialMass] using
      wholeRestartCrossingFiniteAggregateWeightedInitialMass_pos
        initial index modes modesNonzero initialMassPos
  have tangentSqPos : 0 < tangentSq := by
    simpa only [tangentSq] using
      wholeRestartCrossingPrefixWholeTangent_norm_sq_pos
        initial index crossed
  have timeLeRatio :
      time.1 ≤ initialMass ^ 2 /
        (48 * weightedInitialMass * tangentSq) := by
    apply timeLe.trans
    unfold wholeRestartCrossingFiniteAggregatePersistenceTime
    simpa only [initialMass, weightedInitialMass, tangentSq] using
      (min_le_right
        ((run initial index).nextContact.time.1 / 2)
        (initialMass ^ 2 /
          (48 * weightedInitialMass * tangentSq)))
  have denominatorPos : 0 < 48 * weightedInitialMass * tangentSq := by
    positivity
  have scaledTime :
      time.1 * (48 * weightedInitialMass * tangentSq) ≤
        initialMass ^ 2 :=
    (le_div_iff₀ denominatorPos).mp timeLeRatio
  have displacementLe :
      displacement ≤ 3 * time.1 * tangentSq := by
    simpa only [displacement, tangentSq] using
      wholeRestartCrossingFiniteNegativeOneDisplacement_le
        initial index modes modesNonzero time
  have weightedDisplacementSmall :
      weightedInitialMass * displacement ≤ initialMass ^ 2 / 16 := by
    have scaledDisplacement :=
      mul_le_mul_of_nonneg_left
        displacementLe weightedInitialMassPos.le
    nlinarith
  exact finiteAggregateMass_persists_of_weighted_displacement
    modes integerWaveViscousMultiplier
    (fun output outputMem =>
      integerWaveViscousMultiplier_pos
        ⟨output, modesNonzero output outputMem⟩)
    (fun output => (run initial index).contact.physicalState output)
    (fun output =>
      (run initial index).nextContact.prefixReceipt.wholePath time output)
    initialMassPos
    (by
      simpa only [initialMass, weightedInitialMass, displacement] using
        weightedDisplacementSmall)

/-- Native kinetic charge of the source-generated aggregate persistence
rectangle. -/
def wholeRestartCrossingFiniteAggregateKineticCharge
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset IntegerWavevector) : ℝ :=
  ν.coeff *
    wholeRestartCrossingFiniteAggregatePersistenceTime
      initial index modes *
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)

theorem wholeRestartCrossingFiniteAggregateKineticCharge_pos
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    0 < wholeRestartCrossingFiniteAggregateKineticCharge
      initial index modes := by
  unfold wholeRestartCrossingFiniteAggregateKineticCharge
  exact mul_pos
    (mul_pos ν.coeff_pos
      (wholeRestartCrossingFiniteAggregatePersistenceTime_pos
        initial index crossed modes modesNonzero initialMassPos))
    initialMassPos

/-- Exact obstruction split for the generated charge.  Its possible
collapse is now confined to the actual contact-time scale or to the cubic
mass / frequency-weighted tangent rate; there is no unnamed continuity
modulus left in the statement. -/
theorem wholeRestartCrossingFiniteAggregateKineticCharge_eq_min_rate
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    let initialMass :=
      ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
    let weightedInitialMass :=
      ∑ output ∈ modes,
        integerWaveViscousMultiplier output *
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)
    let tangentSq :=
      ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
    wholeRestartCrossingFiniteAggregateKineticCharge
        initial index modes =
      min
        (ν.coeff * (run initial index).nextContact.time.1 *
          initialMass / 2)
        (ν.coeff * initialMass ^ 3 /
          (48 * weightedInitialMass * tangentSq)) := by
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        ((run initial index).contact.physicalState output)
  let weightedInitialMass :=
    ∑ output ∈ modes,
      integerWaveViscousMultiplier output *
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  let tangentSq :=
    ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
  have initialMassPos' : 0 < initialMass := by
    simpa only [initialMass] using initialMassPos
  have weightedInitialMassPos : 0 < weightedInitialMass := by
    simpa only [weightedInitialMass] using
      wholeRestartCrossingFiniteAggregateWeightedInitialMass_pos
        initial index modes modesNonzero initialMassPos
  have tangentSqPos : 0 < tangentSq := by
    simpa only [tangentSq] using
      wholeRestartCrossingPrefixWholeTangent_norm_sq_pos
        initial index crossed
  dsimp only
  unfold wholeRestartCrossingFiniteAggregateKineticCharge
    wholeRestartCrossingFiniteAggregatePersistenceTime
  change
    ν.coeff *
          min
            ((run initial index).nextContact.time.1 / 2)
            (initialMass ^ 2 /
              (48 * weightedInitialMass * tangentSq)) *
        initialMass = _
  calc
    ν.coeff *
          min
            ((run initial index).nextContact.time.1 / 2)
            (initialMass ^ 2 /
              (48 * weightedInitialMass * tangentSq)) *
        initialMass =
      (ν.coeff * initialMass) *
        min
          ((run initial index).nextContact.time.1 / 2)
          (initialMass ^ 2 /
            (48 * weightedInitialMass * tangentSq)) := by ring
    _ = min
        ((ν.coeff * initialMass) *
          ((run initial index).nextContact.time.1 / 2))
        ((ν.coeff * initialMass) *
          (initialMass ^ 2 /
            (48 * weightedInitialMass * tangentSq))) :=
      mul_min_of_nonneg _ _
        (mul_nonneg ν.coeff_pos.le initialMassPos'.le)
    _ = min
        (ν.coeff * (run initial index).nextContact.time.1 *
          initialMass / 2)
        (ν.coeff * initialMass ^ 3 /
          (48 * weightedInitialMass * tangentSq)) := by
      congr 1
      · ring
      · field_simp [ne_of_gt weightedInitialMassPos,
          ne_of_gt tangentSqPos]

/-- The explicit persistence charge is paid once by the kinetic
dissipation of the same actual successor receipt. -/
theorem wholeRestartCrossingFiniteAggregateKineticCharge_le_nextPayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (modes : Finset IntegerWavevector)
    (modesNonzero : ∀ output ∈ modes, output ≠ 0)
    (initialMassPos :
      0 < ∑ output ∈ modes,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)) :
    wholeRestartCrossingFiniteAggregateKineticCharge
        initial index modes ≤
      wholeRestartNextKineticDissipationPayment initial index := by
  let current := run initial index
  let localTime :=
    wholeRestartCrossingFiniteAggregatePersistenceTime
      initial index modes
  let initialMass :=
    ∑ output ∈ modes,
      complexCoordinateAmplitudeSq
        (current.contact.physicalState output)
  let prefixTrajectory :=
    wholeRestartReceiptPhysicalTrajectory
      current.nextContact.prefixReceipt
  let fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory current.nextReceipt
  let density : ℝ → ℝ := fun actual =>
    finiteStateVorticityCoefficientEnstrophy modes
      (fullTrajectory actual)
  let wholeDensity : ℝ → ℝ := fun actual =>
    wholeVorticityEuclideanMass (fullTrajectory actual)
  have localTimePos : 0 < localTime := by
    simpa only [localTime] using
      wholeRestartCrossingFiniteAggregatePersistenceTime_pos
        initial index crossed modes modesNonzero initialMassPos
  have localTimeLt : localTime < current.nextContact.time.1 := by
    simpa only [localTime, current] using
      wholeRestartCrossingFiniteAggregatePersistenceTime_lt_contact
        initial index modes
  have prefixTrajectoryEq
      (actual : ℝ)
      (actualMem : actual ∈ Icc (0 : ℝ) current.nextContact.time.1) :
      prefixTrajectory actual = fullTrajectory actual := by
    unfold prefixTrajectory fullTrajectory
      wholeRestartReceiptPhysicalTrajectory
    rw [projIcc_of_mem
      current.nextContact.prefixReceipt.requestedTimePos.le actualMem]
    rw [projIcc_of_mem current.nextReceipt.requestedTimePos.le
      ⟨actualMem.1,
        actualMem.2.trans current.nextContact.time.2.2⟩]
    rfl
  have retained :
      ∀ actual ∈ Icc (0 : ℝ) localTime,
        initialMass / 2 ≤ density actual := by
    intro actual actualMem
    have actualPrefixMem :
        actual ∈ Icc (0 : ℝ) current.nextContact.time.1 :=
      ⟨actualMem.1, actualMem.2.trans localTimeLt.le⟩
    let time : Icc (0 : ℝ) current.nextContact.time.1 :=
      ⟨actual, actualPrefixMem⟩
    have persists :=
      wholeRestartCrossingFiniteAggregateMass_persists
        initial index crossed modes modesNonzero initialMassPos
        time actualMem.2
    have prefixEq := prefixTrajectoryEq actual actualPrefixMem
    unfold prefixTrajectory at prefixEq
    rw [wholeRestartReceiptPhysicalTrajectory,
      projIcc_of_mem
        current.nextContact.prefixReceipt.requestedTimePos.le
        actualPrefixMem] at prefixEq
    dsimp only [initialMass, density,
      finiteStateVorticityCoefficientEnstrophy]
    rw [← prefixEq]
    simpa only [time, current] using persists
  have fullTrajectoryContinuous : Continuous fullTrajectory :=
    wholeRestartReceiptPhysicalTrajectory_continuous current.nextReceipt
  have densityContinuous : Continuous density := by
    unfold density finiteStateVorticityCoefficientEnstrophy
    apply continuous_finsetSum
    intro output outputMem
    exact complexCoordinateAmplitudeSq_continuous.comp
      ((lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 output).continuous.comp fullTrajectoryContinuous)
  have wholeDensityContinuous : Continuous wholeDensity := by
    rw [continuous_iff_continuousAt]
    intro actual
    exact tendsto_wholeVorticityEuclideanMass
      fullTrajectoryContinuous.continuousAt
  have amplitudeTimeLeDensity :
      localTime * (initialMass / 2) ≤
        ∫ actual in (0 : ℝ)..localTime, density actual := by
    have integrated :=
      intervalIntegral.integral_mono_on
        (μ := volume)
        localTimePos.le
        (continuous_const.intervalIntegrable 0 localTime)
        (densityContinuous.intervalIntegrable 0 localTime)
        retained
    calc
      localTime * (initialMass / 2) =
          localTime * initialMass / 2 := by ring
      _ ≤ ∫ actual in (0 : ℝ)..localTime, density actual := by
        simpa [intervalIntegral.integral_const,
          sub_zero, smul_eq_mul] using integrated
  have densityIntegralLeWhole :
      (∫ actual in (0 : ℝ)..localTime, density actual) ≤
        ∫ actual in (0 : ℝ)..localTime, wholeDensity actual :=
    intervalIntegral.integral_mono_on
      localTimePos.le
      (densityContinuous.intervalIntegrable 0 localTime)
      (wholeDensityContinuous.intervalIntegrable 0 localTime)
      (fun actual _ =>
        finiteStateVorticityCoefficientEnstrophy_le_wholeMass
          modes (fullTrajectory actual))
  have localIntegralLeFull :
      (∫ actual in (0 : ℝ)..localTime, wholeDensity actual) ≤
        ∫ actual in (0 : ℝ)..current.nextContact.time.1,
          wholeDensity actual :=
    intervalIntegral.integral_mono_interval
      (c := (0 : ℝ)) (d := current.nextContact.time.1)
      le_rfl localTimePos.le localTimeLt.le
      (Filter.Eventually.of_forall fun actual => by
        unfold wholeDensity wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _)
      (wholeDensityContinuous.intervalIntegrable
        0 current.nextContact.time.1)
  have fullIntegralEq :
      wholePrefixVorticityMass current.nextContact.time
          current.nextReceipt.stateLimit =
        ∫ actual in (0 : ℝ)..current.nextContact.time.1,
          wholeDensity actual := by
    simpa [wholeDensity, fullTrajectory] using
      wholePrefixVorticityMass_receipt_eq_intervalIntegral
        current.nextReceipt current.nextContact.time
  unfold wholeRestartCrossingFiniteAggregateKineticCharge
  change
    ν.coeff * localTime * initialMass ≤
      wholeRestartNextKineticDissipationPayment initial index
  calc
    ν.coeff * localTime * initialMass =
        2 * ν.coeff * (localTime * (initialMass / 2)) := by ring
    _ ≤ 2 * ν.coeff *
        (∫ actual in (0 : ℝ)..localTime, density actual) :=
      mul_le_mul_of_nonneg_left amplitudeTimeLeDensity
        (mul_nonneg (by norm_num) ν.coeff_pos.le)
    _ ≤ 2 * ν.coeff *
        (∫ actual in (0 : ℝ)..localTime, wholeDensity actual) :=
      mul_le_mul_of_nonneg_left densityIntegralLeWhole
        (mul_nonneg (by norm_num) ν.coeff_pos.le)
    _ ≤ 2 * ν.coeff *
        (∫ actual in (0 : ℝ)..current.nextContact.time.1,
          wholeDensity actual) :=
      mul_le_mul_of_nonneg_left localIntegralLeFull
        (mul_nonneg (by norm_num) ν.coeff_pos.le)
    _ = wholeRestartNextKineticDissipationPayment initial index := by
      rw [← fullIntegralEq]
      rfl

/-! ## Source-generated high-frequency persistence responsibility -/

/-- The faithful-zero output of the finite-time producer, retaining the
actual finite coefficient family together with its canonical persistence
time and same-successor kinetic settlement. -/
structure WholeRestartHighFrequencyAggregatePersistenceReceipt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index radius : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (budget : ℝ) where
  gluingZero :
    wholeRestartCrossingCompleteSourceGluingNegativeOneState
      initial index crossed = 0
  outputs : Finset IntegerWavevector
  outputsGeometry :
    ∀ output ∈ outputs,
      output ≠ 0 ∧
        2 * radius < integerWaveCoordinateRadius output ∧
        output ∉ finiteVorticityPairOutputSupport
          (wholeRestartCrossingFiniteCoreModes initial index crossed)
  initialMassLarge :
    max budget 0 <
      ∑ output ∈ outputs,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
  persistenceTimePos :
    0 < wholeRestartCrossingFiniteAggregatePersistenceTime
      initial index outputs
  persistenceTimeLt :
    wholeRestartCrossingFiniteAggregatePersistenceTime
        initial index outputs <
      (run initial index).nextContact.time.1
  massPersists :
    ∀ time : Icc (0 : ℝ) (run initial index).nextContact.time.1,
      time.1 ≤ wholeRestartCrossingFiniteAggregatePersistenceTime
          initial index outputs →
        (∑ output ∈ outputs,
            complexCoordinateAmplitudeSq
              ((run initial index).contact.physicalState output)) / 2 ≤
          ∑ output ∈ outputs,
            complexCoordinateAmplitudeSq
              ((run initial index).nextContact.prefixReceipt.wholePath
                time output)
  kineticChargePos :
    0 < wholeRestartCrossingFiniteAggregateKineticCharge
      initial index outputs
  kineticChargeLe :
    wholeRestartCrossingFiniteAggregateKineticCharge
        initial index outputs ≤
      wholeRestartNextKineticDissipationPayment initial index
  kineticChargeRate :
    let initialMass :=
      ∑ output ∈ outputs,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output)
    let weightedInitialMass :=
      ∑ output ∈ outputs,
        integerWaveViscousMultiplier output *
          complexCoordinateAmplitudeSq
            ((run initial index).contact.physicalState output)
    let tangentSq :=
      ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2
    wholeRestartCrossingFiniteAggregateKineticCharge
        initial index outputs =
      min
        (ν.coeff * (run initial index).nextContact.time.1 *
          initialMass / 2)
        (ν.coeff * initialMass ^ 3 /
          (48 * weightedInitialMass * tangentSq))

/-- Finite physical-time accumulation now generates its own aggregate
persistence scale.  At every requested radius and mass budget, the source
exhausts a larger least core, native nonzero gluing transport, or a
faithful-zero high-frequency family whose explicit charge is settled by the
same successor kinetic ledger. -/
theorem
    elapsedTime_bddAbove_forces_aggregate_frequency_persistence_responsibility
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    ∀ radius : ℕ, ∀ budget : ℝ,
      ∃ index : ℕ,
        ∃ crossed : wholeRestartHalfCriticalCrossed initial index,
          radius <
              wholeRestartCrossingFiniteCoreRadius initial index crossed ∨
            ((wholeRestartCrossingCompleteSourceGluingNegativeOneState
                  initial index crossed ≠ 0 ∧
                (wholeRestartComponentGluingResidualRow
                      initial (index + 1) ≠ 0 ∨
                  linearResidualTrace
                      wholeRestartComponentGluingResidualTailKeep
                      (wholeRestartComponentGluingResidualTail
                        initial index) 0 ≠ 0) ∧
                0 < wholeRestartCrossingTangentPayment initial index) ∨
              Nonempty
                (WholeRestartHighFrequencyAggregatePersistenceReceipt
                  initial index radius crossed budget)) := by
  intro radius budget
  obtain ⟨index, crossed, responsibility⟩ :=
    elapsedTime_bddAbove_forces_aggregate_frequency_responsibility
      initial elapsedBounded radius budget
  refine ⟨index, crossed, ?_⟩
  rcases responsibility with coreEscapes | gluingOrAggregate
  · exact Or.inl coreEscapes
  rcases gluingOrAggregate with gluing | aggregate
  · exact Or.inr (Or.inl gluing)
  rcases aggregate with
    ⟨gluingZero, outputs, outputsGeometry, initialMassLarge,
      actual, aggregateCharge⟩
  have outputsNonzero : ∀ output ∈ outputs, output ≠ 0 :=
    fun output outputMem =>
      (outputsGeometry output outputMem).1
  have initialMassPos :
      0 < ∑ output ∈ outputs,
        complexCoordinateAmplitudeSq
          ((run initial index).contact.physicalState output) :=
    lt_of_le_of_lt (le_max_right budget 0) initialMassLarge
  refine Or.inr (Or.inr ⟨?_⟩)
  exact
    { gluingZero := gluingZero
      outputs := outputs
      outputsGeometry := outputsGeometry
      initialMassLarge := initialMassLarge
      persistenceTimePos :=
        wholeRestartCrossingFiniteAggregatePersistenceTime_pos
          initial index crossed outputs outputsNonzero initialMassPos
      persistenceTimeLt :=
        wholeRestartCrossingFiniteAggregatePersistenceTime_lt_contact
          initial index outputs
      massPersists := fun time timeLe =>
        wholeRestartCrossingFiniteAggregateMass_persists
          initial index crossed outputs outputsNonzero initialMassPos
          time timeLe
      kineticChargePos :=
        wholeRestartCrossingFiniteAggregateKineticCharge_pos
          initial index crossed outputs outputsNonzero initialMassPos
      kineticChargeLe :=
        wholeRestartCrossingFiniteAggregateKineticCharge_le_nextPayment
          initial index crossed outputs outputsNonzero initialMassPos
      kineticChargeRate :=
        wholeRestartCrossingFiniteAggregateKineticCharge_eq_min_rate
          initial index crossed outputs outputsNonzero initialMassPos }

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingHighFrequencyAggregatePersistence
end NavierStokes
end SaturationMonoid
