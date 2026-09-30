import H0mework.NavierStokes.Crossing.TangentCoercivity

/-!
# Quantitative physical-time payment of the whole crossing tangent quantum

The whole `H⁻¹` tangent quantum is consumed before any single-output
projection.  The actual crossing first generates a finite set of nonzero
Fourier rows carrying more than the fixed quantum.  Those exact rows are
then followed along the same unforced prefix receipt, producing a positive
physical-time payment controlled by the receipt's existing whole-tangent
budget.

No Fourier set, output, time window, modulus, cutoff, margin, branch, or
payment certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentQuantumPayment

open scoped BigOperators ENNReal Interval Topology

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity

noncomputable section

/-! ## Pre-quotient continuous tangent rows -/

/-- The actual unforced coefficient row at one nonzero wave, followed along
the same whole prefix receipt as the crossing update. -/
def wholeRestartCrossingContinuousUnforcedTangentRowAt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (actual : ℝ) : ComplexCoordinateVector :=
  let receipt := (run initial index).nextContact.prefixReceipt
  actualWholeContinuousNonlinearRow receipt wave.1 actual -
    (ν.coeff * integerWaveViscousMultiplier wave.1) •
      actualWholeContinuousStateRow receipt wave.1 actual

theorem wholeRestartCrossingContinuousUnforcedTangentRowAt_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    Continuous
      (wholeRestartCrossingContinuousUnforcedTangentRowAt
        initial index wave) := by
  unfold wholeRestartCrossingContinuousUnforcedTangentRowAt
  exact
    (actualWholeContinuousNonlinearRow_continuous
      (run initial index).nextContact.prefixReceipt wave.1).sub
      ((actualWholeContinuousStateRow_continuous
        (run initial index).nextContact.prefixReceipt wave.1).const_smul
          (ν.coeff * integerWaveViscousMultiplier wave.1))

theorem wholeRestartCrossingContinuousUnforcedTangentRowAt_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartCrossingContinuousUnforcedTangentRowAt
        initial index wave 0 =
      wholeRestartCrossingUnforcedTangentRow initial index wave.1 := by
  let receipt := (run initial index).nextContact.prefixReceipt
  have stateAtZero :
      actualWholeContinuousStateRow receipt wave.1 0 =
        (run initial index).contact.physicalState wave.1 := by
    change
      receipt.wholePath
          (Set.projIcc (0 : ℝ)
            (run initial index).nextContact.time.1
            receipt.requestedTimePos.le 0) wave.1 =
        (run initial index).contact.physicalState wave.1
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le
      ⟨le_rfl, receipt.requestedTimePos.le⟩]
    exact congrArg
      (fun state : ComplexVorticityHilbertState => state wave.1)
      receipt.wholePath_initial
  change
    actualWholeContinuousNonlinearRow receipt wave.1 0 -
        (ν.coeff * integerWaveViscousMultiplier wave.1) •
          actualWholeContinuousStateRow receipt wave.1 0 =
      wholeRestartCrossingUnforcedTangentRow initial index wave.1
  rw [actualWholeContinuousNonlinearRow_zero, stateAtZero]
  rfl

/-- The Euclidean coordinate-square density of one inverse-Laplacian
weighted physical tangent row.  The density is kept on the original
coefficient carrier so continuity is inherited directly from the actual
whole receipt. -/
def wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (actual : ℝ) : ℝ :=
  complexCoordinateAmplitudeSq
    (((Real.sqrt (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹) •
      wholeRestartCrossingContinuousUnforcedTangentRowAt
        initial index wave actual)

theorem
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    Continuous
      (wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
        initial index wave) := by
  unfold wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
  exact complexCoordinateAmplitudeSq_continuous.comp
    ((wholeRestartCrossingContinuousUnforcedTangentRowAt_continuous
      initial index wave).const_smul
        ((Real.sqrt
          (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹))

private theorem euclideanCoordinateRow_complex_inv_smul
    (root : ℝ)
    (row : ComplexCoordinateVector) :
    euclideanCoordinateRow (((root : ℂ)⁻¹) • row) =
      root⁻¹ • euclideanCoordinateRow row := by
  ext coordinate
  simp only [euclideanCoordinateRow_apply, Pi.smul_apply, PiLp.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  rfl

theorem
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_zero
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
        initial index wave 0 =
      ‖(puncturedWholeUnforcedNegativeOneEuclideanState
          ν.coeff
          (run initial index).contact.physicalState
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable) wave‖ ^ 2 := by
  unfold wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
  rw [wholeRestartCrossingContinuousUnforcedTangentRowAt_zero]
  unfold wholeRestartCrossingUnforcedTangentRow
  rw [← euclideanCoordinateRow_norm_sq,
    euclideanCoordinateRow_complex_inv_smul]
  simpa [puncturedWholeUnforcedNegativeOneEuclideanCoefficient] using
    congrArg (fun row : ComplexCoordinateEuclidean => ‖row‖)
      (puncturedWholeUnforcedNegativeOneEuclideanState_apply_eq_coefficient
        ν.coeff
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable
        wave).symm

/-! ## A finite source-generated carrier for the fixed quantum -/

/-- Every actual crossing generates a finite set of nonzero Fourier rows
whose time-zero Euclidean `H⁻¹` tangent density already exceeds the same
fixed whole-tangent quantum. -/
theorem exists_wholeRestartCrossingTangentCoerciveModes
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∃ modes : Finset NonzeroIntegerWavevector,
      wholeRestartCrossingTangentCoerciveQuantum ν <
        ∑ wave ∈ modes,
          wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
            initial index wave 0 := by
  let tangent :=
    puncturedWholeUnforcedNegativeOneEuclideanState
      ν.coeff
      (run initial index).contact.physicalState
      (run initial index).contact.transverse
      (run initial index).contact.gradient_summable
  let density : NonzeroIntegerWavevector → ℝ := fun wave =>
    ‖tangent wave‖ ^ 2
  have densitySummable : Summable density := by
    simpa [density] using tangent.2.summable (by norm_num)
  have normEq : ‖tangent‖ ^ 2 = ∑' wave, density wave := by
    simpa [density] using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num) tangent)
  have quantumLtTsum :
      wholeRestartCrossingTangentCoerciveQuantum ν <
        ∑' wave, density wave := by
    rw [← normEq]
    exact wholeRestartCrossing_unforcedTangent_norm_sq_gt_quantum
      initial index crossed
  have eventuallyFinite :
      ∀ᶠ modes : Finset NonzeroIntegerWavevector in atTop,
        wholeRestartCrossingTangentCoerciveQuantum ν <
          ∑ wave ∈ modes, density wave :=
    densitySummable.hasSum.eventually
      (eventually_gt_nhds quantumLtTsum)
  obtain ⟨modes, modesSpec⟩ := eventuallyFinite.exists
  refine ⟨modes, ?_⟩
  calc
    wholeRestartCrossingTangentCoerciveQuantum ν <
        ∑ wave ∈ modes, density wave := modesSpec
    _ = ∑ wave ∈ modes,
        wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
          initial index wave 0 := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      exact
        (wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_zero
          initial index wave).symm

/-- Finite pre-quotient tangent density generated by one set of actual
nonzero wave occurrences. -/
def wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector)
    (actual : ℝ) : ℝ :=
  ∑ wave ∈ modes,
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
      initial index wave actual

theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector) :
    Continuous
      (wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index modes) := by
  unfold wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
  apply continuous_finsetSum
  intro wave waveMem
  exact
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_continuous
      initial index wave

@[simp] theorem
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_empty
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (actual : ℝ) :
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index ∅ actual = 0 := by
  unfold wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
  exact Finset.sum_empty

theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_insert
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector)
    (modes : Finset NonzeroIntegerWavevector)
    (waveNotMem : wave ∉ modes)
    (actual : ℝ) :
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index (insert wave modes) actual =
      wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
          initial index wave actual +
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index modes actual := by
  unfold wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
  rw [Finset.sum_insert waveNotMem]

/-! ## Same-event bridge into the existing whole-tangent budget -/

/-- On the actual prefix interval, every generated nonzero-wave row is the
corresponding coefficient of the receipt's existing whole `H⁻¹` tangent. -/
theorem wholeRestartCrossingContinuousWeightedTangentRowAt_ae_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    let receipt := (run initial index).nextContact.prefixReceipt
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      ((Real.sqrt
        (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹) •
        wholeRestartCrossingContinuousUnforcedTangentRowAt
          initial index wave time.1) =ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time => receipt.wholeTangent time wave.1 := by
  let receipt := (run initial index).nextContact.prefixReceipt
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have sqrtNe :
      (Real.sqrt
        (integerWaveViscousMultiplier wave.1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 multiplierPos).ne'
  filter_upwards [
    actualWholeContinuousNonlinearRow_ae_eq receipt wave.1,
    transverseSpaceTimeNonlinearRow_coeFn
      receipt.transverseLimit wave.1,
    receipt.rowTangent_eq_unforced_ae wave.1 wave.2,
    receipt.rowTangent_eq_wholeTangent_ae wave.1 wave.2] with
      time nonlinearEq representativeEq rowEq tangentEq
  have stateEq :
      actualWholeContinuousStateRow receipt wave.1 time.1 =
        receipt.wholePath time wave.1 := by
    change
      receipt.wholePath
          (Set.projIcc (0 : ℝ)
            (run initial index).nextContact.time.1
            receipt.requestedTimePos.le time.1) wave.1 =
        receipt.wholePath time wave.1
    rw [Set.projIcc_of_mem receipt.requestedTimePos.le time.property]
  change
    ((Real.sqrt
      (integerWaveViscousMultiplier wave.1) : ℂ)⁻¹) •
        (actualWholeContinuousNonlinearRow receipt wave.1 time.1 -
          (ν.coeff * integerWaveViscousMultiplier wave.1) •
            actualWholeContinuousStateRow receipt wave.1 time.1) =
      receipt.wholeTangent time wave.1
  rw [nonlinearEq, representativeEq,
    transverseSpaceTimeNonlinearRowFunction,
    ← wholeStateVorticityBilinearCoefficientAt_self,
    stateEq, ← rowEq, ← tangentEq, smul_smul]
  simp [sqrtNe]

theorem
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_ae_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    let receipt := (run initial index).nextContact.prefixReceipt
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
        initial index wave time.1) =ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time =>
        complexCoordinateAmplitudeSq
          (receipt.wholeTangent time wave.1) := by
  filter_upwards [
    wholeRestartCrossingContinuousWeightedTangentRowAt_ae_eq
      initial index wave] with time rowEq
  unfold
    wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
  rw [rowEq]

/-- The finite generated density keeps all three physical coordinates but
still costs at most three times the existing outer `ℓ²` row norm.  The
factor three is the exact finite-coordinate norm comparison; it is
independent of the number and frequency of generated modes. -/
theorem finiteEuclideanDensity_le_three_mul_lp_norm_sq
    (state :
      lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2)
    (modes : Finset NonzeroIntegerWavevector) :
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave.1)) ≤
      3 * ‖state‖ ^ 2 := by
  have fullSummable :
      Summable fun output : IntegerWavevector => ‖state output‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      Memℓp.summable (by norm_num) state.2
  have restrictedSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        ‖state wave.1‖ ^ 2 := by
    change Summable
      ((fun output : IntegerWavevector => ‖state output‖ ^ 2) ∘
        Subtype.val)
    exact fullSummable.subtype {output | output ≠ 0}
  have restrictedTsumLe :
      (∑' wave : NonzeroIntegerWavevector, ‖state wave.1‖ ^ 2) ≤
        ∑' output : IntegerWavevector, ‖state output‖ ^ 2 := by
    change
      tsum ((fun output : IntegerWavevector => ‖state output‖ ^ 2) ∘
          Subtype.val) ≤
        tsum (fun output : IntegerWavevector => ‖state output‖ ^ 2)
    exact tsum_comp_le_tsum_of_inj fullSummable
      (fun output => sq_nonneg ‖state output‖)
      Subtype.val_injective
  have normEq :
      ‖state‖ ^ 2 =
        ∑' output : IntegerWavevector, ‖state output‖ ^ 2 := by
    simpa using
      (lp.norm_rpow_eq_tsum
        (p := (2 : ℝ≥0∞)) (by norm_num) state)
  calc
    (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave.1)) ≤
        ∑ wave ∈ modes, 3 * ‖state wave.1‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro wave waveMem
      exact complexCoordinateAmplitudeSq_le_three_mul_norm_sq
        (state wave.1)
    _ ≤ ∑' wave : NonzeroIntegerWavevector,
        3 * ‖state wave.1‖ ^ 2 :=
      (restrictedSummable.mul_left 3).sum_le_tsum modes
        (fun wave waveMem => mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 3 *
        (∑' wave : NonzeroIntegerWavevector,
          ‖state wave.1‖ ^ 2) := by
      rw [tsum_mul_left]
    _ ≤ 3 *
        (∑' output : IntegerWavevector, ‖state output‖ ^ 2) :=
      mul_le_mul_of_nonneg_left restrictedTsumLe (by norm_num)
    _ = 3 * ‖state‖ ^ 2 := by rw [normEq]

/-- The complete finite density is almost everywhere the same generated
finite row sum inside the actual whole-tangent receipt. -/
theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_ae_eq
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector) :
    let receipt := (run initial index).nextContact.prefixReceipt
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index modes time.1) =ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time =>
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
            (receipt.wholeTangent time wave.1) := by
  induction modes using Finset.induction_on with
  | empty =>
      exact Filter.Eventually.of_forall fun time => by
        calc
          wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
              initial index ∅ time.1 = 0 :=
            wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_empty
              initial index time.1
          _ = ∑ wave ∈ (∅ : Finset NonzeroIntegerWavevector),
              complexCoordinateAmplitudeSq
                ((run initial index).nextContact.prefixReceipt.wholeTangent
                  time wave.1) := Finset.sum_empty.symm
  | @insert wave modes waveNotMem ih =>
      filter_upwards [
        wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt_ae_eq
          initial index wave,
        ih] with time rowEq tailEq
      calc
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
            initial index (insert wave modes) time.1 =
          wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
                initial index wave time.1 +
              wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
                initial index modes time.1 :=
          wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_insert
            initial index wave modes waveNotMem time.1
        _ = complexCoordinateAmplitudeSq
                ((run initial index).nextContact.prefixReceipt.wholeTangent
                  time wave.1) +
              ∑ later ∈ modes,
                complexCoordinateAmplitudeSq
                  ((run initial index).nextContact.prefixReceipt.wholeTangent
                    time later.1) := by
          exact congrArg₂ (· + ·) rowEq tailEq
        _ = ∑ later ∈ insert wave modes,
              complexCoordinateAmplitudeSq
                ((run initial index).nextContact.prefixReceipt.wholeTangent
                  time later.1) := by
          exact
            (Finset.sum_insert
              (f := fun later : NonzeroIntegerWavevector =>
                complexCoordinateAmplitudeSq
                  ((run initial index).nextContact.prefixReceipt.wholeTangent
                    time later.1))
              waveNotMem).symm

theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_ae_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector) :
    let receipt := (run initial index).nextContact.prefixReceipt
    (fun time : Icc (0 : ℝ) (run initial index).nextContact.time.1 =>
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
        initial index modes time.1) ≤ᵐ[
      commonTimeMeasure (run initial index).nextContact.time.1]
      fun time => 3 * ‖receipt.wholeTangent time‖ ^ 2 := by
  filter_upwards [
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_ae_eq
      initial index modes] with time densityEq
  rw [densityEq]
  exact finiteEuclideanDensity_le_three_mul_lp_norm_sq
    ((run initial index).nextContact.prefixReceipt.wholeTangent time)
    modes

theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_nonneg
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector)
    (actual : ℝ) :
    0 ≤ wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index modes actual := by
  unfold wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
  exact Finset.sum_nonneg fun wave waveMem => by
    unfold
      wholeRestartCrossingContinuousUnforcedTangentEuclideanDensityAt
    exact complexCoordinateAmplitudeSq_nonneg _

/-- The generated finite Euclidean density is paid by the actual receipt's
already existing whole `L²_t H⁻¹_x` tangent budget. -/
theorem wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_integral_le
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (modes : Finset NonzeroIntegerWavevector) :
    (∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index modes time) ≤
      3 *
        ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  let receipt := (run initial index).nextContact.prefixReceipt
  let duration := (run initial index).nextContact.time.1
  let density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index modes
  have durationPos : 0 < duration := receipt.requestedTimePos
  have densityContinuous : Continuous density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
      initial index modes
  have densityMeasurable :
      AEStronglyMeasurable
        (fun time : Icc (0 : ℝ) duration => density time.1)
        (commonTimeMeasure duration) :=
    (densityContinuous.comp continuous_subtype_val).aestronglyMeasurable
  have tangentSqIntegrable :
      Integrable
        (fun time => ‖receipt.wholeTangent time‖ ^ 2)
        (commonTimeMeasure duration) :=
    (MeasureTheory.Lp.memLp receipt.wholeTangent).integrable_norm_pow
      (by norm_num)
  have threeTangentSqIntegrable :
      Integrable
        (fun time => 3 * ‖receipt.wholeTangent time‖ ^ 2)
        (commonTimeMeasure duration) :=
    tangentSqIntegrable.const_mul 3
  have densityAELe :
      (fun time : Icc (0 : ℝ) duration => density time.1) ≤ᵐ[
        commonTimeMeasure duration]
        fun time => 3 * ‖receipt.wholeTangent time‖ ^ 2 := by
    simpa only [density, duration, receipt] using
      (wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_ae_le
        initial index modes)
  have densityIntegrable :
      Integrable
        (fun time : Icc (0 : ℝ) duration => density time.1)
        (commonTimeMeasure duration) := by
    apply threeTangentSqIntegrable.mono' densityMeasurable
    filter_upwards [densityAELe] with time bound
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_nonneg
          initial index modes time.1)]
    simpa only [Set.mem_setOf_eq, density, duration, receipt] using bound
  have integralLe :
      (∫ time : Icc (0 : ℝ) duration,
          density time.1 ∂(commonTimeMeasure duration)) ≤
        ∫ time : Icc (0 : ℝ) duration,
          3 * ‖receipt.wholeTangent time‖ ^ 2
            ∂(commonTimeMeasure duration) :=
    integral_mono_ae densityIntegrable threeTangentSqIntegrable densityAELe
  calc
    (∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
          initial index modes time) =
        ∫ time : Icc (0 : ℝ) duration,
          density time.1 ∂(commonTimeMeasure duration) := by
      exact
        (commonTime_integral_eq_intervalIntegral
          duration durationPos.le density).symm
    _ ≤ ∫ time : Icc (0 : ℝ) duration,
          3 * ‖receipt.wholeTangent time‖ ^ 2
            ∂(commonTimeMeasure duration) := integralLe
    _ = 3 *
        (∫ time : Icc (0 : ℝ) duration,
          ‖receipt.wholeTangent time‖ ^ 2
            ∂(commonTimeMeasure duration)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = 3 * ‖receipt.wholeTangent‖ ^ 2 := by
      rw [spaceTime_norm_sq_eq_integral]
    _ = 3 *
        ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 :=
      rfl

/-! ## Source-generated quantitative positive-time payment -/

/-- Every actual crossing internally generates a finite pre-quotient
Fourier carrier and a positive physical-time window on which at least half
of the fixed whole-tangent quantum is paid.  The entire payment is charged
once to the same actual whole receipt. -/
theorem wholeRestartCrossingTangentQuantum_positiveTimePayment
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∃ modes : Finset NonzeroIntegerWavevector,
      ∃ localTime : ℝ,
        wholeRestartCrossingTangentCoerciveQuantum ν <
            wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
              initial index modes 0 ∧
          0 < localTime ∧
          localTime < (run initial index).nextContact.time.1 ∧
          localTime *
                (wholeRestartCrossingTangentCoerciveQuantum ν / 2) ≤
            ∫ time in (0 : ℝ)..localTime,
              wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
                initial index modes time ∧
          0 <
            ∫ time in (0 : ℝ)..localTime,
              wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
                initial index modes time ∧
          (∫ time in (0 : ℝ)..localTime,
              wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
                initial index modes time) ≤
            3 *
              ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
  obtain ⟨modes, modesZeroGt⟩ :=
    exists_wholeRestartCrossingTangentCoerciveModes initial index crossed
  let density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity
      initial index modes
  let quantum := wholeRestartCrossingTangentCoerciveQuantum ν
  have densityZeroGt : quantum < density 0 := by
    simpa only [quantum, density,
      wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity] using
        modesZeroGt
  have densityContinuous : Continuous density :=
    wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_continuous
      initial index modes
  have quantumPos : 0 < quantum :=
    wholeRestartCrossingTangentCoerciveQuantum_pos ν
  have halfQuantumPos : 0 < quantum / 2 := by linarith
  have halfQuantumLtZeroDensity : quantum / 2 < density 0 := by
    linarith
  have eventuallyLower :
      ∀ᶠ time in 𝓝 (0 : ℝ), quantum / 2 < density time :=
    densityContinuous.continuousAt.eventually
      (eventually_gt_nhds halfQuantumLtZeroDensity)
  obtain ⟨liveRadius, liveRadiusPos, liveWithin⟩ :=
    Metric.eventually_nhds_iff.mp eventuallyLower
  let localTime :=
    min (run initial index).nextContact.time.1 liveRadius / 2
  have receiptTimePos :
      0 < (run initial index).nextContact.time.1 :=
    (run initial index).nextContact.prefixReceipt.requestedTimePos
  have commonRadiusPos :
      0 < min (run initial index).nextContact.time.1 liveRadius :=
    lt_min receiptTimePos liveRadiusPos
  have localTimePos : 0 < localTime := by
    dsimp [localTime]
    linarith
  have localTimeLtCommon :
      localTime <
        min (run initial index).nextContact.time.1 liveRadius := by
    dsimp [localTime]
    linarith
  have localTimeLtReceipt :
      localTime < (run initial index).nextContact.time.1 :=
    lt_of_lt_of_le localTimeLtCommon (min_le_left _ _)
  have localTimeLtLive : localTime < liveRadius :=
    lt_of_lt_of_le localTimeLtCommon (min_le_right _ _)
  have pointwiseLower :
      ∀ time ∈ Icc (0 : ℝ) localTime,
        quantum / 2 ≤ density time := by
    intro time timeMem
    exact (liveWithin (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg timeMem.1]
      exact timeMem.2.trans_lt localTimeLtLive)).le
  have densityIntegrableLocal :
      IntervalIntegrable density volume 0 localTime :=
    densityContinuous.intervalIntegrable 0 localTime
  have constantIntegrable :
      IntervalIntegrable
        (fun _ : ℝ => quantum / 2) volume 0 localTime :=
    continuous_const.intervalIntegrable 0 localTime
  have integratedLower :=
    intervalIntegral.integral_mono_on
      localTimePos.le constantIntegrable densityIntegrableLocal
      pointwiseLower
  have normalizedLower :
      localTime * (quantum / 2) ≤
        ∫ time in (0 : ℝ)..localTime, density time := by
    calc
      localTime * (quantum / 2) = localTime * quantum / 2 := by ring
      _ ≤ ∫ time in (0 : ℝ)..localTime, density time := by
        simpa [intervalIntegral.integral_const, smul_eq_mul] using
          integratedLower
  have integralPositive :
      0 < ∫ time in (0 : ℝ)..localTime, density time :=
    (mul_pos localTimePos halfQuantumPos).trans_le normalizedLower
  have densityIntegrableFull :
      IntervalIntegrable density volume 0
        (run initial index).nextContact.time.1 :=
    densityContinuous.intervalIntegrable
      0 (run initial index).nextContact.time.1
  have localIntegralLeFull :
      (∫ time in (0 : ℝ)..localTime, density time) ≤
        ∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
          density time :=
    intervalIntegral.integral_mono_interval
      (μ := volume)
      (c := (0 : ℝ))
      (d := (run initial index).nextContact.time.1)
      le_rfl localTimePos.le localTimeLtReceipt.le
      (Filter.Eventually.of_forall fun time =>
        wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_nonneg
          initial index modes time)
      densityIntegrableFull
  have fullIntegralLe :
      (∫ time in (0 : ℝ)..(run initial index).nextContact.time.1,
          density time) ≤
        3 *
          ‖(run initial index).nextContact.prefixReceipt.wholeTangent‖ ^ 2 := by
    simpa only [density] using
      (wholeRestartCrossingFiniteUnforcedTangentEuclideanDensity_integral_le
        initial index modes)
  refine ⟨modes, localTime, ?_, localTimePos, localTimeLtReceipt,
    ?_, integralPositive, ?_⟩
  · simpa only [density, quantum] using densityZeroGt
  · simpa only [density, quantum] using normalizedLower
  · simpa only [density] using localIntegralLeFull.trans fullIntegralLe

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentQuantumPayment
end NavierStokes
end SaturationMonoid
