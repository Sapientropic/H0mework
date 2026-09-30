import H0mework.NavierStokes.Crossing.TangentPaymentCascade

/-!
# Coercivity of the actual whole unforced tangent at a restart crossing

The complete coordinate row is placed in the genuine Euclidean `ℓ²` carrier
before any single-output observation is selected.  Exact whole nonlinear
kinetic cancellation then measures the unforced tangent against the same
physical state and produces a quantitative lower bound at every actual
half-critical crossing.

No Fourier cutoff, output, modulus, branch, margin, or lower-bound
certificate is accepted from a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity

open scoped BigOperators ENNReal ComplexConjugate

open Set
open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeViscousNegativeOne
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
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
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingUnforcedTangentPayment
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentPaymentCascade

noncomputable section

/-! ## Exact Euclideanization of the three coordinate rows -/

/-- The physical three-coordinate row with its Euclidean, rather than
supremum, norm. -/
abbrev ComplexCoordinateEuclidean := EuclideanSpace ℂ Coordinate

/-- Identity on coordinates, changing only the finite-dimensional norm. -/
def euclideanCoordinateRow
    (row : ComplexCoordinateVector) : ComplexCoordinateEuclidean :=
  WithLp.toLp 2 row

@[simp] theorem euclideanCoordinateRow_apply
    (row : ComplexCoordinateVector)
    (coordinate : Coordinate) :
    euclideanCoordinateRow row coordinate = row coordinate := rfl

theorem euclideanCoordinateRow_norm_sq
    (row : ComplexCoordinateVector) :
    ‖euclideanCoordinateRow row‖ ^ 2 =
      complexCoordinateAmplitudeSq row := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [euclideanCoordinateRow, complexCoordinateAmplitudeSq,
    Complex.sq_norm]

/-- The Euclidean coordinate inner product is exactly the physical real
Hermitian row pairing already used by the kinetic cancellation ledger. -/
theorem euclideanCoordinateRow_re_inner
    (left right : ComplexCoordinateVector) :
    (inner ℂ (euclideanCoordinateRow left)
        (euclideanCoordinateRow right)).re =
      complexCoordinateRealInner left right := by
  rw [EuclideanSpace.inner_toLp_toLp,
    complexCoordinateRealInner_eq_re_dot]
  simp [euclideanCoordinateRow, vectorConj, dotProduct, mul_comm]

/-- Restrict one actual whole coefficient `ℓ²` state to nonzero waves
and install the exact Euclidean norm on its finite coordinate rows. -/
def puncturedEuclideanize
    (state : lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2) :
    lp (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  ⟨fun wave => euclideanCoordinateRow (state wave.1), by
    apply memℓp_gen
    have fullSummable :
        Summable fun wave : IntegerWavevector => ‖state wave‖ ^ (2 : ℝ) :=
      state.2.summable (by norm_num)
    have restrictedSummable :
        Summable fun wave : NonzeroIntegerWavevector =>
          ‖state wave.1‖ ^ (2 : ℝ) := by
      change Summable
        ((fun wave : IntegerWavevector =>
          ‖state wave‖ ^ (2 : ℝ)) ∘ Subtype.val)
      exact fullSummable.subtype {wave | wave ≠ 0}
    have majorantSummable :
        Summable fun wave : NonzeroIntegerWavevector =>
          3 * ‖state wave.1‖ ^ (2 : ℝ) :=
      restrictedSummable.mul_left 3
    exact majorantSummable.of_nonneg_of_le
      (fun wave => by positivity)
      (fun wave => by
        norm_num
        rw [euclideanCoordinateRow_norm_sq]
        exact complexCoordinateAmplitudeSq_le_three_mul_norm_sq
          (state wave.1))⟩

@[simp] theorem puncturedEuclideanize_apply
    (state : lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2)
    (wave : NonzeroIntegerWavevector) :
    puncturedEuclideanize state wave =
      euclideanCoordinateRow (state wave.1) := rfl

theorem puncturedEuclideanize_norm_sq
    (state : lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2) :
    ‖puncturedEuclideanize state‖ ^ 2 =
      ∑' wave : NonzeroIntegerWavevector,
        complexCoordinateAmplitudeSq (state wave.1) := by
  rw [show
    ‖puncturedEuclideanize state‖ ^ 2 =
      ∑' wave : NonzeroIntegerWavevector,
        ‖puncturedEuclideanize state wave‖ ^ 2 by
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (puncturedEuclideanize state))]
  apply tsum_congr
  intro wave
  exact euclideanCoordinateRow_norm_sq (state wave.1)

/-- The complete Euclidean restriction is bounded on the original whole
Fourier carrier.  The factor three is forced by the three physical
coordinates; no finite-mode cutoff enters the estimate. -/
theorem puncturedEuclideanize_norm_sq_le
    (state : lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2) :
    ‖puncturedEuclideanize state‖ ^ 2 ≤ 3 * ‖state‖ ^ 2 := by
  have restrictedSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        complexCoordinateAmplitudeSq (state wave.1) := by
    simpa only [← euclideanCoordinateRow_norm_sq,
      ENNReal.toReal_ofNat, Real.rpow_two,
      puncturedEuclideanize_apply] using
      (puncturedEuclideanize state).2.summable (by norm_num)
  have stateNormSummable :
      Summable fun wave : IntegerWavevector => ‖state wave‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      state.2.summable (by norm_num)
  have fullSummable :
      Summable fun wave : IntegerWavevector => 3 * ‖state wave‖ ^ 2 :=
    stateNormSummable.mul_left 3
  rw [puncturedEuclideanize_norm_sq]
  calc
    (∑' wave : NonzeroIntegerWavevector,
        complexCoordinateAmplitudeSq (state wave.1)) ≤
        ∑' wave : NonzeroIntegerWavevector,
          3 * ‖state wave.1‖ ^ 2 :=
      restrictedSummable.tsum_le_tsum
        (fun wave =>
          complexCoordinateAmplitudeSq_le_three_mul_norm_sq
            (state wave.1))
        (fullSummable.subtype {wave | wave ≠ 0})
    _ ≤ ∑' wave : IntegerWavevector, 3 * ‖state wave‖ ^ 2 :=
      Summable.tsum_subtype_le
        (fun wave : IntegerWavevector => 3 * ‖state wave‖ ^ 2)
        {wave : IntegerWavevector | wave ≠ 0}
        (fun wave => mul_nonneg (by norm_num) (sq_nonneg ‖state wave‖))
        fullSummable
    _ = 3 * ‖state‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num) state).symm

theorem puncturedEuclideanize_sub
    (left right :
      lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2) :
    puncturedEuclideanize (left - right) =
      puncturedEuclideanize left - puncturedEuclideanize right := by
  apply lp.ext
  funext wave
  rfl

/-- Consequently the full nonzero-wave physical readout is continuous
before any endpoint or finite-observation quotient is taken. -/
theorem continuous_puncturedEuclideanize :
    Continuous puncturedEuclideanize := by
  rw [continuous_iff_continuousAt]
  intro state
  rw [Metric.continuousAt_iff]
  intro epsilon epsilonPos
  refine ⟨epsilon / 2, half_pos epsilonPos, ?_⟩
  intro current currentClose
  rw [dist_eq_norm, ← puncturedEuclideanize_sub]
  have sourceClose : ‖current - state‖ < epsilon / 2 := by
    simpa only [dist_eq_norm] using currentClose
  have squareLe := puncturedEuclideanize_norm_sq_le (current - state)
  nlinarith [norm_nonneg (puncturedEuclideanize (current - state)),
    norm_nonneg (current - state)]

/-! ## Kinetic test state on the same punctured Hilbert carrier -/

/-- Inverse-square-root Laplacian weighting of the actual vorticity row. -/
def puncturedWholeVorticityKineticEuclideanCoefficient
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateEuclidean :=
  (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
    euclideanCoordinateRow (state wave.1)

theorem puncturedWholeVorticityKineticEuclideanCoefficient_norm_sq
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) :
    ‖puncturedWholeVorticityKineticEuclideanCoefficient state wave‖ ^ 2 =
      complexCoordinateAmplitudeSq (state wave.1) /
        integerWaveViscousMultiplier wave.1 := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave.1) :=
    Real.sqrt_pos.2 multiplierPos
  let row : ComplexCoordinateVector := state wave.1
  change
    ‖(Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow row‖ ^ 2 =
      complexCoordinateAmplitudeSq row /
        integerWaveViscousMultiplier wave.1
  have scalarNormSq :
      ‖(Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹‖ ^ 2 =
        1 / integerWaveViscousMultiplier wave.1 := by
    rw [norm_inv, Real.norm_eq_abs, abs_of_pos sqrtPos, inv_pow,
      Real.sq_sqrt multiplierPos.le]
    simp only [one_div]
  have rowNormSq :
      ‖euclideanCoordinateRow row‖ ^ 2 =
        complexCoordinateAmplitudeSq row :=
    euclideanCoordinateRow_norm_sq row
  rw [norm_smul]
  calc
    (‖(Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹‖ *
        ‖euclideanCoordinateRow row‖) ^ 2 =
        ‖(Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹‖ ^ 2 *
          ‖euclideanCoordinateRow row‖ ^ 2 := by ring
    _ = (1 / integerWaveViscousMultiplier wave.1) *
          complexCoordinateAmplitudeSq row := by
      rw [scalarNormSq, rowNormSq]
    _ = complexCoordinateAmplitudeSq row /
          integerWaveViscousMultiplier wave.1 := by ring

/-- The complete physical vorticity row in the kinetic `H⁻¹` test
carrier.  Membership follows from the integer-lattice spectral gap. -/
def puncturedWholeVorticityKineticEuclideanState
    (state : ComplexVorticityHilbertState) :
    lp (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  ⟨puncturedWholeVorticityKineticEuclideanCoefficient state, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (summable_puncturedWholeVorticityKineticMass state).congr
        (fun wave =>
          (puncturedWholeVorticityKineticEuclideanCoefficient_norm_sq
            state wave).symm)⟩

@[simp] theorem puncturedWholeVorticityKineticEuclideanState_apply
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) :
    puncturedWholeVorticityKineticEuclideanState state wave =
      puncturedWholeVorticityKineticEuclideanCoefficient state wave := rfl

theorem puncturedWholeVorticityKineticEuclideanState_norm_sq
    (state : ComplexVorticityHilbertState) :
    ‖puncturedWholeVorticityKineticEuclideanState state‖ ^ 2 =
      puncturedWholeVorticityKineticMass state := by
  rw [show
    ‖puncturedWholeVorticityKineticEuclideanState state‖ ^ 2 =
      ∑' wave : NonzeroIntegerWavevector,
        ‖puncturedWholeVorticityKineticEuclideanState state wave‖ ^ 2 by
      simpa using
        (lp.norm_rpow_eq_tsum
          (p := (2 : ℝ≥0∞)) (by norm_num)
          (puncturedWholeVorticityKineticEuclideanState state))]
  unfold puncturedWholeVorticityKineticMass
  apply tsum_congr
  intro wave
  exact
    puncturedWholeVorticityKineticEuclideanCoefficient_norm_sq state wave

/-! ## The actual whole unforced tangent on the same carrier -/

/-- The genuine whole unforced vorticity tangent after the exact
inverse-square-root Laplacian weight.  Both summands are existing whole
Navier--Stokes states; Euclideanization changes only the finite coordinate
norm before the punctured restriction. -/
def puncturedWholeUnforcedNegativeOneEuclideanState
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    lp (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 :=
  puncturedEuclideanize
    (wholeStateVorticityNonlinearNegativeOneState
        state stateTransverse gradientSummable -
      wholeStateVorticityViscousNegativeOneState
        viscosity state gradientSummable)

@[simp] theorem puncturedWholeUnforcedNegativeOneEuclideanState_apply
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (wave : NonzeroIntegerWavevector) :
    puncturedWholeUnforcedNegativeOneEuclideanState
        viscosity state stateTransverse gradientSummable wave =
      euclideanCoordinateRow
        (wholeStateVorticityNonlinearNegativeOneWeightedCoefficient
            state wave.1 -
          wholeStateVorticityViscousNegativeOneWeightedCoefficient
            viscosity state wave.1) := rfl

/-- The same weighted tangent written directly from the physical unforced
Fourier row. -/
def puncturedWholeUnforcedNegativeOneEuclideanCoefficient
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) : ComplexCoordinateEuclidean :=
  (Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
    euclideanCoordinateRow
      (wholeStateVorticityNonlinearCoefficientAt state wave.1 -
        (viscosity * integerWaveViscousMultiplier wave.1) •
          state wave.1)

/-- Existing whole negative-one states and the direct physical tangent
formula are the same coefficient on every actual nonzero wave. -/
theorem puncturedWholeUnforcedNegativeOneEuclideanState_apply_eq_coefficient
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave))
    (wave : NonzeroIntegerWavevector) :
    puncturedWholeUnforcedNegativeOneEuclideanState
        viscosity state stateTransverse gradientSummable wave =
      puncturedWholeUnforcedNegativeOneEuclideanCoefficient
        viscosity state wave := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave.1) :=
    Real.sqrt_pos.2 multiplierPos
  ext coordinate
  simp only [puncturedWholeUnforcedNegativeOneEuclideanState_apply,
    puncturedWholeUnforcedNegativeOneEuclideanCoefficient,
    euclideanCoordinateRow_apply,
    wholeStateVorticityNonlinearNegativeOneWeightedCoefficient,
    wholeStateVorticityViscousNegativeOneWeightedCoefficient,
    if_neg wave.2, Pi.sub_apply, Pi.smul_apply,
    PiLp.smul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_eq_mul]
  generalize hNonlinear :
    wholeStateVorticityNonlinearCoefficientAt state wave.1 coordinate =
      nonlinearCoordinate
  generalize hState : state wave.1 coordinate = stateCoordinate
  generalize hMultiplier :
    integerWaveViscousMultiplier wave.1 = multiplier at *
  generalize hRoot : Real.sqrt multiplier = root at *
  push_cast
  field_simp [sqrtPos.ne']
  have sqrtSqComplex :
      (root : ℂ) ^ 2 = (multiplier : ℂ) := by
    norm_cast
    rw [← hRoot]
    exact Real.sq_sqrt multiplierPos.le
  change
    nonlinearCoordinate -
        (root : ℂ) ^ 2 * (viscosity : ℂ) * stateCoordinate =
      nonlinearCoordinate -
        (viscosity : ℂ) * stateCoordinate * (multiplier : ℂ)
  calc
    nonlinearCoordinate -
        (root : ℂ) ^ 2 * (viscosity : ℂ) * stateCoordinate =
      nonlinearCoordinate -
        (multiplier : ℂ) * (viscosity : ℂ) * stateCoordinate := by
      rw [sqrtSqComplex]
    _ = nonlinearCoordinate -
        (viscosity : ℂ) * stateCoordinate * (multiplier : ℂ) := by
      ring

/-- Pointwise kinetic testing of the actual weighted tangent is the
nonlinear kinetic work minus the exact viscous vorticity mass. -/
theorem puncturedKinetic_unforcedNegativeOne_re_inner_eq
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (wave : NonzeroIntegerWavevector) :
    (inner ℂ
        (puncturedWholeVorticityKineticEuclideanCoefficient state wave)
        (puncturedWholeUnforcedNegativeOneEuclideanCoefficient
          viscosity state wave)).re =
      complexCoordinateRealInner
          (state wave.1)
          (wholeStateVorticityNonlinearCoefficientAt state wave.1) /
        integerWaveViscousMultiplier wave.1 -
      viscosity * complexCoordinateAmplitudeSq (state wave.1) := by
  have multiplierPos :
      0 < integerWaveViscousMultiplier wave.1 :=
    integerWaveViscousMultiplier_pos wave
  have multiplierNe :
      integerWaveViscousMultiplier wave.1 ≠ 0 :=
    multiplierPos.ne'
  have sqrtPos :
      0 < Real.sqrt (integerWaveViscousMultiplier wave.1) :=
    Real.sqrt_pos.2 multiplierPos
  change
    (inner ℂ
      ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow (state wave.1))
      ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow
          (wholeStateVorticityNonlinearCoefficientAt state wave.1 -
            (viscosity * integerWaveViscousMultiplier wave.1) •
              state wave.1))).re = _
  generalize hStateRow : state wave.1 = stateRow at *
  generalize hNonlinearRow :
    wholeStateVorticityNonlinearCoefficientAt state wave.1 =
      nonlinearRow at *
  generalize hMultiplier :
    integerWaveViscousMultiplier wave.1 = multiplier at *
  generalize hRoot : Real.sqrt multiplier = root at *
  generalize hInverseRoot : root⁻¹ = inverseRoot at *
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [inner_smul_left, inner_smul_right]
  generalize hRowInner :
    inner ℂ (euclideanCoordinateRow stateRow)
        (euclideanCoordinateRow
          (nonlinearRow - (viscosity * multiplier) • stateRow)) =
      rowInner at *
  have conjugateScalar :
      starRingEnd ℂ (inverseRoot : ℂ) = (inverseRoot : ℂ) := by
    simp
  have normalizedProduct :
      starRingEnd ℂ (inverseRoot : ℂ) *
          ((inverseRoot : ℂ) * rowInner) =
        ((inverseRoot : ℂ) * (inverseRoot : ℂ)) * rowInner := by
    calc
      starRingEnd ℂ (inverseRoot : ℂ) *
          ((inverseRoot : ℂ) * rowInner) =
        (inverseRoot : ℂ) * ((inverseRoot : ℂ) * rowInner) :=
          congrArg
            (fun scalar : ℂ => scalar * ((inverseRoot : ℂ) * rowInner))
            conjugateScalar
      _ = ((inverseRoot : ℂ) * (inverseRoot : ℂ)) * rowInner := by
        ring
  have scalarSquare :
      (inverseRoot : ℂ) * (inverseRoot : ℂ) =
        ((1 / multiplier : ℝ) : ℂ) := by
    norm_cast
    rw [← hInverseRoot, ← hRoot]
    field_simp [sqrtPos.ne', multiplierNe]
    rw [Real.sq_sqrt multiplierPos.le]
  have rowInnerRe :
      rowInner.re =
        complexCoordinateRealInner stateRow
          (nonlinearRow - (viscosity * multiplier) • stateRow) := by
    calc
      rowInner.re =
          (inner ℂ (euclideanCoordinateRow stateRow)
            (euclideanCoordinateRow
              (nonlinearRow -
                (viscosity * multiplier) • stateRow))).re :=
        congrArg Complex.re hRowInner.symm
      _ = complexCoordinateRealInner stateRow
          (nonlinearRow - (viscosity * multiplier) • stateRow) :=
        euclideanCoordinateRow_re_inner _ _
  calc
    (starRingEnd ℂ (inverseRoot : ℂ) *
        ((inverseRoot : ℂ) * rowInner)).re =
      (((inverseRoot : ℂ) * (inverseRoot : ℂ)) * rowInner).re :=
        congrArg Complex.re normalizedProduct
    _ = (((1 / multiplier : ℝ) : ℂ) * rowInner).re := by
      rw [scalarSquare]
    _ = (1 / multiplier) * rowInner.re := by
      rw [Complex.mul_re]
      simp
    _ = complexCoordinateRealInner stateRow nonlinearRow / multiplier -
        viscosity * complexCoordinateAmplitudeSq stateRow := by
      rw [rowInnerRe, complexCoordinateRealInner_sub_right,
        complexCoordinateRealInner_real_smul_right,
        complexCoordinateRealInner_self,
        ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      field_simp [multiplierNe]

/-! ## Exact whole kinetic pairing and coercivity -/

private theorem zero_whole_gradient_summable :
    Summable fun wave : IntegerWavevector =>
      integerWaveNormSq wave *
        complexCoordinateAmplitudeSq
          ((0 : ComplexVorticityHilbertState) wave) := by
  simp [complexCoordinateAmplitudeSq]

/-- Exact nonlinear cancellation turns kinetic testing of the actual whole
unforced tangent into the negative viscous vorticity mass. -/
theorem puncturedWholeUnforcedNegativeOneEuclideanState_kineticPairing
    (viscosity : ℝ)
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (stateTransverse : WholeStateTransverse state)
    (stateReality : FiniteStateFourierReality state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    (inner ℂ
        (puncturedWholeVorticityKineticEuclideanState state)
        (puncturedWholeUnforcedNegativeOneEuclideanState
          viscosity state stateTransverse gradientSummable)).re =
      -viscosity * wholeVorticityEuclideanMass state := by
  let kineticState :=
    puncturedWholeVorticityKineticEuclideanState state
  let tangentState :=
    puncturedWholeUnforcedNegativeOneEuclideanState
      viscosity state stateTransverse gradientSummable
  let nonlinearWork : NonzeroIntegerWavevector → ℝ :=
    fun wave =>
      complexCoordinateRealInner
          (state wave.1)
          (wholeStateVorticityNonlinearCoefficientAt state wave.1) /
        integerWaveViscousMultiplier wave.1
  let viscousMass : NonzeroIntegerWavevector → ℝ :=
    fun wave =>
      viscosity * complexCoordinateAmplitudeSq (state wave.1)
  have innerSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        inner ℂ (kineticState wave) (tangentState wave) :=
    (lp.hasSum_inner kineticState tangentState).summable
  have combinedSummable :
      Summable fun wave : NonzeroIntegerWavevector =>
        nonlinearWork wave - viscousMass wave := by
    have realInnerSummable :
        Summable fun wave : NonzeroIntegerWavevector =>
          (inner ℂ (kineticState wave) (tangentState wave)).re := by
      apply Summable.of_norm
      exact innerSummable.norm.of_nonneg_of_le
        (fun wave => norm_nonneg _)
        (fun wave => RCLike.norm_re_le_norm
          (inner ℂ (kineticState wave) (tangentState wave)))
    exact realInnerSummable.congr fun wave => by
      simp only [kineticState, tangentState]
      rw [puncturedWholeVorticityKineticEuclideanState_apply,
        puncturedWholeUnforcedNegativeOneEuclideanState_apply_eq_coefficient]
      exact puncturedKinetic_unforcedNegativeOne_re_inner_eq
        viscosity state wave
  have viscousMassSummable : Summable viscousMass := by
    exact
      (summable_puncturedWholeVorticityEuclideanMass state).mul_left
        viscosity
  have nonlinearWorkSummable : Summable nonlinearWork := by
    exact (combinedSummable.add viscousMassSummable).congr fun wave => by
      simp only [nonlinearWork, viscousMass]
      ring
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
  have nonlinearWorkTsum : (∑' wave, nonlinearWork wave) = 0 := by
    have pairingTsum : pairing = ∑' wave, nonlinearWork wave := by
      simpa [pairing, nonlinearWork, nonlinearAtZero] using
        wholeStateVorticityNonlinearDifferenceKineticPairing_eq_tsum
          state 0 stateTransverse wholeStateTransverse_zero
          gradientSummable zero_whole_gradient_summable
    rw [← pairingTsum, pairingZero]
  have innerAsTsum :
      (inner ℂ kineticState tangentState).re =
        ∑' wave, (nonlinearWork wave - viscousMass wave) := by
    rw [lp.inner_eq_tsum, Complex.re_tsum innerSummable]
    apply tsum_congr
    intro wave
    simp only [kineticState, tangentState]
    rw [puncturedWholeVorticityKineticEuclideanState_apply,
      puncturedWholeUnforcedNegativeOneEuclideanState_apply_eq_coefficient]
    exact puncturedKinetic_unforcedNegativeOne_re_inner_eq
      viscosity state wave
  rw [show
    (inner ℂ
        (puncturedWholeVorticityKineticEuclideanState state)
        (puncturedWholeUnforcedNegativeOneEuclideanState
          viscosity state stateTransverse gradientSummable)).re =
      (inner ℂ kineticState tangentState).re by rfl]
  rw [innerAsTsum,
    Summable.tsum_sub nonlinearWorkSummable viscousMassSummable,
    nonlinearWorkTsum]
  simp only [zero_sub]
  have viscousMassTsum :
      (∑' wave, viscousMass wave) =
        viscosity * puncturedWholeVorticityEuclideanMass state := by
    simp only [viscousMass]
    rw [tsum_mul_left]
    rfl
  rw [viscousMassTsum,
    puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row state zeroRow]
  ring

/-- The integer-lattice spectral gap controls the complete kinetic test norm
by the actual whole vorticity mass. -/
theorem twoPiSq_mul_kineticEuclideanState_norm_sq_le_wholeMass
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    (2 * Real.pi) ^ 2 *
        ‖puncturedWholeVorticityKineticEuclideanState state‖ ^ 2 ≤
      wholeVorticityEuclideanMass state := by
  rw [puncturedWholeVorticityKineticEuclideanState_norm_sq,
    ← puncturedWholeVorticityEuclideanMass_eq_whole_of_zero_row
      state zeroRow]
  let kineticDensity : NonzeroIntegerWavevector → ℝ :=
    fun wave =>
      complexCoordinateAmplitudeSq (state wave.1) /
        integerWaveViscousMultiplier wave.1
  let massDensity : NonzeroIntegerWavevector → ℝ :=
    fun wave => complexCoordinateAmplitudeSq (state wave.1)
  change (2 * Real.pi) ^ 2 * (∑' wave, kineticDensity wave) ≤
    ∑' wave, massDensity wave
  calc
    (2 * Real.pi) ^ 2 * (∑' wave, kineticDensity wave) =
        ∑' wave, (2 * Real.pi) ^ 2 * kineticDensity wave := by
      rw [tsum_mul_left]
    _ ≤ ∑' wave, massDensity wave :=
      Summable.tsum_le_tsum
        (fun wave => by
          have multiplierPos :
              0 < integerWaveViscousMultiplier wave.1 :=
            integerWaveViscousMultiplier_pos wave
          simp only [kineticDensity, massDensity]
          calc
            (2 * Real.pi) ^ 2 *
                (complexCoordinateAmplitudeSq (state wave.1) /
                  integerWaveViscousMultiplier wave.1) =
              complexCoordinateAmplitudeSq (state wave.1) *
                  (2 * Real.pi) ^ 2 /
                integerWaveViscousMultiplier wave.1 := by ring
            _ ≤ complexCoordinateAmplitudeSq (state wave.1) := by
              apply (div_le_iff₀ multiplierPos).2
              exact mul_le_mul_of_nonneg_left
                (twoPiSq_le_integerWaveViscousMultiplier wave)
                (complexCoordinateAmplitudeSq_nonneg _))
        ((summable_puncturedWholeVorticityKineticMass state).mul_left
          ((2 * Real.pi) ^ 2))
        (summable_puncturedWholeVorticityEuclideanMass state)

/-- Exact kinetic cancellation plus Hilbert Cauchy--Schwarz gives a
quantitative `H⁻¹` lower bound for every nonzero-mass unforced state. -/
theorem viscosity_sq_mul_twoPiSq_mul_mass_le_unforcedTangent_norm_sq
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
    (massPos : 0 < wholeVorticityEuclideanMass state) :
    viscosity ^ 2 * (2 * Real.pi) ^ 2 *
        wholeVorticityEuclideanMass state ≤
      ‖puncturedWholeUnforcedNegativeOneEuclideanState
        viscosity state stateTransverse gradientSummable‖ ^ 2 := by
  let kineticState :=
    puncturedWholeVorticityKineticEuclideanState state
  let tangentState :=
    puncturedWholeUnforcedNegativeOneEuclideanState
      viscosity state stateTransverse gradientSummable
  let mass := wholeVorticityEuclideanMass state
  let spectralGap := (2 * Real.pi) ^ 2
  have massNonneg : 0 ≤ mass := massPos.le
  have spectralGapNonneg : 0 ≤ spectralGap := by
    exact sq_nonneg _
  have pairing :
      (inner ℂ kineticState tangentState).re = -viscosity * mass := by
    simpa [kineticState, tangentState, mass] using
      puncturedWholeUnforcedNegativeOneEuclideanState_kineticPairing
        viscosity state zeroRow stateTransverse stateReality
        gradientSummable
  have negPairing :
      (inner ℂ kineticState (-tangentState)).re =
        viscosity * mass := by
    rw [inner_neg_right]
    simp only [Complex.neg_re, pairing]
    ring
  have cauchy :
      viscosity * mass ≤ ‖kineticState‖ * ‖tangentState‖ := by
    calc
      viscosity * mass =
          (inner ℂ kineticState (-tangentState)).re :=
        negPairing.symm
      _ ≤ ‖kineticState‖ * ‖-tangentState‖ :=
        re_inner_le_norm (𝕜 := ℂ) kineticState (-tangentState)
      _ = ‖kineticState‖ * ‖tangentState‖ := by
        rw [norm_neg]
  have squaredCauchy :
      (viscosity * mass) ^ 2 ≤
        (‖kineticState‖ * ‖tangentState‖) ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg viscosityPos.le massNonneg)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 cauchy
  have spectralControl :
      spectralGap * ‖kineticState‖ ^ 2 ≤ mass := by
    simpa [spectralGap, kineticState, mass] using
      twoPiSq_mul_kineticEuclideanState_norm_sq_le_wholeMass
        state zeroRow
  have combined :
      spectralGap * (viscosity * mass) ^ 2 ≤
        mass * ‖tangentState‖ ^ 2 := by
    calc
      spectralGap * (viscosity * mass) ^ 2 ≤
          spectralGap *
            (‖kineticState‖ * ‖tangentState‖) ^ 2 :=
        mul_le_mul_of_nonneg_left squaredCauchy spectralGapNonneg
      _ = (spectralGap * ‖kineticState‖ ^ 2) *
          ‖tangentState‖ ^ 2 := by ring
      _ ≤ mass * ‖tangentState‖ ^ 2 :=
        mul_le_mul_of_nonneg_right spectralControl (sq_nonneg _)
  change viscosity ^ 2 * spectralGap * mass ≤
    ‖tangentState‖ ^ 2
  apply (mul_le_mul_iff_right₀ massPos).mp
  calc
    mass * (viscosity ^ 2 * spectralGap * mass) =
        spectralGap * (viscosity * mass) ^ 2 := by ring
    _ ≤ mass * ‖tangentState‖ ^ 2 := combined

/-! ## Uniform source-owned quantum at every actual half-critical crossing -/

/-- The fixed positive `H⁻¹` tangent quantum generated by viscosity,
the integer spectral gap, and the intrinsic half-critical lattice constant.
There is no caller-selected output, cutoff, margin, or lower bound. -/
def wholeRestartCrossingTangentCoerciveQuantum
    (ν : Viscosity) : ℝ :=
  (ν.coeff ^ 2 * (2 * Real.pi) ^ 2) ^ 2 /
    (2 * criticalEnstrophyLatticeConstant)

theorem wholeRestartCrossingTangentCoerciveQuantum_pos
    (ν : Viscosity) :
    0 < wholeRestartCrossingTangentCoerciveQuantum ν := by
  unfold wholeRestartCrossingTangentCoerciveQuantum
  exact div_pos
    (sq_pos_of_pos
      (mul_pos (sq_pos_of_pos ν.coeff_pos)
        (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))))
    (mul_pos (by norm_num) criticalEnstrophyLatticeConstant_pos)

/-- Every actual half-critical restart crossing carries the same strictly
positive whole-tangent `H⁻¹` quantum.  The bound is generated internally
from the crossing state and exact kinetic cancellation. -/
theorem wholeRestartCrossing_unforcedTangent_norm_sq_gt_quantum
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    wholeRestartCrossingTangentCoerciveQuantum ν <
      ‖puncturedWholeUnforcedNegativeOneEuclideanState
        ν.coeff
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable‖ ^ 2 := by
  let state := (run initial index).contact.physicalState
  let mass := wholeVorticityEuclideanMass state
  let amplitude := ν.coeff ^ 2 * (2 * Real.pi) ^ 2
  have amplitudePos : 0 < amplitude := by
    exact mul_pos (sq_pos_of_pos ν.coeff_pos)
      (sq_pos_of_pos (mul_pos (by norm_num) Real.pi_pos))
  have crossed' :
      (1 / 2 : ℝ) * amplitude <
        criticalEnstrophyLatticeConstant * mass := by
    unfold wholeRestartHalfCriticalCrossed at crossed
    calc
      (1 / 2 : ℝ) * amplitude =
          (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
        simp only [amplitude]
        ring
      _ < criticalEnstrophyLatticeConstant *
          wholeVorticityEuclideanMass
            (run initial index).contact.physicalState := crossed
      _ = criticalEnstrophyLatticeConstant * mass := by rfl
  have thresholdPos : 0 < (1 / 2 : ℝ) * amplitude :=
    mul_pos (by norm_num) amplitudePos
  have constantMulMassPos :
      0 < criticalEnstrophyLatticeConstant * mass :=
    thresholdPos.trans crossed'
  have massPos : 0 < mass := by
    rcases (mul_pos_iff.mp constantMulMassPos) with positive | negative
    · exact positive.2
    · exact False.elim
        ((not_lt_of_ge criticalEnstrophyLatticeConstant_pos.le)
          negative.1)
  have coercive :
      amplitude * mass ≤
        ‖puncturedWholeUnforcedNegativeOneEuclideanState
          ν.coeff state
          (run initial index).contact.transverse
          (run initial index).contact.gradient_summable‖ ^ 2 := by
    simpa [amplitude, mass, state] using
      viscosity_sq_mul_twoPiSq_mul_mass_le_unforcedTangent_norm_sq
        ν.coeff ν.coeff_pos state
        (run initial index).contact.physicalState_zero
        (run initial index).contact.transverse
        (run initial index).contact.reality
        (run initial index).contact.gradient_summable
        massPos
  have quantumLtMass :
      amplitude ^ 2 /
          (2 * criticalEnstrophyLatticeConstant) <
        amplitude * mass := by
    have scaled :
        (2 * amplitude) * ((1 / 2 : ℝ) * amplitude) <
          (2 * amplitude) *
            (criticalEnstrophyLatticeConstant * mass) :=
      mul_lt_mul_of_pos_left crossed'
        (mul_pos (by norm_num) amplitudePos)
    apply (div_lt_iff₀
      (mul_pos (by norm_num)
        criticalEnstrophyLatticeConstant_pos)).2
    calc
      amplitude ^ 2 =
          (2 * amplitude) * ((1 / 2 : ℝ) * amplitude) := by
        ring
      _ < (2 * amplitude) *
          (criticalEnstrophyLatticeConstant * mass) := scaled
      _ = (amplitude * mass) *
          (2 * criticalEnstrophyLatticeConstant) := by ring
  calc
    wholeRestartCrossingTangentCoerciveQuantum ν =
        amplitude ^ 2 /
          (2 * criticalEnstrophyLatticeConstant) := by
      rfl
    _ < amplitude * mass := quantumLtMass
    _ ≤ ‖puncturedWholeUnforcedNegativeOneEuclideanState
        ν.coeff
        (run initial index).contact.physicalState
        (run initial index).contact.transverse
        (run initial index).contact.gradient_summable‖ ^ 2 := by
      simpa [state] using coercive

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
end NavierStokes
end SaturationMonoid
