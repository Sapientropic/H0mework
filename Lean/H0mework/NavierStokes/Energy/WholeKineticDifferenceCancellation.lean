import H0mework.NavierStokes.Energy.FiniteKineticDifferenceCancellation
import H0mework.NavierStokes.Energy.WholeKineticMassSeparation
import H0mework.NavierStokes.Fourier.WholeNonlinearDifferenceNegativeOne

/-!
# Whole-lattice kinetic cancellation for a nonlinear difference

The cutoff-independent kinetic pairing is realized on the actual
nonzero-frequency lattice as the real part of three scalar `ℓ²` inner
products.  Canonical punctured-cube projections converge strongly in the
kinetic test slot and in the nonlinear `H⁻¹` slot.  The finite exact
transport cancellation therefore survives the whole-lattice limit:

```text
|⟨omega_left - omega_right, N(left) - N(right)⟩_{H⁻¹,H¹}|
  ≤ M(left) * sqrt (kineticMass(left - right))
            * sqrt (euclideanMass(left - right)).
```

The conclusion has no cutoff, terminal shell, target radius, critical
smallness, or convergence certificate premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation

open scoped BigOperators ENNReal Topology

open Filter
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientInfiniteNonlinearNegativeSobolev
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientWholeSpaceTimeCriticalSerrin
open ThreeDimensionalVorticityCoefficientGeneratedPathInfiniteNonlinearNegativeOneTimeBudget
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientFiniteKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientWholeKineticMassSeparation
open ThreeDimensionalVorticityCoefficientWholeNonlinearDifferenceNegativeOne

noncomputable section

/-! ## Exact one-wave kinetic identification -/

/--
Biot--Savart is an exact isometry between the transverse vorticity row with
inverse Laplacian weight and its velocity row.
-/
theorem complexCoordinateRealInner_biotSavartVelocityCoefficient
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (left right : ComplexCoordinateVector)
    (leftTransverse : complexWavevector wave ⬝ᵥ left = 0) :
    complexCoordinateRealInner
        (biotSavartVelocityCoefficient wave left)
        (biotSavartVelocityCoefficient wave right) =
      complexCoordinateRealInner left right /
        integerWaveViscousMultiplier wave := by
  have conjugateTransverse :
      vectorConj left ⬝ᵥ complexWavevector wave = 0 := by
    rw [dotProduct_comm,
      complexWavevector_dot_vectorConj,
      leftTransverse]
    simp
  have scalarStar :
      star
          (Complex.I /
            (((2 * Real.pi * integerWaveNormSq wave : ℝ) : ℂ))) =
        -Complex.I /
          (((2 * Real.pi * integerWaveNormSq wave : ℝ) : ℂ)) := by
    change
      (starRingEnd ℂ)
          (Complex.I /
            (((2 * Real.pi * integerWaveNormSq wave : ℝ) : ℂ))) = _
    rw [map_div₀, Complex.conj_I, Complex.conj_ofReal]
  rw [complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot]
  simp only [biotSavartVelocityCoefficient, if_neg waveNe]
  rw [vectorConj_smul, scalarStar,
    vectorConj_crossProduct,
    vectorConj_complexWavevector,
    smul_dotProduct, dotProduct_smul,
    cross_dot_cross,
    complexWavevector_dot_self,
    conjugateTransverse]
  simp only [mul_zero, sub_zero, smul_eq_mul]
  unfold integerWaveViscousMultiplier
  have waveNormNe : integerWaveNormSq wave ≠ 0 :=
    integerWaveNormSq_ne_zero waveNe
  have piNe : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  rw [Complex.I_sq]
  simp only [neg_mul, neg_div, neg_neg, one_mul]
  rw [Complex.div_re]
  have castPiSq :
      (Real.pi : ℂ) ^ 2 = ((Real.pi ^ 2 : ℝ) : ℂ) := by
    norm_cast
  rw [castPiSq]
  have castDenom :
      (2 : ℂ) ^ 2 * ((Real.pi ^ 2 : ℝ) : ℂ) *
          (integerWaveNormSq wave : ℂ) =
        (((2 : ℝ) ^ 2 * Real.pi ^ 2 *
          integerWaveNormSq wave : ℝ) : ℂ) := by
    norm_cast
  rw [castDenom]
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, Complex.normSq_ofReal]
  field_simp
  ring

/-! ## Whole weighted pairing -/

/-- Coordinate projection on the complete scalar `ℓ²` lattice. -/
def wholeCoordinateSliceCLM
    (coordinate : Coordinate) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 →L[ℂ]
      lp (fun _ : IntegerWavevector => ℂ) 2 :=
  lp.mapCLM 2
    (fun _ =>
      (ContinuousLinearMap.proj coordinate :
        ComplexCoordinateVector →L[ℂ] ℂ))
    zero_le_one
    (fun _ => by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro vector
      exact (norm_le_pi_norm vector coordinate).trans_eq
        (one_mul ‖vector‖).symm)

@[simp] theorem wholeCoordinateSliceCLM_apply
    (coordinate : Coordinate)
    (state :
      lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2)
    (wave : IntegerWavevector) :
    wholeCoordinateSliceCLM coordinate state wave =
      state wave coordinate :=
  rfl

/-- One coordinate of the actual whole nonlinear difference after the
inverse square-root Laplacian weight. -/
def wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate
    (coordinate : Coordinate)
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
          complexCoordinateAmplitudeSq (right wave))
    (differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((left - right) wave)) :
    lp (fun _ : IntegerWavevector => ℂ) 2 :=
  wholeCoordinateSliceCLM coordinate <|
    wholeStateVorticityNonlinearDifferenceNegativeOneState
      left right leftTransverse rightTransverse
      leftGradientSummable rightGradientSummable
      differenceGradientSummable

@[simp] theorem
    wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate_apply
    (coordinate : Coordinate)
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
          complexCoordinateAmplitudeSq (right wave))
    (differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((left - right) wave))
    (wave : IntegerWavevector) :
    wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate
        coordinate left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        differenceGradientSummable wave =
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
        left right wave coordinate :=
  rfl

/--
Cutoff-free kinetic pairing of the actual whole vorticity difference with
its actual whole nonlinear difference.
-/
def wholeStateVorticityNonlinearDifferenceKineticPairing
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
          complexCoordinateAmplitudeSq (right wave))
    (differenceGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq ((left - right) wave)) : ℝ :=
  ∑ coordinate : Coordinate,
    (inner ℂ
      (wholeKineticCoordinateSliceCLM coordinate (left - right))
      (wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate
        coordinate left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        differenceGradientSummable)).re

/-! ## Strong canonical projection in the nonlinear slot -/

/--
The source-owned gradient responsibility omitted by the canonical
punctured cube tends to zero.  The conclusion is generated by the actual
summable whole gradient density.
-/
theorem
    wholeStateVorticityGradientMass_puncturedProjection_sub_tendsto_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Tendsto
      (fun radius =>
        wholeStateVorticityGradientMass
          (complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) state - state))
      atTop (𝓝 0) := by
  unfold wholeStateVorticityGradientMass
  let f : ℕ → IntegerWavevector → ℝ := fun radius wave =>
    integerWaveNormSq wave *
      complexCoordinateAmplitudeSq
        ((complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) state - state) wave)
  have pointwise :
      ∀ wave, Tendsto (fun radius => f radius wave) atTop (𝓝 0) := by
    intro wave
    by_cases waveZero : wave = 0
    · subst wave
      simp [f, complexSharpSupportProjection_apply, zeroRow,
        complexCoordinateAmplitudeSq]
    · refine (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr' ?_
      filter_upwards
        [nonzero_integerWave_eventually_mem_puncturedFrequencyCube
          wave waveZero] with radius waveMem
      simp [f, complexSharpSupportProjection_apply, waveMem,
        complexCoordinateAmplitudeSq]
  have dominated :
      ∀ᶠ radius : ℕ in atTop, ∀ wave,
        ‖f radius wave‖ ≤
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) :=
    Filter.Eventually.of_forall fun radius wave => by
      have rhsNonneg :
          0 ≤ integerWaveNormSq wave *
            complexCoordinateAmplitudeSq (state wave) :=
        mul_nonneg (integerWaveNormSq_nonneg wave)
          (complexCoordinateAmplitudeSq_nonneg _)
      by_cases waveMem :
          wave ∈ puncturedIntegerWaveFrequencyCube radius
      · calc
          ‖f radius wave‖ = 0 := by
            simp [f, complexSharpSupportProjection_apply, waveMem,
              complexCoordinateAmplitudeSq]
          _ ≤ integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (state wave) := rhsNonneg
      · have fEq :
            f radius wave =
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq (state wave) := by
          simp [f, complexSharpSupportProjection_apply, waveMem,
            complexCoordinateAmplitudeSq]
        calc
          ‖f radius wave‖ =
              integerWaveNormSq wave *
                complexCoordinateAmplitudeSq (state wave) := by
            rw [fEq, Real.norm_of_nonneg rhsNonneg]
          _ ≤ _ := le_rfl
  simpa [f] using
    (tendsto_tsum_of_dominated_convergence
      (f := f) (g := fun _ => 0)
      gradientSummable pointwise dominated)

/-- The complete Euclidean mass omitted by the canonical punctured cube
tends to zero on the actual Hilbert carrier. -/
theorem
    wholeVorticityEuclideanMass_puncturedProjection_sub_tendsto_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0) :
    Tendsto
      (fun radius =>
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) state - state))
      atTop (𝓝 0) := by
  have projectionTendsto :=
    complexSharpSupportProjection_puncturedFrequencyCube_tendsto
      state zeroRow
  have differenceTendsto :
      Tendsto
        (fun radius =>
          complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) state - state)
        atTop (𝓝 0) := by
    simpa using projectionTendsto.sub
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => state) atTop (𝓝 state))
  have normSqTendsto :
      Tendsto
        (fun radius =>
          ‖complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) state -
              state‖ ^ 2)
        atTop (𝓝 0) := by
    simpa using (tendsto_norm.comp differenceTendsto).pow 2
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun radius => by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
  · exact Filter.Eventually.of_forall fun radius =>
      wholeVorticityEuclideanMass_le_three_mul_norm_sq _
  · simpa using (normSqTendsto.const_mul 3)

/-- The velocity-majorant square of the canonical omitted tail tends to
zero.  The critical lattice estimate consumes the actual gradient tail
generated above. -/
theorem
    wholeStateVelocityMajorant_sq_puncturedProjection_sub_tendsto_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Tendsto
      (fun radius =>
        wholeStateVelocityMajorant
          (complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) state - state) ^ 2)
      atTop (𝓝 0) := by
  let criticalConstant :=
    biotSavartSerrinConstant *
      (∑' wave : IntegerWavevector, integerWaveCriticalKernel wave)
  have tailGradientSummable :
      ∀ radius,
        Summable fun wave : IntegerWavevector =>
          integerWaveNormSq wave *
            complexCoordinateAmplitudeSq
              ((complexSharpSupportProjection
                (puncturedIntegerWaveFrequencyCube radius) state -
                state) wave) := by
    intro radius
    exact summable_wholeStateVorticityGradientDensity_sub
      (complexSharpSupportProjection
        (puncturedIntegerWaveFrequencyCube radius) state) state
      (summable_wholeStateVorticityGradientDensity_of_supported
        (puncturedIntegerWaveFrequencyCube radius)
        (complexSharpSupportProjection
          (puncturedIntegerWaveFrequencyCube radius) state)
        (complexSharpSupportProjection_supported
          (puncturedIntegerWaveFrequencyCube radius) state))
      gradientSummable
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun radius => sq_nonneg _
  · exact Filter.Eventually.of_forall fun radius => by
      simpa [criticalConstant] using
        wholeStateVelocityMajorant_sq_le_criticalGlobal
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) state - state)
          (tailGradientSummable radius)
  · simpa [criticalConstant] using
      ((wholeStateVorticityGradientMass_puncturedProjection_sub_tendsto_zero
        state zeroRow gradientSummable).const_mul criticalConstant)

/-- Sharp projection preserves the retained finite velocity majorant. -/
theorem finiteStateVelocityMajorant_sharpSupportProjection
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVelocityMajorant modes
        (complexSharpSupportProjection modes state) =
      finiteStateVelocityMajorant modes state := by
  unfold finiteStateVelocityMajorant finiteVelocityFourierMajorant
  apply Finset.sum_congr rfl
  intro wave waveMem
  simp [finiteStateVelocityCoefficient,
    complexSharpSupportProjection_apply, waveMem]

/-- A finite sharp projection cannot increase the complete velocity
majorant. -/
theorem wholeStateVelocityMajorant_sharpSupportProjection_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    wholeStateVelocityMajorant
        (complexSharpSupportProjection modes state) ≤
      wholeStateVelocityMajorant state := by
  rw [wholeStateVelocityMajorant_eq_finite_of_supported
    modes (complexSharpSupportProjection modes state)
    (complexSharpSupportProjection_supported modes state)]
  rw [finiteStateVelocityMajorant_sharpSupportProjection]
  exact finiteStateVelocityMajorant_le_whole
    modes state gradientSummable

/-- A finite sharp projection cannot increase the complete Euclidean
vorticity mass. -/
theorem wholeVorticityEuclideanMass_sharpSupportProjection_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass
        (complexSharpSupportProjection modes state) ≤
      wholeVorticityEuclideanMass state := by
  rw [wholeVorticityEuclideanMass_eq_finite_of_supported
    modes (complexSharpSupportProjection modes state)
    (complexSharpSupportProjection_supported modes state)]
  rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass modes state

/-- Sharp projection and its omitted complement form an exact Euclidean
mass partition.  This identity is taken before any path or frequency
occurrence is quotiented away. -/
theorem wholeVorticityEuclideanMass_eq_projection_add_complement
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    wholeVorticityEuclideanMass state =
      wholeVorticityEuclideanMass
          (complexSharpSupportProjection modes state) +
        wholeVorticityEuclideanMass
          (complexSharpSupportProjection modes state - state) := by
  unfold wholeVorticityEuclideanMass
  rw [← (summable_vorticityRowAmplitude_sq
      (complexSharpSupportProjection modes state)).tsum_add
    (summable_vorticityRowAmplitude_sq
      (complexSharpSupportProjection modes state - state))]
  apply tsum_congr
  intro wave
  by_cases waveMem : wave ∈ modes
  · simp [complexSharpSupportProjection_apply, waveMem,
      vorticityRowAmplitude, complexCoordinateAmplitudeSq]
  · simp [complexSharpSupportProjection_apply, waveMem,
      vorticityRowAmplitude, complexCoordinateAmplitudeSq]

/-- Whole transversality is preserved by every sharp support projection. -/
theorem wholeStateTransverse_sharpSupportProjection
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    WholeStateTransverse
      (complexSharpSupportProjection modes state) := by
  intro wave
  by_cases waveMem : wave ∈ modes
  · simpa [complexSharpSupportProjection_apply, waveMem] using
      transverse wave
  · simp [complexSharpSupportProjection_apply, waveMem]

/-- The nonlinear `H⁻¹` error generated by one canonical punctured sharp
projection of a whole state. -/
def puncturedProjectionNonlinearErrorState
    (radius : ℕ)
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 :=
  let projected :=
    complexSharpSupportProjection
      (puncturedIntegerWaveFrequencyCube radius) state
  let projectedTransverse :=
    wholeStateTransverse_sharpSupportProjection
      (puncturedIntegerWaveFrequencyCube radius) state transverse
  let projectedGradientSummable :=
    summable_wholeStateVorticityGradientDensity_of_supported
      (puncturedIntegerWaveFrequencyCube radius) projected
      (complexSharpSupportProjection_supported
        (puncturedIntegerWaveFrequencyCube radius) state)
  wholeStateVorticityNonlinearDifferenceNegativeOneState
    projected state projectedTransverse transverse
    projectedGradientSummable gradientSummable
    (summable_wholeStateVorticityGradientDensity_sub
      projected state projectedGradientSummable gradientSummable)

/--
The actual nonlinear `H⁻¹` mass between a canonical punctured projection
and its whole state tends to zero.
-/
theorem
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_tendsto_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (transverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Tendsto
      (fun radius =>
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) state)
          state)
      atTop (𝓝 0) := by
  let projected : ℕ → ComplexVorticityHilbertState := fun radius =>
    complexSharpSupportProjection
      (puncturedIntegerWaveFrequencyCube radius) state
  let stateMajorant := wholeStateVelocityMajorant state
  let stateMass := wholeVorticityEuclideanMass state
  let tailMass : ℕ → ℝ := fun radius =>
    wholeVorticityEuclideanMass (projected radius - state)
  let tailMajorantSq : ℕ → ℝ := fun radius =>
    wholeStateVelocityMajorant (projected radius - state) ^ 2
  let upper : ℕ → ℝ := fun radius =>
    8 *
      (stateMajorant ^ 2 * tailMass radius +
        tailMajorantSq radius * stateMass)
  have stateMajorantNonneg : 0 ≤ stateMajorant := by
    exact wholeStateVelocityMajorant_nonneg state
  have stateMassNonneg : 0 ≤ stateMass := by
    unfold stateMass wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  have tailMassTendsto :
      Tendsto tailMass atTop (𝓝 0) := by
    simpa [tailMass, projected] using
      wholeVorticityEuclideanMass_puncturedProjection_sub_tendsto_zero
        state zeroRow
  have tailMajorantSqTendsto :
      Tendsto tailMajorantSq atTop (𝓝 0) := by
    simpa [tailMajorantSq, projected] using
      wholeStateVelocityMajorant_sq_puncturedProjection_sub_tendsto_zero
        state zeroRow gradientSummable
  have upperTendsto : Tendsto upper atTop (𝓝 0) := by
    have firstTendsto :
        Tendsto
          (fun radius => stateMajorant ^ 2 * tailMass radius)
          atTop (𝓝 0) := by
      simpa using tailMassTendsto.const_mul (stateMajorant ^ 2)
    have secondTendsto :
        Tendsto
          (fun radius => tailMajorantSq radius * stateMass)
          atTop (𝓝 0) := by
      simpa using tailMajorantSqTendsto.mul_const stateMass
    simpa [upper] using
      (firstTendsto.add secondTendsto).const_mul 8
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun radius => by
      unfold wholeStateVorticityNonlinearDifferenceNegativeOneMass
      exact tsum_nonneg fun output =>
        wholeStateVorticityNonlinearDifferenceNegativeOneDensity_nonneg
          (projected radius) state output
  · exact Filter.Eventually.of_forall fun radius => by
      have projectedTransverse :
          WholeStateTransverse (projected radius) := by
        simpa [projected] using
          wholeStateTransverse_sharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) state transverse
      have projectedGradientSummable :
          Summable fun wave : IntegerWavevector =>
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq (projected radius wave) := by
        exact summable_wholeStateVorticityGradientDensity_of_supported
          (puncturedIntegerWaveFrequencyCube radius)
          (projected radius)
          (by
            simpa [projected] using
              complexSharpSupportProjection_supported
                (puncturedIntegerWaveFrequencyCube radius) state)
      have differenceGradientSummable :
          Summable fun wave : IntegerWavevector =>
            integerWaveNormSq wave *
              complexCoordinateAmplitudeSq
                ((projected radius - state) wave) :=
        summable_wholeStateVorticityGradientDensity_sub
          (projected radius) state
          projectedGradientSummable gradientSummable
      have nonlinearBound :=
        wholeStateVorticityNonlinearDifferenceNegativeOneMass_le
          (projected radius) state
          projectedTransverse transverse
          projectedGradientSummable gradientSummable
          differenceGradientSummable
      have projectedMajorantLe :
          wholeStateVelocityMajorant (projected radius) ≤
            stateMajorant := by
        simpa [projected, stateMajorant] using
          wholeStateVelocityMajorant_sharpSupportProjection_le
            (puncturedIntegerWaveFrequencyCube radius)
            state gradientSummable
      have projectedMassLe :
          wholeVorticityEuclideanMass (projected radius) ≤
            stateMass := by
        simpa [projected, stateMass] using
          wholeVorticityEuclideanMass_sharpSupportProjection_le
            (puncturedIntegerWaveFrequencyCube radius) state
      have projectedMajorantNonneg :
          0 ≤ wholeStateVelocityMajorant (projected radius) :=
        wholeStateVelocityMajorant_nonneg _
      have projectedMajorantSqLe :
          wholeStateVelocityMajorant (projected radius) ^ 2 ≤
            stateMajorant ^ 2 :=
        (sq_le_sq₀ projectedMajorantNonneg stateMajorantNonneg).2
          projectedMajorantLe
      have projectedMassNonneg :
          0 ≤ wholeVorticityEuclideanMass (projected radius) := by
        unfold wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _
      have tailMassNonneg : 0 ≤ tailMass radius := by
        unfold tailMass wholeVorticityEuclideanMass
        exact tsum_nonneg fun wave => sq_nonneg _
      have tailMajorantSqNonneg : 0 ≤ tailMajorantSq radius := by
        exact sq_nonneg _
      have firstCoefficientLe :
          wholeStateVelocityMajorant (projected radius) ^ 2 +
              stateMajorant ^ 2 ≤
            2 * stateMajorant ^ 2 := by
        linarith
      have secondCoefficientLe :
          wholeVorticityEuclideanMass (projected radius) +
              stateMass ≤
            2 * stateMass := by
        linarith
      calc
        wholeStateVorticityNonlinearDifferenceNegativeOneMass
            (projected radius) state ≤
          4 *
            ((wholeStateVelocityMajorant (projected radius) ^ 2 +
                wholeStateVelocityMajorant state ^ 2) *
                wholeVorticityEuclideanMass
                  (projected radius - state) +
              wholeStateVelocityMajorant
                  (projected radius - state) ^ 2 *
                (wholeVorticityEuclideanMass (projected radius) +
                  wholeVorticityEuclideanMass state)) := nonlinearBound
        _ ≤
          4 *
            ((2 * stateMajorant ^ 2) * tailMass radius +
              tailMajorantSq radius * (2 * stateMass)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              firstCoefficientLe tailMassNonneg
          · exact mul_le_mul_of_nonneg_left
              secondCoefficientLe tailMajorantSqNonneg
        _ = upper radius := by
          simp only [stateMajorant, stateMass, tailMass,
            tailMajorantSq] at nonlinearBound ⊢
          unfold upper
          ring
  · exact upperTendsto

/--
Canonical punctured projection converges strongly in the actual nonlinear
`H⁻¹` carrier.
-/
theorem puncturedProjectionNonlinearErrorState_tendsto_zero
    (state : ComplexVorticityHilbertState)
    (zeroRow : state 0 = 0)
    (transverse : WholeStateTransverse state)
    (gradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (state wave)) :
    Tendsto
      (fun radius =>
        puncturedProjectionNonlinearErrorState
          radius state transverse gradientSummable)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have massTendsto :=
    wholeStateVorticityNonlinearDifferenceNegativeOneMass_projection_tendsto_zero
      state zeroRow transverse gradientSummable
  have sqrtMassTendsto :
      Tendsto
        (fun radius =>
          Real.sqrt
            (wholeStateVorticityNonlinearDifferenceNegativeOneMass
              (complexSharpSupportProjection
                (puncturedIntegerWaveFrequencyCube radius) state)
              state))
        atTop (𝓝 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp massTendsto using 1 <;>
      simp [Function.comp_def]
  apply sqrtMassTendsto.congr'
  exact Filter.Eventually.of_forall fun radius => by
    let projected :=
      complexSharpSupportProjection
        (puncturedIntegerWaveFrequencyCube radius) state
    let projectedTransverse :=
      wholeStateTransverse_sharpSupportProjection
        (puncturedIntegerWaveFrequencyCube radius) state transverse
    let projectedGradientSummable :=
      summable_wholeStateVorticityGradientDensity_of_supported
        (puncturedIntegerWaveFrequencyCube radius) projected
        (complexSharpSupportProjection_supported
          (puncturedIntegerWaveFrequencyCube radius) state)
    let differenceGradientSummable :=
      summable_wholeStateVorticityGradientDensity_sub
        projected state projectedGradientSummable gradientSummable
    have normSq :
        ‖puncturedProjectionNonlinearErrorState
            radius state transverse gradientSummable‖ ^ 2 =
          wholeStateVorticityNonlinearDifferenceNegativeOneMass
            projected state := by
      simpa [puncturedProjectionNonlinearErrorState,
        projected, projectedTransverse,
        projectedGradientSummable, differenceGradientSummable] using
        wholeStateVorticityNonlinearDifferenceNegativeOneState_norm_sq
          projected state projectedTransverse transverse
          projectedGradientSummable gradientSummable
          differenceGradientSummable
    change
      Real.sqrt
          (wholeStateVorticityNonlinearDifferenceNegativeOneMass
            projected state) =
        ‖puncturedProjectionNonlinearErrorState
          radius state transverse gradientSummable‖
    rw [← normSq, Real.sqrt_sq (norm_nonneg _)]

/-- The actual whole `H⁻¹` nonlinear difference of the two canonical
punctured projections. -/
def puncturedProjectionNonlinearDifferenceState
    (radius : ℕ)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right) :
    lp (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 :=
  let modes := puncturedIntegerWaveFrequencyCube radius
  let projectedLeft := complexSharpSupportProjection modes left
  let projectedRight := complexSharpSupportProjection modes right
  let projectedLeftTransverse :=
    wholeStateTransverse_sharpSupportProjection
      modes left leftTransverse
  let projectedRightTransverse :=
    wholeStateTransverse_sharpSupportProjection
      modes right rightTransverse
  let projectedLeftGradientSummable :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes projectedLeft
      (complexSharpSupportProjection_supported modes left)
  let projectedRightGradientSummable :=
    summable_wholeStateVorticityGradientDensity_of_supported
      modes projectedRight
      (complexSharpSupportProjection_supported modes right)
  wholeStateVorticityNonlinearDifferenceNegativeOneState
    projectedLeft projectedRight
    projectedLeftTransverse projectedRightTransverse
    projectedLeftGradientSummable projectedRightGradientSummable
    (summable_wholeStateVorticityGradientDensity_sub
      projectedLeft projectedRight
      projectedLeftGradientSummable projectedRightGradientSummable)

/--
The canonical nonlinear difference error is exactly the left projection
error minus the right projection error.
-/
theorem
    puncturedProjectionNonlinearDifferenceState_sub_eq_error_sub_error
    (radius : ℕ)
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
    puncturedProjectionNonlinearDifferenceState
          radius left right leftTransverse rightTransverse -
        wholeStateVorticityNonlinearDifferenceNegativeOneState
          left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable
          (summable_wholeStateVorticityGradientDensity_sub
            left right leftGradientSummable rightGradientSummable) =
      puncturedProjectionNonlinearErrorState
          radius left leftTransverse leftGradientSummable -
        puncturedProjectionNonlinearErrorState
          radius right rightTransverse rightGradientSummable := by
  apply lp.ext
  funext output
  change
    wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) left)
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) right)
          output -
        wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
          left right output =
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) left)
          left output -
        wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
          (complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) right)
          right output
  unfold
    wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
  by_cases outputZero : output = 0
  · simp [outputZero]
  · simp only [if_neg outputZero]
    module

/-- Canonical projected nonlinear differences converge strongly in the
actual whole `H⁻¹` carrier. -/
theorem puncturedProjectionNonlinearDifferenceState_tendsto
    (left right : ComplexVorticityHilbertState)
    (leftZeroRow : left 0 = 0)
    (rightZeroRow : right 0 = 0)
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
    Tendsto
      (fun radius =>
        puncturedProjectionNonlinearDifferenceState
          radius left right leftTransverse rightTransverse)
      atTop
      (𝓝
        (wholeStateVorticityNonlinearDifferenceNegativeOneState
          left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable
          (summable_wholeStateVorticityGradientDensity_sub
            left right leftGradientSummable rightGradientSummable))) := by
  let target :=
    wholeStateVorticityNonlinearDifferenceNegativeOneState
      left right leftTransverse rightTransverse
      leftGradientSummable rightGradientSummable
      (summable_wholeStateVorticityGradientDensity_sub
        left right leftGradientSummable rightGradientSummable)
  have leftErrorTendsto :=
    puncturedProjectionNonlinearErrorState_tendsto_zero
      left leftZeroRow leftTransverse leftGradientSummable
  have rightErrorTendsto :=
    puncturedProjectionNonlinearErrorState_tendsto_zero
      right rightZeroRow rightTransverse rightGradientSummable
  have differenceErrorTendsto :
      Tendsto
        (fun radius =>
          puncturedProjectionNonlinearErrorState
              radius left leftTransverse leftGradientSummable -
            puncturedProjectionNonlinearErrorState
              radius right rightTransverse rightGradientSummable)
        atTop (𝓝 0) := by
    simpa using leftErrorTendsto.sub rightErrorTendsto
  have targetPlusErrorTendsto :
      Tendsto
        (fun radius =>
          target +
            (puncturedProjectionNonlinearErrorState
                radius left leftTransverse leftGradientSummable -
              puncturedProjectionNonlinearErrorState
                radius right rightTransverse rightGradientSummable))
        atTop (𝓝 target) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => target) atTop (𝓝 target)).add
          differenceErrorTendsto
  apply targetPlusErrorTendsto.congr'
  exact Filter.Eventually.of_forall fun radius => by
    exact
      ((sub_eq_iff_eq_add').mp
        (puncturedProjectionNonlinearDifferenceState_sub_eq_error_sub_error
          radius left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable)).symm

/-! ## Canonical finite-to-whole pairing -/

/-- Canonical punctured-cube pairing, written on the two weighted whole
`ℓ²` slots so that its limit is forced by strong convergence. -/
def canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
    (radius : ℕ)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right) : ℝ :=
  let modes := puncturedIntegerWaveFrequencyCube radius
  ∑ coordinate : Coordinate,
    (inner ℂ
      (wholeKineticCoordinateSliceCLM coordinate
        (complexSharpSupportProjection modes (left - right)))
      (wholeCoordinateSliceCLM coordinate
        (puncturedProjectionNonlinearDifferenceState
          radius left right leftTransverse rightTransverse))).re

/--
The canonical punctured-cube pairings converge to the actual whole-lattice
pairing.
-/
theorem
    canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_tendsto
    (left right : ComplexVorticityHilbertState)
    (leftZeroRow : left 0 = 0)
    (rightZeroRow : right 0 = 0)
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
    Tendsto
      (fun radius =>
        canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
          radius left right leftTransverse rightTransverse)
      atTop
      (𝓝
        (wholeStateVorticityNonlinearDifferenceKineticPairing
          left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable
          (summable_wholeStateVorticityGradientDensity_sub
            left right leftGradientSummable rightGradientSummable))) := by
  have differenceZeroRow : (left - right) 0 = 0 := by
    simp [leftZeroRow, rightZeroRow]
  have testStateTendsto :
      Tendsto
        (fun radius =>
          complexSharpSupportProjection
            (puncturedIntegerWaveFrequencyCube radius) (left - right))
        atTop (𝓝 (left - right)) :=
    complexSharpSupportProjection_puncturedFrequencyCube_tendsto
      (left - right) differenceZeroRow
  have nonlinearStateTendsto :=
    puncturedProjectionNonlinearDifferenceState_tendsto
      left right leftZeroRow rightZeroRow
      leftTransverse rightTransverse
      leftGradientSummable rightGradientSummable
  unfold canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
    wholeStateVorticityNonlinearDifferenceKineticPairing
  apply tendsto_finsetSum
  intro coordinate coordinateMem
  have testCoordinateTendsto :
      Tendsto
        (fun radius =>
          wholeKineticCoordinateSliceCLM coordinate
            (complexSharpSupportProjection
              (puncturedIntegerWaveFrequencyCube radius) (left - right)))
        atTop
        (𝓝 (wholeKineticCoordinateSliceCLM coordinate (left - right))) :=
    by
      convert
        ((wholeKineticCoordinateSliceCLM coordinate).continuous.tendsto
          (left - right)).comp testStateTendsto using 1
      all_goals simp [Function.comp_def]
  have nonlinearCoordinateTendsto :
      Tendsto
        (fun radius =>
          wholeCoordinateSliceCLM coordinate
            (puncturedProjectionNonlinearDifferenceState
              radius left right leftTransverse rightTransverse))
        atTop
        (𝓝
          (wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate
            coordinate left right leftTransverse rightTransverse
            leftGradientSummable rightGradientSummable
            (summable_wholeStateVorticityGradientDensity_sub
              left right
              leftGradientSummable rightGradientSummable))) := by
    simpa [wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate,
      Function.comp_def] using
      ((wholeCoordinateSliceCLM coordinate).continuous.tendsto
        (wholeStateVorticityNonlinearDifferenceNegativeOneState
          left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable
          (summable_wholeStateVorticityGradientDensity_sub
            left right
            leftGradientSummable rightGradientSummable))).comp
        nonlinearStateTendsto
  exact (Complex.continuous_re.tendsto _).comp
    (testCoordinateTendsto.inner nonlinearCoordinateTendsto)

/-- The finite kinetic pairing is the direct inverse-Laplacian weighted
vorticity pairing on every zero-free transverse inventory. -/
theorem
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_weighted_sum
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : FiniteStateTransverseOn modes left)
    (rightTransverse : FiniteStateTransverseOn modes right) :
    finiteStateVorticityNonlinearDifferenceKineticPairing
        modes left right =
      ∑ wave ∈ modes,
        complexCoordinateRealInner
          ((left - right) wave)
          (finiteStateVorticityNonlinearCoefficientAt modes left wave -
            finiteStateVorticityNonlinearCoefficientAt modes right wave) /
          integerWaveViscousMultiplier wave := by
  classical
  unfold finiteStateVorticityNonlinearDifferenceKineticPairing
    finiteStateVorticityKineticPairing
  apply Finset.sum_congr rfl
  intro wave waveMem
  have waveNe : wave ≠ 0 := by
    intro waveZero
    exact zeroNotMem (waveZero ▸ waveMem)
  have differenceTransverse :
      complexWavevector wave ⬝ᵥ (left - right) wave = 0 :=
    finiteStateTransverseOn_sub
      modes left right leftTransverse rightTransverse wave waveMem
  simpa [finiteStateVelocityCoefficient] using
    complexCoordinateRealInner_biotSavartVelocityCoefficient
      wave waveNe ((left - right) wave)
      (finiteStateVorticityNonlinearCoefficientAt modes left wave -
        finiteStateVorticityNonlinearCoefficientAt modes right wave)
      differenceTransverse

/-- One nonzero row of the two weighted scalar `ℓ²` slots is exactly the
inverse-Laplacian real pairing. -/
theorem weightedCoordinateInnerSum_eq_realInner_div
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0)
    (left right : ComplexCoordinateVector) :
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave * left coordinate)
        (((Real.sqrt (integerWaveViscousMultiplier wave))⁻¹ : ℝ) *
          right coordinate)).re) =
      complexCoordinateRealInner left right /
        integerWaveViscousMultiplier wave := by
  have multiplierPos : 0 < integerWaveViscousMultiplier wave :=
    integerWaveViscousMultiplier_pos ⟨wave, waveNe⟩
  have sqrtPos : 0 < Real.sqrt (integerWaveViscousMultiplier wave) :=
    Real.sqrt_pos.2 multiplierPos
  have invCast :
      ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) =
        (((Real.sqrt
          (integerWaveViscousMultiplier wave))⁻¹ : ℝ) : ℂ) := by
    norm_cast
  rw [show wholeKineticFourierWeight wave =
      ((Real.sqrt (integerWaveViscousMultiplier wave) : ℂ)⁻¹) by
    simp [wholeKineticFourierWeight, waveNe], invCast]
  unfold complexCoordinateRealInner
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro coordinate coordinateMem
  rw [RCLike.inner_apply]
  simp only [map_mul, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, sub_zero, Complex.conj_re, Complex.conj_im]
  field_simp
  rw [Real.sq_sqrt multiplierPos.le]
  ring

/-- Every zero-free finite weighted mass is bounded by the complete
nonzero-lattice kinetic mass. -/
theorem finiteWeightedVorticityMass_le_puncturedWholeKineticMass
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
      complexCoordinateAmplitudeSq (state wave) /
        integerWaveViscousMultiplier wave) ≤
      puncturedWholeVorticityKineticMass state := by
  let embedding : ↥modes ↪ NonzeroIntegerWavevector :=
    ⟨fun wave =>
      ⟨wave.1, fun waveZero =>
        zeroNotMem (waveZero ▸ wave.2)⟩,
      fun left right equality => by
        apply Subtype.ext
        exact congrArg
          (fun wave : NonzeroIntegerWavevector => wave.1) equality⟩
  let indexedModes : Finset NonzeroIntegerWavevector :=
    modes.attach.map embedding
  have sumEq :
      (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave) /
          integerWaveViscousMultiplier wave) =
        ∑ wave ∈ indexedModes,
          complexCoordinateAmplitudeSq (state wave.1) /
            integerWaveViscousMultiplier wave.1 := by
    dsimp [indexedModes]
    rw [Finset.sum_map]
    change
      (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave) /
          integerWaveViscousMultiplier wave) =
      ∑ wave ∈ modes.attach,
        complexCoordinateAmplitudeSq (state wave.1) /
          integerWaveViscousMultiplier wave.1
    exact (Finset.sum_attach modes fun wave =>
      complexCoordinateAmplitudeSq (state wave) /
        integerWaveViscousMultiplier wave).symm
  rw [sumEq]
  unfold puncturedWholeVorticityKineticMass
  exact
    (summable_puncturedWholeVorticityKineticMass state).sum_le_tsum
      indexedModes fun wave waveMem =>
        div_nonneg (complexCoordinateAmplitudeSq_nonneg _)
          (integerWaveViscousMultiplier_pos wave).le

/-- Twice the conventional finite kinetic energy is bounded by the
complete nonzero-lattice kinetic mass. -/
theorem
    two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    2 * finiteStateVorticityKineticEnergy modes state ≤
      puncturedWholeVorticityKineticMass state := by
  rw [finiteStateVorticityKineticEnergy_eq_weightedVorticity
    modes zeroNotMem state stateTransverse]
  rw [show
      2 *
          ((1 / 2 : ℝ) *
            ∑ wave ∈ modes,
              complexCoordinateVectorNormSq (state wave) /
                ((2 * Real.pi) ^ 2 * integerWaveNormSq wave)) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) /
            integerWaveViscousMultiplier wave by
      unfold integerWaveViscousMultiplier
      simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      ring]
  exact finiteWeightedVorticityMass_le_puncturedWholeKineticMass
    modes zeroNotMem state

/-- A zero-free finitely supported state has no hidden kinetic mass outside
its actual finite Fourier inventory. -/
theorem puncturedWholeVorticityKineticMass_eq_finite_of_supported
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0) :
    puncturedWholeVorticityKineticMass state =
      ∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave) /
          integerWaveViscousMultiplier wave := by
  classical
  let embedding : ↥modes ↪ NonzeroIntegerWavevector :=
    ⟨fun wave =>
      ⟨wave.1, fun waveZero =>
        zeroNotMem (waveZero ▸ wave.2)⟩,
      fun left right equality => by
        apply Subtype.ext
        exact congrArg
          (fun wave : NonzeroIntegerWavevector => wave.1) equality⟩
  let indexedModes : Finset NonzeroIntegerWavevector :=
    modes.attach.map embedding
  unfold puncturedWholeVorticityKineticMass
  rw [tsum_eq_sum (s := indexedModes)]
  · dsimp [indexedModes]
    rw [Finset.sum_map]
    change
      (∑ wave ∈ modes.attach,
          complexCoordinateAmplitudeSq (state wave.1) /
            integerWaveViscousMultiplier wave.1) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) /
            integerWaveViscousMultiplier wave
    exact Finset.sum_attach modes (fun wave =>
      complexCoordinateAmplitudeSq (state wave) /
        integerWaveViscousMultiplier wave)
  · intro wave waveNotMem
    have baseNotMem : wave.1 ∉ modes := by
      intro baseMem
      apply waveNotMem
      exact Finset.mem_map.2
        ⟨⟨wave.1, baseMem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
    rw [supported wave.1 baseNotMem]
    simp [complexCoordinateAmplitudeSq]

/-- On an actual zero-free finite transverse carrier, whole kinetic mass is
exactly twice the conventional finite kinetic energy. -/
theorem puncturedWholeVorticityKineticMass_eq_two_mul_finiteEnergy
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (stateTransverse : FiniteStateTransverseOn modes state) :
    puncturedWholeVorticityKineticMass state =
      2 * finiteStateVorticityKineticEnergy modes state := by
  rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
    modes zeroNotMem state supported]
  rw [finiteStateVorticityKineticEnergy_eq_weightedVorticity
    modes zeroNotMem state stateTransverse]
  unfold integerWaveViscousMultiplier
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  ring

/-- Sharp finite projection cannot increase the complete kinetic-scale
mass; the discarded Fourier rows carry the nonnegative complement. -/
theorem puncturedWholeVorticityKineticMass_sharpSupportProjection_le
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState) :
    puncturedWholeVorticityKineticMass
        (complexSharpSupportProjection modes state) ≤
      puncturedWholeVorticityKineticMass state := by
  rw [puncturedWholeVorticityKineticMass_eq_finite_of_supported
    modes zeroNotMem (complexSharpSupportProjection modes state)
    (complexSharpSupportProjection_supported modes state)]
  have projectedSum :
      (∑ wave ∈ modes,
          complexCoordinateAmplitudeSq
              (complexSharpSupportProjection modes state wave) /
            integerWaveViscousMultiplier wave) =
        ∑ wave ∈ modes,
          complexCoordinateAmplitudeSq (state wave) /
            integerWaveViscousMultiplier wave := by
    apply Finset.sum_congr rfl
    intro wave waveMem
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
  rw [projectedSum]
  exact finiteWeightedVorticityMass_le_puncturedWholeKineticMass
    modes zeroNotMem state

/-- Every zero-free finite vorticity mass is bounded by the complete
nonzero-lattice Euclidean mass. -/
theorem finiteStateVorticityMass_le_puncturedWhole
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityMass modes state ≤
      puncturedWholeVorticityEuclideanMass state := by
  let embedding : ↥modes ↪ NonzeroIntegerWavevector :=
    ⟨fun wave =>
      ⟨wave.1, fun waveZero =>
        zeroNotMem (waveZero ▸ wave.2)⟩,
      fun left right equality => by
        apply Subtype.ext
        exact congrArg
          (fun wave : NonzeroIntegerWavevector => wave.1) equality⟩
  let indexedModes : Finset NonzeroIntegerWavevector :=
    modes.attach.map embedding
  have sumEq :
      finiteStateVorticityMass modes state =
        ∑ wave ∈ indexedModes,
          complexCoordinateAmplitudeSq (state wave.1) := by
    unfold finiteStateVorticityMass
    simp_rw [←
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    dsimp [indexedModes]
    rw [Finset.sum_map]
    change
      (∑ wave ∈ modes,
        complexCoordinateAmplitudeSq (state wave)) =
      ∑ wave ∈ modes.attach,
        complexCoordinateAmplitudeSq (state wave.1)
    exact (Finset.sum_attach modes fun wave =>
      complexCoordinateAmplitudeSq (state wave)).symm
  rw [sumEq]
  unfold puncturedWholeVorticityEuclideanMass
  exact
    (summable_puncturedWholeVorticityEuclideanMass state).sum_le_tsum
      indexedModes fun wave waveMem =>
        complexCoordinateAmplitudeSq_nonneg _

/--
At every radius, the canonical weighted whole-carrier pairing is exactly
the finite punctured-cube kinetic pairing.
-/
theorem
    canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_eq_finite
    (radius : ℕ)
    (left right : ComplexVorticityHilbertState)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right) :
    canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
        radius left right leftTransverse rightTransverse =
      finiteStateVorticityNonlinearDifferenceKineticPairing
        (puncturedIntegerWaveFrequencyCube radius) left right := by
  classical
  let modes := puncturedIntegerWaveFrequencyCube radius
  have zeroNotMem : 0 ∉ modes := by
    exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius
  have finiteLeftTransverse :
      FiniteStateTransverseOn modes left :=
    finiteStateTransverseOn_of_wholeStateTransverse
      modes left leftTransverse
  have finiteRightTransverse :
      FiniteStateTransverseOn modes right :=
    finiteStateTransverseOn_of_wholeStateTransverse
      modes right rightTransverse
  rw [
    finiteStateVorticityNonlinearDifferenceKineticPairing_eq_weighted_sum
      modes zeroNotMem left right
      finiteLeftTransverse finiteRightTransverse]
  unfold canonicalPuncturedVorticityNonlinearDifferenceKineticPairing
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate
          (complexSharpSupportProjection modes (left - right)))
        (wholeCoordinateSliceCLM coordinate
          (puncturedProjectionNonlinearDifferenceState
            radius left right leftTransverse rightTransverse))).re) = _
  simp_rw [lp.inner_eq_tsum]
  have innerSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          inner ℂ
            (wholeKineticCoordinateSliceCLM coordinate
              (complexSharpSupportProjection modes (left - right)) wave)
            (wholeCoordinateSliceCLM coordinate
              (puncturedProjectionNonlinearDifferenceState
                radius left right leftTransverse rightTransverse) wave) :=
    fun coordinate =>
      (lp.hasSum_inner
        (wholeKineticCoordinateSliceCLM coordinate
          (complexSharpSupportProjection modes (left - right)))
        (wholeCoordinateSliceCLM coordinate
          (puncturedProjectionNonlinearDifferenceState
            radius left right leftTransverse rightTransverse))).summable
  simp_rw [Complex.re_tsum (innerSummable _)]
  have reSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          (inner ℂ
            (wholeKineticCoordinateSliceCLM coordinate
              (complexSharpSupportProjection modes (left - right)) wave)
            (wholeCoordinateSliceCLM coordinate
              (puncturedProjectionNonlinearDifferenceState
                radius left right leftTransverse rightTransverse) wave)).re := by
    intro coordinate
    simpa [Function.comp_def] using
      (innerSummable coordinate).map
        Complex.reCLM Complex.continuous_re
  rw [← Summable.tsum_finsetSum
    (fun coordinate _ => reSummable coordinate)]
  rw [tsum_eq_sum (s := modes)]
  · apply Finset.sum_congr rfl
    intro wave waveMem
    have waveNe : wave ≠ 0 := by
      intro waveZero
      exact zeroNotMem (waveZero ▸ waveMem)
    have projectedLeftRow :
        wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection modes left) wave =
          finiteStateVorticityNonlinearCoefficientAt
            modes left wave :=
      wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite
        modes left wave
    have projectedRightRow :
        wholeStateVorticityNonlinearCoefficientAt
            (complexSharpSupportProjection modes right) wave =
          finiteStateVorticityNonlinearCoefficientAt
            modes right wave :=
      wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite
        modes right wave
    simp only [wholeKineticCoordinateSliceCLM_apply,
      wholeCoordinateSliceCLM_apply]
    change
      (∑ coordinate : Coordinate,
        (inner ℂ
          (wholeKineticFourierWeight wave *
            (complexSharpSupportProjection modes (left - right)
              wave coordinate))
          (wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
            (complexSharpSupportProjection modes left)
            (complexSharpSupportProjection modes right)
            wave coordinate)).re) =
        complexCoordinateRealInner
          ((left - right) wave)
          (finiteStateVorticityNonlinearCoefficientAt modes left wave -
            finiteStateVorticityNonlinearCoefficientAt modes right wave) /
          integerWaveViscousMultiplier wave
    rw [complexSharpSupportProjection_apply, if_pos waveMem]
    unfold
      wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
    rw [if_neg waveNe, projectedLeftRow, projectedRightRow]
    exact weightedCoordinateInnerSum_eq_realInner_div
      wave waveNe ((left - right) wave)
      (finiteStateVorticityNonlinearCoefficientAt modes left wave -
        finiteStateVorticityNonlinearCoefficientAt modes right wave)
  · intro wave waveNotMem
    simp [wholeKineticCoordinateSliceCLM_apply,
      complexSharpSupportProjection_apply, waveNotMem]

/-! ## Whole-lattice sharp and absorbed estimates -/

/--
Exact finite transport cancellation survives the canonical whole-lattice
limit with its cutoff-independent constant one.
-/
theorem
    wholeStateVorticityNonlinearDifferenceKineticPairing_abs_le
    (left right : ComplexVorticityHilbertState)
    (leftZeroRow : left 0 = 0)
    (rightZeroRow : right 0 = 0)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftReality : FiniteStateFourierReality left)
    (rightReality : FiniteStateFourierReality right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave)) :
    |wholeStateVorticityNonlinearDifferenceKineticPairing
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable)| ≤
      wholeStateVelocityMajorant left *
        Real.sqrt
          (puncturedWholeVorticityKineticMass (left - right)) *
        Real.sqrt
          (puncturedWholeVorticityEuclideanMass (left - right)) := by
  have canonicalTendsto :=
    canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_tendsto
      left right leftZeroRow rightZeroRow
      leftTransverse rightTransverse
      leftGradientSummable rightGradientSummable
  apply le_of_tendsto canonicalTendsto.abs
  exact Filter.Eventually.of_forall fun radius => by
    let modes := puncturedIntegerWaveFrequencyCube radius
    have zeroNotMem : 0 ∉ modes := by
      exact zero_not_mem_puncturedIntegerWaveFrequencyCube radius
    have negClosed : FiniteModeNegClosed modes := by
      exact fun wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    have finiteLeftTransverse :
        FiniteStateTransverseOn modes left :=
      finiteStateTransverseOn_of_wholeStateTransverse
        modes left leftTransverse
    have finiteRightTransverse :
        FiniteStateTransverseOn modes right :=
      finiteStateTransverseOn_of_wholeStateTransverse
        modes right rightTransverse
    have finiteLeftReality : FiniteStateRealityOn modes left :=
      fun wave waveMem => leftReality wave
    have finiteRightReality : FiniteStateRealityOn modes right :=
      fun wave waveMem => rightReality wave
    rw [
      canonicalPuncturedVorticityNonlinearDifferenceKineticPairing_eq_finite
        radius left right leftTransverse rightTransverse]
    have finiteBound :=
      finiteStateVorticityNonlinearDifferenceKineticPairing_abs_le
        modes zeroNotMem negClosed left right
        finiteLeftTransverse finiteRightTransverse
        finiteLeftReality finiteRightReality
    have majorantLe :
        finiteStateVelocityMajorant modes left ≤
          wholeStateVelocityMajorant left :=
      finiteStateVelocityMajorant_le_whole
        modes left leftGradientSummable
    have kineticLe :
        2 * finiteStateVorticityKineticEnergy modes (left - right) ≤
          puncturedWholeVorticityKineticMass (left - right) :=
      two_mul_finiteStateVorticityKineticEnergy_le_puncturedWhole
        modes zeroNotMem (left - right)
        (finiteStateTransverseOn_sub
          modes left right finiteLeftTransverse finiteRightTransverse)
    have massLe :
        finiteStateVorticityMass modes (left - right) ≤
          puncturedWholeVorticityEuclideanMass (left - right) :=
      finiteStateVorticityMass_le_puncturedWhole
        modes zeroNotMem (left - right)
    have firstProductLe :
        finiteStateVelocityMajorant modes left *
            Real.sqrt
              (2 * finiteStateVorticityKineticEnergy
                modes (left - right)) ≤
          wholeStateVelocityMajorant left *
            Real.sqrt
              (puncturedWholeVorticityKineticMass (left - right)) :=
      mul_le_mul majorantLe (Real.sqrt_le_sqrt kineticLe)
        (Real.sqrt_nonneg _)
        (wholeStateVelocityMajorant_nonneg left)
    exact finiteBound.trans <|
      mul_le_mul firstProductLe (Real.sqrt_le_sqrt massLe)
        (Real.sqrt_nonneg _)
        (mul_nonneg
          (wholeStateVelocityMajorant_nonneg left)
          (Real.sqrt_nonneg _))

/--
The whole weighted `ℓ²` pairing is exactly the actual rowwise nonlinear
work summed over all nonzero integer waves.
-/
theorem wholeStateVorticityNonlinearDifferenceKineticPairing_eq_tsum
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
    wholeStateVorticityNonlinearDifferenceKineticPairing
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) =
      ∑' wave : NonzeroIntegerWavevector,
        complexCoordinateRealInner
          ((left - right) wave.1)
          (wholeStateVorticityNonlinearCoefficientAt left wave.1 -
            wholeStateVorticityNonlinearCoefficientAt right wave.1) /
          integerWaveViscousMultiplier wave.1 := by
  let nonlinearCoordinate :
      Coordinate → lp (fun _ : IntegerWavevector => ℂ) 2 :=
    fun coordinate =>
      wholeStateVorticityNonlinearDifferenceNegativeOneCoordinate
        coordinate left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable)
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticCoordinateSliceCLM coordinate (left - right))
        (nonlinearCoordinate coordinate)).re) = _
  simp_rw [lp.inner_eq_tsum]
  have innerSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave)
            (nonlinearCoordinate coordinate wave) :=
    fun coordinate =>
      (lp.hasSum_inner
        (wholeKineticCoordinateSliceCLM coordinate (left - right))
        (nonlinearCoordinate coordinate)).summable
  simp_rw [Complex.re_tsum (innerSummable _)]
  have reSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : IntegerWavevector =>
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave)
            (nonlinearCoordinate coordinate wave)).re := by
    intro coordinate
    simpa [Function.comp_def] using
      (innerSummable coordinate).map
        Complex.reCLM Complex.continuous_re
  have coordinateTsumEq :
      ∀ coordinate : Coordinate,
        (∑' wave : IntegerWavevector,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave)
            (nonlinearCoordinate coordinate wave)).re) =
        ∑' wave : NonzeroIntegerWavevector,
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave.1)
            (nonlinearCoordinate coordinate wave.1)).re := by
    intro coordinate
    have complementZero :
        (∑' wave :
            ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
              Set IntegerWavevector),
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave.1)
            (nonlinearCoordinate coordinate wave.1)).re) = 0 := by
      rw [show
          (fun wave :
              ↥({ wave : IntegerWavevector | wave ≠ 0 }ᶜ :
                Set IntegerWavevector) =>
            (inner ℂ
              (wholeKineticCoordinateSliceCLM
                coordinate (left - right) wave.1)
              (nonlinearCoordinate coordinate wave.1)).re) =
            0 by
          funext wave
          have waveZero : wave.1 = 0 := by
            simpa using wave.2
          simp [wholeKineticCoordinateSliceCLM_apply,
            wholeKineticFourierWeight, waveZero]]
      exact tsum_zero
    have split :=
      (reSummable coordinate).tsum_subtype_add_tsum_subtype_compl
        { wave : IntegerWavevector | wave ≠ 0 }
    rw [complementZero, add_zero] at split
    exact split.symm
  simp_rw [coordinateTsumEq]
  have subtypeSummable :
      ∀ coordinate : Coordinate,
        Summable fun wave : NonzeroIntegerWavevector =>
          (inner ℂ
            (wholeKineticCoordinateSliceCLM
              coordinate (left - right) wave.1)
            (nonlinearCoordinate coordinate wave.1)).re := by
    intro coordinate
    exact (reSummable coordinate).subtype
      { wave : IntegerWavevector | wave ≠ 0 }
  rw [← Summable.tsum_finsetSum
    (fun coordinate _ => subtypeSummable coordinate)]
  apply tsum_congr
  intro wave
  simp only [wholeKineticCoordinateSliceCLM_apply]
  change
    (∑ coordinate : Coordinate,
      (inner ℂ
        (wholeKineticFourierWeight wave.1 *
          (left - right) wave.1 coordinate)
        (wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
          left right wave.1 coordinate)).re) =
      complexCoordinateRealInner
        ((left - right) wave.1)
        (wholeStateVorticityNonlinearCoefficientAt left wave.1 -
          wholeStateVorticityNonlinearCoefficientAt right wave.1) /
        integerWaveViscousMultiplier wave.1
  unfold
    wholeStateVorticityNonlinearDifferenceNegativeOneWeightedCoefficient
  rw [if_neg wave.2]
  exact weightedCoordinateInnerSum_eq_realInner_div
    wave.1 wave.2 ((left - right) wave.1)
    (wholeStateVorticityNonlinearCoefficientAt left wave.1 -
      wholeStateVorticityNonlinearCoefficientAt right wave.1)

/-- Whole-lattice Young absorption at the exact kinetic scale. -/
theorem
    wholeStateVorticityNonlinearDifferenceKineticPairing_abs_le_young
    (left right : ComplexVorticityHilbertState)
    (leftZeroRow : left 0 = 0)
    (rightZeroRow : right 0 = 0)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftReality : FiniteStateFourierReality left)
    (rightReality : FiniteStateFourierReality right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave))
    (ν : ℝ)
    (νPos : 0 < ν) :
    |wholeStateVorticityNonlinearDifferenceKineticPairing
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable)| ≤
      (ν / 2) *
          puncturedWholeVorticityEuclideanMass (left - right) +
        (ν⁻¹ / 2) * wholeStateVelocityMajorant left ^ 2 *
          puncturedWholeVorticityKineticMass (left - right) := by
  let mass :=
    puncturedWholeVorticityEuclideanMass (left - right)
  let energy :=
    puncturedWholeVorticityKineticMass (left - right)
  let majorant := wholeStateVelocityMajorant left
  have massNonneg : 0 ≤ mass := by
    unfold mass puncturedWholeVorticityEuclideanMass
    exact tsum_nonneg fun wave =>
      complexCoordinateAmplitudeSq_nonneg _
  have energyNonneg : 0 ≤ energy := by
    exact puncturedWholeVorticityKineticMass_nonneg (left - right)
  have sharpBound :
      |wholeStateVorticityNonlinearDifferenceKineticPairing
          left right leftTransverse rightTransverse
          leftGradientSummable rightGradientSummable
          (summable_wholeStateVorticityGradientDensity_sub
            left right leftGradientSummable rightGradientSummable)| ≤
        majorant * Real.sqrt energy * Real.sqrt mass := by
    simpa [mass, energy, majorant] using
      wholeStateVorticityNonlinearDifferenceKineticPairing_abs_le
        left right leftZeroRow rightZeroRow
        leftTransverse rightTransverse
        leftReality rightReality
        leftGradientSummable rightGradientSummable
  have young :=
    two_mul_le_add_mul_sq
      (a := Real.sqrt mass)
      (b := majorant * Real.sqrt energy)
      νPos
  have doubled :
      2 *
          |wholeStateVorticityNonlinearDifferenceKineticPairing
            left right leftTransverse rightTransverse
            leftGradientSummable rightGradientSummable
            (summable_wholeStateVorticityGradientDensity_sub
              left right
              leftGradientSummable rightGradientSummable)| ≤
        ν * mass + ν⁻¹ * majorant ^ 2 * energy := by
    calc
      2 *
          |wholeStateVorticityNonlinearDifferenceKineticPairing
            left right leftTransverse rightTransverse
            leftGradientSummable rightGradientSummable
            (summable_wholeStateVorticityGradientDensity_sub
              left right
              leftGradientSummable rightGradientSummable)| ≤
        2 * (majorant * Real.sqrt energy * Real.sqrt mass) :=
        mul_le_mul_of_nonneg_left sharpBound (by norm_num)
      _ = 2 * Real.sqrt mass * (majorant * Real.sqrt energy) := by
        ring
      _ ≤
        ν * Real.sqrt mass ^ 2 +
          ν⁻¹ * (majorant * Real.sqrt energy) ^ 2 :=
        young
      _ = ν * mass + ν⁻¹ * majorant ^ 2 * energy := by
        rw [Real.sq_sqrt massNonneg, mul_pow,
          Real.sq_sqrt energyNonneg]
        ring
  dsimp [mass, energy, majorant] at doubled
  nlinarith

/-- One-sided whole-lattice form consumed directly by the difference
kinetic ledger. -/
theorem wholeStateVorticityNonlinearDifferenceKineticPairing_le_young
    (left right : ComplexVorticityHilbertState)
    (leftZeroRow : left 0 = 0)
    (rightZeroRow : right 0 = 0)
    (leftTransverse : WholeStateTransverse left)
    (rightTransverse : WholeStateTransverse right)
    (leftReality : FiniteStateFourierReality left)
    (rightReality : FiniteStateFourierReality right)
    (leftGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (left wave))
    (rightGradientSummable :
      Summable fun wave : IntegerWavevector =>
        integerWaveNormSq wave *
          complexCoordinateAmplitudeSq (right wave))
    (ν : ℝ)
    (νPos : 0 < ν) :
    wholeStateVorticityNonlinearDifferenceKineticPairing
        left right leftTransverse rightTransverse
        leftGradientSummable rightGradientSummable
        (summable_wholeStateVorticityGradientDensity_sub
          left right leftGradientSummable rightGradientSummable) ≤
      (ν / 2) *
          puncturedWholeVorticityEuclideanMass (left - right) +
        (ν⁻¹ / 2) * wholeStateVelocityMajorant left ^ 2 *
          puncturedWholeVorticityKineticMass (left - right) := by
  exact le_trans (le_abs_self _)
    (wholeStateVorticityNonlinearDifferenceKineticPairing_abs_le_young
      left right leftZeroRow rightZeroRow
      leftTransverse rightTransverse
      leftReality rightReality
      leftGradientSummable rightGradientSummable ν νPos)

end

end ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
end NavierStokes
end SaturationMonoid
