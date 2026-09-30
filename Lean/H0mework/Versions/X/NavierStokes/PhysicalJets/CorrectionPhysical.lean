import H0mework.Versions.X.NavierStokes.PhysicalJets.Correction

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeCorrectionPhysical

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientPhysicalCompiler
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent
open NativeFullOrderAction NativeFullOrderSynthesis NativeFullOrderCorrection NativeFullOrderFlux
open NativePhysicalContinuous

noncomputable section

theorem mode_eq_original (state : ComplexVorticityHilbertState) (wave : IntegerWavevector) :
    mode state wave = realComplexFourierMode wave (state wave) := by
  funext point
  apply PiLp.ext
  intro coordinate
  change (state wave coordinate * UnitAddTorus.mFourier wave (circlePoint point)).re = _
  rw [monomial_phase]
  simp only [profile, Complex.mul_re, Complex.exp_re, Complex.exp_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
    Real.exp_zero, one_mul, phase_apply, realComplexFourierMode,
    PiLp.sub_apply, PiLp.smul_apply, coefficientReal_apply, coefficientImag_apply,
    smul_eq_mul, integerCosine, integerSine, integerWavePhase]
  ring

theorem finite_amplitude_paid (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    Summable (amplitude (finiteComplexVorticityState modes coefficient)) :=
  summable_of_ne_finset_zero (s := modes) fun wave outside => by
    simp [amplitude, vorticityRowAmplitude, outside, complexCoordinateAmplitudeSq]

theorem spatialField_finite_compiler (modes : Finset IntegerWavevector)
    (coefficient : IntegerWavevector → ComplexCoordinateVector) :
    spatialField (finiteComplexVorticityState modes coefficient) =
      finiteRealComplexFourierField modes coefficient := by
  rw [spatialField_eq_tsum _ (finite_amplitude_paid modes coefficient)]
  funext point
  rw [tsum_eq_sum (s := modes)]
  · apply Finset.sum_congr rfl
    intro wave inside
    rw [mode_eq_original, finiteComplexVorticityState_apply, if_pos inside]
  · intro wave outside
    rw [mode_eq_original, finiteComplexVorticityState_apply, if_neg outside]
    simp [realComplexFourierMode]

theorem spatialField_sub (left right : ComplexVorticityHilbertState)
    (leftPaid : Summable (amplitude left)) (rightPaid : Summable (amplitude right)) :
    spatialField (left - right) = spatialField left - spatialField right := by
  have scalar (coordinate : Coordinate) : scalarContinuous (left - right) coordinate =
      scalarContinuous left coordinate - scalarContinuous right coordinate := by
    unfold scalarContinuous
    simp only [lp.coeFn_sub, Pi.sub_apply]
    convert! (scalarSummable left coordinate leftPaid).tsum_sub
      (scalarSummable right coordinate rightPaid) using 1
    apply tsum_congr
    intro wave
    ext point
    simp [sub_mul]
  funext point
  apply PiLp.ext
  intro coordinate
  change (scalarContinuous (left - right) coordinate (circlePoint point)).re = _
  rw [scalar]
  rfl

def outputModes (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    Finset IntegerWavevector :=
  generatedStretchingOutputInventory
    (rawSourceOfFiniteVorticityState modes (complexSharpSupportProjection modes state))

theorem resolved_nonlinear_supported (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0)
    (wave : IntegerWavevector) (outside : wave ∉ outputModes modes state) :
    wholeStateVorticityNonlinearCoefficientAt (complexSharpSupportProjection modes state) wave = 0 := by
  rw [wholeStateVorticityNonlinearCoefficientAt_projection_eq_finite]
  unfold finiteStateVorticityNonlinearCoefficientAt
  apply Finset.sum_eq_zero
  intro first firstMem
  apply Finset.sum_eq_zero
  intro second secondMem
  by_cases firstZero : first = 0
  · subst first
    simp [finiteStateVorticityNonlinearPairContribution_zero_first, zero]
  by_cases secondZero : second = 0
  · subst second
    simp [finiteStateVorticityNonlinearPairContribution_zero_second, zero]
  have notOutput : first + second ≠ wave := by
    intro same
    apply outside
    apply (mem_generatedStretchingOutputInventory_iff _ _).mpr
    refine ⟨(first, second), ?_, same⟩
    apply (mem_generatedStretchingPairTable_iff _ _).mpr
    constructor
    · exact Finset.mem_erase.mpr ⟨firstZero, Finset.mem_union_left _ firstMem⟩
    · exact Finset.mem_erase.mpr ⟨secondZero, Finset.mem_union_left _ secondMem⟩
  simp only [if_neg notOutput]

def correctionState (modes : Finset IntegerWavevector) (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState modes (wholeStateVorticityNonlinearCoefficientAt state) -
    finiteComplexVorticityState (outputModes modes state)
      (wholeStateVorticityNonlinearCoefficientAt (complexSharpSupportProjection modes state))

theorem correctionState_apply (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) (zero : state 0 = 0) (wave : IntegerWavevector) :
    correctionState modes state wave = nativeTurbulenceCorrectionAt modes state wave := by
  simp only [correctionState, lp.coeFn_sub, Pi.sub_apply, finiteComplexVorticityState_apply]
  unfold nativeTurbulenceCorrectionAt projectedWholeNonlinearCoefficientAt
  by_cases inside : wave ∈ outputModes modes state
  · rw [if_pos inside]
  · rw [if_neg inside, resolved_nonlinear_supported modes state zero wave inside]

theorem correctionState_physical_eq_original (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    spatialField (correctionState modes state) = nativeTurbulenceCorrectionField modes state := by
  rw [correctionState, spatialField_sub _ _ (finite_amplitude_paid _ _) (finite_amplitude_paid _ _),
    spatialField_finite_compiler, spatialField_finite_compiler]
  rfl

def correctionJetBudget (order index : ℕ) : ℝ :=
  (2 * Real.pi) ^ order *
    ((9 * (2 * Real.pi) ^ 4 * (4 * sourceFluxBudget (order + 4) index) + ∑' wave, decay wave) / 2)

theorem run_correction_square_control (modes : Finset IntegerWavevector) (order index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    let field := correctionState modes ((run stackedShortCurrent index).receipt.wholePath time)
    (Summable fun wave => frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (field wave)) ∧
      (∑' wave, frequencySize wave ^ (2 * order) * complexCoordinateAmplitudeSq (field wave)) ≤
        9 * (2 * Real.pi) ^ 4 * (4 * sourceFluxBudget (order + 2) index) := by
  dsimp only
  simp_rw [correctionState_apply modes _ ((run stackedShortCurrent index).receipt.wholePath_zero_row time)]
  simpa only [← pow_mul, Nat.mul_comm order 2] using run_native_correction_control modes order index time

theorem run_native_correction_spatial_control (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
        (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time)) ∧
      ∀ order point, ‖iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time)) point‖ ≤
          correctionJetBudget order index := by
  rw [← correctionState_physical_eq_original]
  have moments order := (run_correction_square_control modes order index time).1
  refine ⟨spatialField_smooth_of_square _ moments, ?_⟩
  intro order point
  apply (spatialField_bound_of_square _ moments order point).trans
  unfold correctionJetBudget
  gcongr
  exact (run_correction_square_control modes (order + 2) index time).2

theorem run_native_correction_word_eq (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (order : ℕ) (point : PhysicalSpace) (directions : Fin order → PhysicalSpace) :
    iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time))
        point directions =
      ∑' wave, WithLp.toLp 2 fun coordinate =>
        (nativeTurbulenceCorrectionAt modes ((run stackedShortCurrent index).receipt.wholePath time) wave coordinate *
          ((∏ index, phase wave (directions index)) •
            (Complex.I ^ order * UnitAddTorus.mFourier wave (circlePoint point)))).re := by
  rw [← correctionState_physical_eq_original]
  have moments m := summable_moment_of_square _ m (run_correction_square_control modes (m + 2) index time).1
  rw [spatialField_word_eq _ moments]
  apply tsum_congr
  intro wave
  unfold value
  rw [correctionState_apply modes _ ((run stackedShortCurrent index).receipt.wholePath_zero_row time)]

theorem run_native_correction_spatial_Lp (modes : Finset IntegerWavevector) (index : ℕ)
    (time : Icc (0 : ℝ) (run stackedShortCurrent index).duration)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set PhysicalSpace} (compact : IsCompact domain) :
    MemLp (iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time)))
        exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order
        (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time)))
        exponent (volume.restrict domain) ≤
          ENNReal.ofReal (correctionJetBudget order index) * volume domain ^ (1 / exponent.toReal) := by
  let : IsFiniteMeasure (volume.restrict domain) := ⟨by simpa using compact.measure_lt_top (μ := volume)⟩
  have actual := run_native_correction_spatial_control modes index time
  have continuous := ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) actual.1 (m := order)
  have aeBound : ∀ᵐ point ∂volume.restrict domain, ‖iteratedFDeriv ℝ order
      (nativeTurbulenceCorrectionField modes ((run stackedShortCurrent index).receipt.wholePath time)) point‖ ≤
        correctionJetBudget order index := Eventually.of_forall (actual.2 order)
  exact ⟨MemLp.of_bound continuous.aestronglyMeasurable _ aeBound,
    by simpa [mul_comm] using eLpNorm_le_of_ae_bound (p := exponent) aeBound⟩

end
end SaturationMonoid.NavierStokes.NativeCorrectionPhysical
