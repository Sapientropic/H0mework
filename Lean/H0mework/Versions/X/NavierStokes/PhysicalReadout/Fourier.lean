import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import H0mework.NavierStokes.SourceReadout.MomentumFlux
import H0mework.Versions.X.NavierStokes.NormControl.Global
import H0mework.NavierStokes.PhysicalReadout.FourierProduct
import H0mework.NavierStokes.PhysicalReadout.FourierReality

set_option autoImplicit false
open scoped BigOperators ENNReal

namespace SaturationMonoid.NavierStokes.NativePhysicalFourier

open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory

noncomputable section

abbrev Torus := UnitAddTorus Coordinate

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev ScalarField := Lp ℂ 2 (volume : Measure Torus)
abbrev ScalarSequence := lp (fun _ : IntegerWavevector => ℂ) 2

/-- Each coordinate is extracted from the complete source Fourier state. -/
def scalarSequence (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate) : ScalarSequence :=
  ⟨fun wave => velocity wave coordinate, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun wave => ?_) (summable_vorticityRowAmplitude_sq velocity)
    rw [vorticityRowAmplitude_sq, ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun index _ => Complex.normSq_nonneg _) (Finset.mem_univ coordinate)⟩

/-- Inverse Fourier realization on the whole three-torus, with no finite observation table. -/
def scalarField (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate) : ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (scalarSequence velocity coordinate)

theorem scalarField_fourier (velocity : ComplexVorticityHilbertState)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (scalarField velocity coordinate) wave = velocity wave coordinate := by
  rw [← UnitAddTorus.mFourierBasis_repr]
  exact congrArg (fun sequence : ScalarSequence => sequence wave)
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.apply_symm_apply
      (scalarSequence velocity coordinate))

theorem scalarField_norm_sq (velocity : ComplexVorticityHilbertState) (coordinate : Coordinate) :
    ‖scalarField velocity coordinate‖ ^ 2 = ∑' wave, ‖velocity wave coordinate‖ ^ 2 := by
  rw [scalarField, LinearIsometryEquiv.norm_map]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scalarSequence] using
    lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (scalarSequence velocity coordinate)

def vectorValue (velocity : ComplexVorticityHilbertState) (point : Torus) : EuclideanSpace ℂ Coordinate :=
  WithLp.toLp 2 fun coordinate => scalarField velocity coordinate point

theorem vectorValue_memLp (velocity : ComplexVorticityHilbertState) :
    MemLp (vectorValue velocity) 2 (volume : Measure Torus) := by
  apply memLp_piLp_iff.mpr
  intro coordinate
  exact Lp.memLp (scalarField velocity coordinate)

/-- The original full field in physical space, on its complete Euclidean L² carrier. -/
def vectorField (velocity : ComplexVorticityHilbertState) :
    Lp (EuclideanSpace ℂ Coordinate) 2 (volume : Measure Torus) :=
  (vectorValue_memLp velocity).toLp (vectorValue velocity)

theorem vectorField_apply (velocity : ComplexVorticityHilbertState) :
    vectorField velocity =ᵐ[volume] vectorValue velocity := (vectorValue_memLp velocity).coeFn_toLp

theorem vectorValue_fourier (velocity : ComplexVorticityHilbertState)
    (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point => vectorValue velocity point coordinate) wave =
      velocity wave coordinate := scalarField_fourier velocity coordinate wave

theorem scalarField_sum_norm_sq (velocity : ComplexVorticityHilbertState) :
    (∑ coordinate : Coordinate, ‖scalarField velocity coordinate‖ ^ 2) =
      wholeVorticityEuclideanMass velocity := by
  have summable (coordinate : Coordinate) : Summable (fun wave => ‖velocity wave coordinate‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, scalarSequence] using
      (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (scalarSequence velocity coordinate)).summable
  simp_rw [scalarField_norm_sq]
  rw [← Summable.tsum_finsetSum (fun coordinate _ => summable coordinate)]
  apply tsum_congr
  intro wave
  simp only [vorticityRowAmplitude_sq,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  unfold complexCoordinateAmplitudeSq
  simp only [Complex.normSq_eq_norm_sq]

private theorem l2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (field : Lp E 2 (volume : Measure Torus)) :
    ‖field‖ ^ 2 = ∫ point, ‖field point‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Physical Parseval uses the full Euclidean vector norm, with no dimension factor. -/
theorem vectorField_norm_sq (velocity : ComplexVorticityHilbertState) :
    ‖vectorField velocity‖ ^ 2 = wholeVorticityEuclideanMass velocity := by
  rw [l2_norm_sq]
  calc
    (∫ point : Torus, ‖vectorField velocity point‖ ^ 2) =
        ∫ point : Torus, ∑ coordinate : Coordinate, ‖scalarField velocity coordinate point‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [vectorField_apply velocity] with point actual
      rw [actual, EuclideanSpace.norm_sq_eq]
      rfl
    _ = ∑ coordinate : Coordinate, ∫ point : Torus, ‖scalarField velocity coordinate point‖ ^ 2 := by
      exact integral_finsetSum Finset.univ (fun coordinate _ => (Lp.memLp _).norm.integrable_sq)
    _ = ∑ coordinate : Coordinate, ‖scalarField velocity coordinate‖ ^ 2 := by
      exact Finset.sum_congr rfl (fun coordinate _ => (l2_norm_sq _).symm)
    _ = _ := scalarField_sum_norm_sq velocity

/-- The actual complete physical product has the original all-pair Fourier stress. -/
theorem physical_flux_fourier (velocity : ComplexVorticityHilbertState)
    (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff
      (fun point => -(scalarField velocity input point * scalarField velocity output point)) wave =
      NativeStressSource.quadraticFlux velocity wave output input := by
  have product := NativeFourierProduct.product_coeff (scalarField velocity input)
    (scalarField velocity output) wave
  simp_rw [scalarField_fourier] at product
  change (∫ point : Torus, UnitAddTorus.mFourier (-wave) point •
    -(scalarField velocity input point * scalarField velocity output point)) = _
  simp only [smul_neg, integral_neg]
  exact congrArg Neg.neg product

theorem scalarField_real (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) (coordinate : Coordinate) :
    ∀ᵐ point ∂(volume : Measure Torus), (scalarField velocity coordinate point).im = 0 := by
  apply NativeFourierReality.inverseFourier_im_ae_zero (scalarSequence velocity coordinate)
  intro wave
  change velocity (-wave) coordinate = star (velocity wave coordinate)
  have negEq : -wave = waveNeg wave := by
    funext direction
    rfl
  rw [negEq, reality wave]
  rfl

def realValue (velocity : ComplexVorticityHilbertState) (point : Torus) : PhysicalSpace :=
  WithLp.toLp 2 fun coordinate => (scalarField velocity coordinate point).re

theorem realValue_memLp (velocity : ComplexVorticityHilbertState) :
    MemLp (realValue velocity) 2 (volume : Measure Torus) := by
  apply memLp_piLp_iff.mpr
  intro coordinate
  exact Complex.reCLM.comp_memLp (scalarField velocity coordinate)

def realField (velocity : ComplexVorticityHilbertState) : Lp PhysicalSpace 2 (volume : Measure Torus) :=
  (realValue_memLp velocity).toLp (realValue velocity)

theorem realField_apply (velocity : ComplexVorticityHilbertState) :
    realField velocity =ᵐ[volume] realValue velocity := (realValue_memLp velocity).coeFn_toLp

theorem realValue_recovers_complex (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) :
    ∀ᵐ point ∂(volume : Measure Torus), ∀ coordinate : Coordinate,
      (realValue velocity point coordinate : ℂ) = scalarField velocity coordinate point := by
  have all := ae_all_iff.mpr (fun coordinate => scalarField_real velocity reality coordinate)
  filter_upwards [all] with point real coordinate
  apply Complex.ext
  · rfl
  · exact (real coordinate).symm

theorem realField_norm_sq (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) :
    ‖realField velocity‖ ^ 2 = wholeVorticityEuclideanMass velocity := by
  rw [l2_norm_sq, ← vectorField_norm_sq velocity, l2_norm_sq]
  apply integral_congr_ae
  filter_upwards [realField_apply velocity, vectorField_apply velocity,
    realValue_recovers_complex velocity reality] with point actual complexActual real
  rw [actual, complexActual, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro coordinate _
  change ‖realValue velocity point coordinate‖ ^ 2 = ‖scalarField velocity coordinate point‖ ^ 2
  rw [← real coordinate, Complex.norm_real]

theorem realField_fourier (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) (coordinate : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff
      (fun point => (realField velocity point coordinate : ℂ)) wave = velocity wave coordinate := by
  rw [← scalarField_fourier velocity coordinate wave]
  apply integral_congr_ae
  filter_upwards [realField_apply velocity,
    realValue_recovers_complex velocity reality] with point actual real
  rw [actual, real coordinate]

/-- No original Fourier coordinate is lost on the source's real physical carrier. -/
theorem realField_faithful (left right : ComplexVorticityHilbertState)
    (leftReality : FiniteStateFourierReality left) (rightReality : FiniteStateFourierReality right)
    (same : realField left = realField right) : left = right := by
  apply lp.ext
  funext wave coordinate
  rw [← realField_fourier left leftReality coordinate wave,
    ← realField_fourier right rightReality coordinate wave, same]

theorem real_product_integrable (velocity : ComplexVorticityHilbertState) (output input : Coordinate) :
    Integrable (fun point => -(realField velocity point input * realField velocity point output))
      (volume : Measure Torus) := by
  have each := memLp_piLp_iff.mp (Lp.memLp (realField velocity))
  exact memLp_one_iff_integrable.mp ((each output).mul' (each input)).neg

/-- Fourier transformation of the actual whole-space real momentum tensor recovers the source Q. -/
theorem real_flux_fourier (velocity : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality velocity) (output input : Coordinate) (wave : IntegerWavevector) :
    UnitAddTorus.mFourierCoeff (fun point =>
      ((-(realField velocity point input * realField velocity point output) : ℝ) : ℂ)) wave =
      NativeStressSource.quadraticFlux velocity wave output input := by
  have actual := physical_flux_fourier velocity output input wave
  have realEach := realValue_recovers_complex velocity reality
  rw [← actual]
  apply integral_congr_ae
  filter_upwards [realField_apply velocity, realEach] with point fieldEq real
  rw [fieldEq]
  push_cast
  rw [real input, real output]

private theorem scalarField_add (left right : ComplexVorticityHilbertState) (coordinate : Coordinate) :
    scalarField (left + right) coordinate = scalarField left coordinate + scalarField right coordinate := by
  have sequence : scalarSequence (left + right) coordinate =
      scalarSequence left coordinate + scalarSequence right coordinate := by
    apply lp.ext
    rfl
  exact (congrArg (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm sequence).trans
    ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.map_add _ _)

private theorem scalarField_real_smul (scalar : ℝ) (velocity : ComplexVorticityHilbertState)
    (coordinate : Coordinate) :
    scalarField (scalar • velocity) coordinate = scalar • scalarField velocity coordinate := by
  have sequence : scalarSequence (scalar • velocity) coordinate =
      scalar • scalarSequence velocity coordinate := by
    apply lp.ext
    rfl
  rw [scalarField, sequence]
  exact ((UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.restrictScalars ℝ).map_smul scalar _

theorem realField_add (left right : ComplexVorticityHilbertState) :
    realField (left + right) = realField left + realField right := by
  apply Lp.ext
  have each (coordinate : Coordinate) :
      scalarField (left + right) coordinate =ᵐ[volume]
        (fun point => scalarField left coordinate point + scalarField right coordinate point) := by
    rw [scalarField_add]
    exact Lp.coeFn_add _ _
  filter_upwards [realField_apply (left + right), realField_apply left, realField_apply right,
    Lp.coeFn_add (realField left) (realField right), ae_all_iff.mpr each]
    with point sumField leftField rightField fieldSum scalars
  rw [sumField, fieldSum, Pi.add_apply, leftField, rightField]
  apply PiLp.ext
  intro coordinate
  change (scalarField (left + right) coordinate point).re = _
  rw [scalars coordinate, Complex.add_re]
  rfl

theorem realField_smul (scalar : ℝ) (velocity : ComplexVorticityHilbertState) :
    realField (scalar • velocity) = scalar • realField velocity := by
  apply Lp.ext
  have each (coordinate : Coordinate) : scalarField (scalar • velocity) coordinate =ᵐ[volume]
      (fun point => scalar • scalarField velocity coordinate point) := by
    rw [scalarField_real_smul]
    exact Lp.coeFn_smul _ _
  filter_upwards [realField_apply (scalar • velocity), realField_apply velocity,
    Lp.coeFn_smul scalar (realField velocity), ae_all_iff.mpr each]
    with point scaledField sourceField fieldScale scalars
  rw [scaledField, fieldScale, Pi.smul_apply, sourceField]
  apply PiLp.ext
  intro coordinate
  change (scalarField (scalar • velocity) coordinate point).re = _
  rw [scalars coordinate]
  simp [realValue]

theorem realField_norm_le (velocity : ComplexVorticityHilbertState) :
    ‖realField velocity‖ ≤ Real.sqrt 3 * ‖velocity‖ := by
  have realLe : ‖realField velocity‖ ≤ ‖vectorField velocity‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [realField_apply velocity, vectorField_apply velocity] with point real complexField
    rw [real, complexField]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro coordinate _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    change ‖(scalarField velocity coordinate point).re‖ ≤ ‖scalarField velocity coordinate point‖
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
  apply realLe.trans
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [vectorField_norm_sq, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact wholeVorticityEuclideanMass_le_three_mul_norm_sq velocity

/-- The whole physical realization commutes with source time calculus and action integrals. -/
def realFieldCLM : ComplexVorticityHilbertState →L[ℝ] Lp PhysicalSpace 2 (volume : Measure Torus) :=
  LinearMap.mkContinuous
    { toFun := realField
      map_add' := realField_add
      map_smul' := realField_smul }
    (Real.sqrt 3) realField_norm_le

end
end SaturationMonoid.NavierStokes.NativePhysicalFourier
