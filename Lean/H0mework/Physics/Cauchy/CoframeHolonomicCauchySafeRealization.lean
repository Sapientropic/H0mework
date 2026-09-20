import H0mework.Physics.Coframe.CurrentCoframeMatterTemporalPrincipal
import H0mework.Physics.Holonomic.CoframeHolonomicMatrixExponentialRealization
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Globally noncharacteristic realization of a coframe second jet

This module constructs the algebraic core of a source-generated Cauchy-safe
coframe realization.  The constructor has a positive lapse, an arbitrary
shift, and an arbitrary invertible spatial coframe.  No equation residual,
target field, support, or noncharacteristic certificate enters its value.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicCauchySafeRealization

open ProofFreeRicherAnholonomicSource
open DiracExteriorMatterAction
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCoframeHolonomicMatrixExponentialRealization
open StageNineHolonomicField
open scoped ComplexOrder ContDiff Matrix Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

/-- Lower block-triangular time-gauge coframe. -/
def timeGaugeCoframe
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ) :
    LorentzianCoframe :=
  Matrix.of ![![lapse, 0, 0, 0],
    ![shift 0, spatial 0 0, spatial 0 1, spatial 0 2],
    ![shift 1, spatial 1 0, spatial 1 1, spatial 1 2],
    ![shift 2, spatial 2 0, spatial 2 1, spatial 2 2]]

/-- Explicit inverse candidate for the lower block-triangular coframe. -/
def timeGaugeCoframeInverse
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ) :
    LorentzianCoframe :=
  Matrix.of ![![lapse⁻¹, 0, 0, 0],
    ![-lapse⁻¹ * ∑ index : Fin 3, spatial⁻¹ 0 index * shift index,
      spatial⁻¹ 0 0, spatial⁻¹ 0 1, spatial⁻¹ 0 2],
    ![-lapse⁻¹ * ∑ index : Fin 3, spatial⁻¹ 1 index * shift index,
      spatial⁻¹ 1 0, spatial⁻¹ 1 1, spatial⁻¹ 1 2],
    ![-lapse⁻¹ * ∑ index : Fin 3, spatial⁻¹ 2 index * shift index,
      spatial⁻¹ 2 0, spatial⁻¹ 2 1, spatial⁻¹ 2 2]]

theorem timeGaugeCoframeInverse_mul
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ)
    (lapseNonzero : lapse ≠ 0)
    (spatialNondegenerate : Matrix.det spatial ≠ 0) :
    timeGaugeCoframeInverse lapse shift spatial *
        timeGaugeCoframe lapse shift spatial = 1 := by
  have spatialInverse : spatial⁻¹ * spatial = 1 :=
    Matrix.nonsing_inv_mul spatial (isUnit_iff_ne_zero.mpr spatialNondegenerate)
  have spatialEntry
      (row column : Fin 3) :
      ∑ index : Fin 3, spatial⁻¹ row index * spatial index column =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) row column := by
    exact congrFun (congrFun spatialInverse row) column
  have h00 :
      spatial⁻¹ 0 0 * spatial 0 0 +
          spatial⁻¹ 0 1 * spatial 1 0 +
          spatial⁻¹ 0 2 * spatial 2 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 0 0
  have h01 :
      spatial⁻¹ 0 0 * spatial 0 1 +
          spatial⁻¹ 0 1 * spatial 1 1 +
          spatial⁻¹ 0 2 * spatial 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 0 1
  have h02 :
      spatial⁻¹ 0 0 * spatial 0 2 +
          spatial⁻¹ 0 1 * spatial 1 2 +
          spatial⁻¹ 0 2 * spatial 2 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 0 2
  have h10 :
      spatial⁻¹ 1 0 * spatial 0 0 +
          spatial⁻¹ 1 1 * spatial 1 0 +
          spatial⁻¹ 1 2 * spatial 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 1 0
  have h11 :
      spatial⁻¹ 1 0 * spatial 0 1 +
          spatial⁻¹ 1 1 * spatial 1 1 +
          spatial⁻¹ 1 2 * spatial 2 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 1 1
  have h12 :
      spatial⁻¹ 1 0 * spatial 0 2 +
          spatial⁻¹ 1 1 * spatial 1 2 +
          spatial⁻¹ 1 2 * spatial 2 2 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 1 2
  have h20 :
      spatial⁻¹ 2 0 * spatial 0 0 +
          spatial⁻¹ 2 1 * spatial 1 0 +
          spatial⁻¹ 2 2 * spatial 2 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 2 0
  have h21 :
      spatial⁻¹ 2 0 * spatial 0 1 +
          spatial⁻¹ 2 1 * spatial 1 1 +
          spatial⁻¹ 2 2 * spatial 2 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 2 1
  have h22 :
      spatial⁻¹ 2 0 * spatial 0 2 +
          spatial⁻¹ 2 1 * spatial 1 2 +
          spatial⁻¹ 2 2 * spatial 2 2 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three] using spatialEntry 2 2
  ext row column
  rw [Matrix.mul_apply]
  fin_cases row <;> fin_cases column <;>
    simp [timeGaugeCoframeInverse, timeGaugeCoframe,
      Fin.sum_univ_four, Fin.sum_univ_three, lapseNonzero]
  all_goals try assumption
  all_goals field_simp [lapseNonzero]
  all_goals ring

theorem timeGaugeCoframe_inv
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ)
    (lapseNonzero : lapse ≠ 0)
    (spatialNondegenerate : Matrix.det spatial ≠ 0) :
    (timeGaugeCoframe lapse shift spatial)⁻¹ =
      timeGaugeCoframeInverse lapse shift spatial := by
  exact Matrix.inv_eq_left_inv
    (timeGaugeCoframeInverse_mul lapse shift spatial lapseNonzero
      spatialNondegenerate)

theorem timeGaugeCoframe_det_ne_zero
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ)
    (lapseNonzero : lapse ≠ 0)
    (spatialNondegenerate : Matrix.det spatial ≠ 0) :
    Matrix.det (timeGaugeCoframe lapse shift spatial) ≠ 0 := by
  have inverseProduct := congrArg Matrix.det
    (timeGaugeCoframeInverse_mul lapse shift spatial lapseNonzero
      spatialNondegenerate)
  rw [Matrix.det_mul, Matrix.det_one] at inverseProduct
  intro singular
  rw [singular, mul_zero] at inverseProduct
  norm_num at inverseProduct

/-- The fixed coordinate-time principal is exactly the inverse lapse square;
the shift and spatial coframe cannot make the slice characteristic. -/
theorem timeGaugeCoframe_temporalPrincipalScalar
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ)
    (lapseNonzero : lapse ≠ 0)
    (spatialNondegenerate : Matrix.det spatial ≠ 0) :
    coframeTemporalPrincipalScalar
        (timeGaugeCoframe lapse shift spatial) = lapse⁻¹ ^ 2 := by
  rw [coframeTemporalPrincipalScalar,
    timeGaugeCoframe_inv lapse shift spatial lapseNonzero
      spatialNondegenerate]
  simp [timeGaugeCoframeInverse, minkowskiInternalSign,
    Fin.sum_univ_four]

theorem timeGaugeCoframe_noncharacteristic
    (lapse : ℝ)
    (shift : Fin 3 → ℝ)
    (spatial : Matrix (Fin 3) (Fin 3) ℝ)
    (lapseNonzero : lapse ≠ 0)
    (spatialNondegenerate : Matrix.det spatial ≠ 0) :
    coframeTemporalPrincipalScalar
        (timeGaugeCoframe lapse shift spatial) ≠ 0 := by
  rw [timeGaugeCoframe_temporalPrincipalScalar lapse shift spatial
    lapseNonzero spatialNondegenerate]
  exact pow_ne_zero _ (inv_ne_zero lapseNonzero)

/-! ## A globally Lorentz-safe boost factor -/

/-- The boost part of an arbitrary infinitesimal coframe matrix.  Its three
parameters are read from the time--space row; no equation or target enters. -/
def coframeBoostGenerator
    (matrix : LorentzianCoframe) : LorentzianCoframe :=
  Matrix.of ![![0, matrix 0 1, matrix 0 2, matrix 0 3],
    ![matrix 0 1, 0, 0, 0],
    ![matrix 0 2, 0, 0, 0],
    ![matrix 0 3, 0, 0, 0]]

@[simp] theorem coframeBoostGenerator_zero :
    coframeBoostGenerator 0 = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator]

theorem coframeBoostGenerator_transpose
    (matrix : LorentzianCoframe) :
    (coframeBoostGenerator matrix).transpose =
      coframeBoostGenerator matrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator, Matrix.transpose_apply]

theorem coframeBoostGenerator_minkowskiSkew
    (matrix : LorentzianCoframe) :
    (coframeBoostGenerator matrix).transpose * minkowskiInternalMetric +
        minkowskiInternalMetric * coframeBoostGenerator matrix = 0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator, minkowskiInternalMetric,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four]

private theorem minkowskiInternalMetric_square :
    minkowskiInternalMetric * minkowskiInternalMetric =
      (1 : LorentzianMetric) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [minkowskiInternalMetric, Matrix.mul_apply, Fin.sum_univ_four]

private theorem minkowskiInternalMetric_inverse :
    minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
  exact Matrix.inv_eq_left_inv minkowskiInternalMetric_square

private theorem minkowskiInternalMetric_isUnit :
    IsUnit minkowskiInternalMetric := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [minkowskiInternalMetric, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

theorem coframeBoostGenerator_minkowskiConjugate
    (matrix : LorentzianCoframe) :
    minkowskiInternalMetric * (-coframeBoostGenerator matrix) *
        minkowskiInternalMetric =
      (coframeBoostGenerator matrix).transpose := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator, minkowskiInternalMetric,
      Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four]

open scoped Matrix.Norms.Operator in
/-- The finite boost factor selected by the infinitesimal boost part. -/
def coframeBoostFactor
    (matrix : LorentzianCoframe) : LorentzianCoframe :=
  NormedSpace.exp (coframeBoostGenerator matrix)

open scoped Matrix.Norms.Operator in
@[simp] theorem coframeBoostFactor_zero :
    coframeBoostFactor 0 = 1 := by
  rw [coframeBoostFactor, coframeBoostGenerator_zero]
  exact NormedSpace.exp_zero

open scoped Matrix.Norms.Operator in
theorem coframeBoostFactor_isUnit
    (matrix : LorentzianCoframe) :
    IsUnit (coframeBoostFactor matrix) := by
  exact Matrix.isUnit_exp _

open scoped Matrix.Norms.Operator in
theorem coframeBoostFactor_transpose
    (matrix : LorentzianCoframe) :
    (coframeBoostFactor matrix).transpose = coframeBoostFactor matrix := by
  rw [coframeBoostFactor, ← Matrix.exp_transpose,
    coframeBoostGenerator_transpose]

open scoped Matrix.Norms.Operator in
/-- The finite boost is positive definite: it is the square of its invertible
half-exponential. -/
theorem coframeBoostFactor_posDef
    (matrix : LorentzianCoframe) :
    (coframeBoostFactor matrix).PosDef := by
  let generator := coframeBoostGenerator matrix
  let halfGenerator := (2 : ℝ)⁻¹ • generator
  let halfFactor := NormedSpace.exp halfGenerator
  have halfFactorPositive :
      (halfFactorᴴ * halfFactor).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self halfFactor
      (Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_exp _))
  have halfGeneratorTranspose : halfGenerator.transpose = halfGenerator := by
    dsimp only [halfGenerator]
    rw [Matrix.transpose_smul,
      show generator.transpose = generator by
        simpa [generator] using coframeBoostGenerator_transpose matrix]
  have halfFactorTranspose : halfFactor.transpose = halfFactor := by
    dsimp only [halfFactor]
    rw [← Matrix.exp_transpose, halfGeneratorTranspose]
  have halfFactorConjTranspose : halfFactorᴴ = halfFactor := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      halfFactorTranspose]
  have halfGeneratorAdd : halfGenerator + halfGenerator = generator := by
    ext row column
    simp [halfGenerator]
    ring
  have factorization :
      halfFactorᴴ * halfFactor = coframeBoostFactor matrix := by
    calc
      halfFactorᴴ * halfFactor = halfFactor * halfFactor := by
        rw [halfFactorConjTranspose]
      _ = NormedSpace.exp (halfGenerator + halfGenerator) := by
        exact (NormedSpace.exp_add_of_commute
          (Commute.refl halfGenerator)).symm
      _ = NormedSpace.exp generator := by
        rw [halfGeneratorAdd]
      _ = coframeBoostFactor matrix := by
        rfl
  rw [factorization] at halfFactorPositive
  exact halfFactorPositive

@[simp] theorem coframeBoostGenerator_neg
    (matrix : LorentzianCoframe) :
    coframeBoostGenerator (-matrix) = -coframeBoostGenerator matrix := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator]

open scoped Matrix.Norms.Operator in
theorem coframeBoostFactor_neg
    (matrix : LorentzianCoframe) :
    coframeBoostFactor (-matrix) = (coframeBoostFactor matrix)⁻¹ := by
  rw [coframeBoostFactor, coframeBoostGenerator_neg, Matrix.exp_neg]
  rfl

theorem coframeBoostFactor_inverse_zero_zero_pos
    (matrix : LorentzianCoframe) :
    0 < (coframeBoostFactor matrix)⁻¹ 0 0 := by
  rw [← coframeBoostFactor_neg]
  exact (coframeBoostFactor_posDef (-matrix)).diag_pos

open scoped Matrix.Norms.Operator in
/-- The exponential boost preserves the internal Minkowski metric. -/
theorem coframeBoostFactor_preserves_minkowskiMetric
    (matrix : LorentzianCoframe) :
    (coframeBoostFactor matrix).transpose * minkowskiInternalMetric *
        coframeBoostFactor matrix = minkowskiInternalMetric := by
  let generator := coframeBoostGenerator matrix
  have generatorConjugate :
      minkowskiInternalMetric * (-generator) *
          minkowskiInternalMetric⁻¹ = generator.transpose := by
    rw [minkowskiInternalMetric_inverse]
    exact coframeBoostGenerator_minkowskiConjugate matrix
  have expConjugate :
      NormedSpace.exp generator.transpose =
        minkowskiInternalMetric * NormedSpace.exp (-generator) *
          minkowskiInternalMetric⁻¹ := by
    rw [← generatorConjugate]
    exact Matrix.exp_conj minkowskiInternalMetric (-generator)
      minkowskiInternalMetric_isUnit
  have exponentialInverse :
      (NormedSpace.exp generator)⁻¹ * NormedSpace.exp generator = 1 :=
    Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp generator))
  rw [coframeBoostFactor, ← Matrix.exp_transpose, expConjugate,
    minkowskiInternalMetric_inverse, Matrix.exp_neg]
  calc
    (minkowskiInternalMetric * (NormedSpace.exp generator)⁻¹ *
          minkowskiInternalMetric) *
          minkowskiInternalMetric * NormedSpace.exp generator =
        minkowskiInternalMetric *
          ((NormedSpace.exp generator)⁻¹ *
            NormedSpace.exp generator) := by
      noncomm_ring [minkowskiInternalMetric_square]
    _ = minkowskiInternalMetric := by
      rw [exponentialInverse, Matrix.mul_one]

/-- The inverse boost preserves the inverse internal metric form needed by
the coordinate-row principal symbol. -/
theorem coframeBoostFactor_inverse_preserves_minkowskiMetric
    (matrix : LorentzianCoframe) :
    (coframeBoostFactor matrix)⁻¹ * minkowskiInternalMetric *
        ((coframeBoostFactor matrix)⁻¹).transpose =
      minkowskiInternalMetric := by
  rw [← coframeBoostFactor_neg]
  rw [← coframeBoostFactor_transpose (-matrix)]
  exact coframeBoostFactor_preserves_minkowskiMetric (-matrix)

theorem coframeTemporalPrincipalScalar_eq_inverseMetric
    (coframe : LorentzianCoframe) :
    coframeTemporalPrincipalScalar coframe =
      -((coframe⁻¹ * minkowskiInternalMetric *
          (coframe⁻¹).transpose) 0 0) := by
  simp [coframeTemporalPrincipalScalar, minkowskiInternalMetric,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four,
    minkowskiInternalSign]
  ring

/-- Left multiplication by the generated boost cannot change whether the
fixed coordinate-time slice is characteristic. -/
theorem coframeTemporalPrincipalScalar_boost_mul
    (matrix coframe : LorentzianCoframe) :
    coframeTemporalPrincipalScalar
        (coframeBoostFactor matrix * coframe) =
      coframeTemporalPrincipalScalar coframe := by
  have inverseMetric :=
    coframeBoostFactor_inverse_preserves_minkowskiMetric matrix
  rw [coframeTemporalPrincipalScalar_eq_inverseMetric,
    coframeTemporalPrincipalScalar_eq_inverseMetric,
    Matrix.mul_inv_rev, Matrix.transpose_mul]
  have matrixEquality :
      (coframe⁻¹ * (coframeBoostFactor matrix)⁻¹) *
            minkowskiInternalMetric *
            (((coframeBoostFactor matrix)⁻¹).transpose *
              (coframe⁻¹).transpose) =
          coframe⁻¹ * minkowskiInternalMetric *
            (coframe⁻¹).transpose := by
    calc
      (coframe⁻¹ * (coframeBoostFactor matrix)⁻¹) *
            minkowskiInternalMetric *
            (((coframeBoostFactor matrix)⁻¹).transpose *
              (coframe⁻¹).transpose) =
          coframe⁻¹ *
            ((coframeBoostFactor matrix)⁻¹ * minkowskiInternalMetric *
              ((coframeBoostFactor matrix)⁻¹).transpose) *
            (coframe⁻¹).transpose := by
        noncomm_ring
      _ = coframe⁻¹ * minkowskiInternalMetric *
            (coframe⁻¹).transpose := by
        rw [inverseMetric]
  exact congrArg Neg.neg (congrFun (congrFun matrixEquality 0) 0)

/-! ## The complete global Cauchy-safe chart -/

def coframeSpatialBlock
    (matrix : LorentzianCoframe) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun row column => matrix row.succ column.succ

@[simp] theorem coframeSpatialBlock_zero :
    coframeSpatialBlock 0 = 0 := by
  ext row column
  simp [coframeSpatialBlock]

open scoped Matrix.Norms.Operator in
def coframeSpatialFactor
    (matrix : LorentzianCoframe) : Matrix (Fin 3) (Fin 3) ℝ :=
  NormedSpace.exp (coframeSpatialBlock matrix)

open scoped Matrix.Norms.Operator in
@[simp] theorem coframeSpatialFactor_zero :
    coframeSpatialFactor 0 = 1 := by
  rw [coframeSpatialFactor, coframeSpatialBlock_zero]
  exact NormedSpace.exp_zero

open scoped Matrix.Norms.Operator in
theorem coframeSpatialFactor_det_ne_zero
    (matrix : LorentzianCoframe) :
    Matrix.det (coframeSpatialFactor matrix) ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_exp (coframeSpatialBlock matrix)))

def coframeTimeGaugeFactor
    (matrix : LorentzianCoframe) : LorentzianCoframe :=
  timeGaugeCoframe
    (Real.exp (matrix 0 0))
    (fun spatial => matrix spatial.succ 0 - matrix 0 spatial.succ)
    (coframeSpatialFactor matrix)

@[simp] theorem coframeTimeGaugeFactor_zero :
    coframeTimeGaugeFactor 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeTimeGaugeFactor, timeGaugeCoframe]

/-- A global chart through the identity whose boost part carries the three
missing time--space rows while the time-gauge part keeps coordinate time
strictly noncharacteristic. -/
def cauchySafeCoframeChart
    (matrix : LorentzianCoframe) : LorentzianCoframe :=
  coframeBoostFactor matrix * coframeTimeGaugeFactor matrix

@[simp] theorem cauchySafeCoframeChart_zero :
    cauchySafeCoframeChart 0 = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [cauchySafeCoframeChart, coframeTimeGaugeFactor,
      timeGaugeCoframe, Matrix.mul_apply, Fin.sum_univ_four]

theorem cauchySafeCoframeChart_temporalPrincipalScalar
    (matrix : LorentzianCoframe) :
    coframeTemporalPrincipalScalar (cauchySafeCoframeChart matrix) =
      (Real.exp (matrix 0 0))⁻¹ ^ 2 := by
  rw [cauchySafeCoframeChart,
    coframeTemporalPrincipalScalar_boost_mul]
  exact timeGaugeCoframe_temporalPrincipalScalar _ _ _
    (Real.exp_ne_zero _) (coframeSpatialFactor_det_ne_zero matrix)

theorem cauchySafeCoframeChart_inverse_zero_zero_pos
    (matrix : LorentzianCoframe) :
    0 < (cauchySafeCoframeChart matrix)⁻¹ 0 0 := by
  rw [cauchySafeCoframeChart, Matrix.mul_inv_rev,
    coframeTimeGaugeFactor,
    timeGaugeCoframe_inv _ _ _ (Real.exp_ne_zero _)
      (coframeSpatialFactor_det_ne_zero matrix)]
  simp [timeGaugeCoframeInverse, Matrix.mul_apply,
    Fin.sum_univ_four]
  exact mul_pos (inv_pos.mpr (Real.exp_pos _))
    (coframeBoostFactor_inverse_zero_zero_pos matrix)

theorem cauchySafeCoframeChart_temporalPrincipalScalar_pos
    (matrix : LorentzianCoframe) :
    0 < coframeTemporalPrincipalScalar (cauchySafeCoframeChart matrix) := by
  rw [cauchySafeCoframeChart_temporalPrincipalScalar]
  exact sq_pos_of_pos (inv_pos.mpr (Real.exp_pos _))

/-- The source-generated Cauchy-safe chart has a strictly positive
coordinate-time Dirac evolution coefficient at every point. -/
theorem cauchySafeCoframeChart_coordinateTimeEvolutionPrincipal_posDef
    (matrix : LorentzianCoframe) :
    (coframeCoordinateDiracEvolutionPrincipal
      (cauchySafeCoframeChart matrix) 0).PosDef := by
  exact
    coframeCoordinateDiracEvolutionPrincipal_posDef_of_futureTimelike _
      (cauchySafeCoframeChart_inverse_zero_zero_pos matrix)
      (cauchySafeCoframeChart_temporalPrincipalScalar_pos matrix)

theorem cauchySafeCoframeChart_noncharacteristic
    (matrix : LorentzianCoframe) :
    coframeTemporalPrincipalScalar (cauchySafeCoframeChart matrix) ≠ 0 := by
  rw [cauchySafeCoframeChart_temporalPrincipalScalar]
  exact pow_ne_zero _ (inv_ne_zero (Real.exp_ne_zero _))

theorem cauchySafeCoframeChart_det_ne_zero
    (matrix : LorentzianCoframe) :
    Matrix.det (cauchySafeCoframeChart matrix) ≠ 0 := by
  rw [cauchySafeCoframeChart, Matrix.det_mul]
  apply mul_ne_zero
  · exact isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (coframeBoostFactor_isUnit matrix))
  · exact timeGaugeCoframe_det_ne_zero _ _ _
      (Real.exp_ne_zero _) (coframeSpatialFactor_det_ne_zero matrix)

/-! ## Raw/algebraic exponential bridge -/

private abbrev ProbeCoframeEndSpace :=
  WithLp 2 (LorentzianIndex → ℝ)

private noncomputable def probeCoframeEndAlgEquiv :
    LorentzianCoframe ≃ₐ[ℝ]
      (ProbeCoframeEndSpace →L[ℝ] ProbeCoframeEndSpace) :=
  (Matrix.toLpLinAlgEquiv (R := ℝ) (n := LorentzianIndex) 2).trans
    (Module.End.toContinuousLinearMap ProbeCoframeEndSpace)

private noncomputable def probeCoframeEndContinuousLinearEquiv :
    LorentzianCoframe ≃L[ℝ]
      (ProbeCoframeEndSpace →L[ℝ] ProbeCoframeEndSpace) :=
  probeCoframeEndAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

open scoped Matrix.Norms.Operator in
theorem coframeMatrixExponential_eq_rawMatrixExp
    (matrix : LorentzianCoframe) :
    coframeMatrixExponential matrix = NormedSpace.exp matrix := by
  change probeCoframeEndAlgEquiv.symm
      (NormedSpace.exp (probeCoframeEndAlgEquiv matrix)) = _
  have mappedExponential := NormedSpace.map_exp
    probeCoframeEndAlgEquiv
    probeCoframeEndContinuousLinearEquiv.continuous matrix
  rw [← mappedExponential]
  simp
  rfl

/-! ## First germ of the global chart -/

def coframeBoostGeneratorLinear :
    LorentzianCoframe →ₗ[ℝ] LorentzianCoframe where
  toFun := coframeBoostGenerator
  map_add' := by
    intro first second
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [coframeBoostGenerator]
  map_smul' := by
    intro parameter matrix
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [coframeBoostGenerator]

def coframeBoostGeneratorCLM :
    LorentzianCoframe →L[ℝ] LorentzianCoframe :=
  ⟨coframeBoostGeneratorLinear,
    coframeBoostGeneratorLinear.continuous_of_finiteDimensional⟩

@[simp] theorem coframeBoostGeneratorCLM_apply
    (matrix : LorentzianCoframe) :
    coframeBoostGeneratorCLM matrix = coframeBoostGenerator matrix :=
  rfl

theorem coframeBoostFactor_hasFDerivAt_zero :
    HasFDerivAt coframeBoostFactor coframeBoostGeneratorCLM 0 := by
  have factorEquality :
      coframeBoostFactor = fun matrix =>
        coframeMatrixExponential (coframeBoostGeneratorCLM matrix) := by
    funext matrix
    rw [coframeBoostGeneratorCLM_apply,
      coframeMatrixExponential_eq_rawMatrixExp]
    rfl
  rw [factorEquality]
  have outerDerivative : HasFDerivAt coframeMatrixExponential
      (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe)
      (coframeBoostGeneratorCLM 0) := by
    simpa using coframeMatrixExponential_hasFDerivAt_zero
  have composed :=
    outerDerivative.comp 0 coframeBoostGeneratorCLM.hasFDerivAt
  convert composed using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · funext matrix
    rfl
  · apply heq_of_eq
    ext matrix row column
    rfl

/-! ### Spatial exponential in the canonical elementwise topology -/

private abbrev SpatialMatrix := Matrix (Fin 3) (Fin 3) ℝ

private abbrev ProbeSpatialEndSpace := WithLp 2 (Fin 3 → ℝ)

private noncomputable def probeSpatialEndAlgEquiv :
    SpatialMatrix ≃ₐ[ℝ]
      (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) :=
  (Matrix.toLpLinAlgEquiv (R := ℝ) (n := Fin 3) 2).trans
    (Module.End.toContinuousLinearMap ProbeSpatialEndSpace)

private noncomputable def probeSpatialEndContinuousLinearEquiv :
    SpatialMatrix ≃L[ℝ]
      (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) :=
  probeSpatialEndAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

private local instance probeSpatialEndRatNormedAlgebra :
    NormedAlgebra ℚ
      (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

def spatialMatrixExponential
    (matrix : SpatialMatrix) : SpatialMatrix :=
  probeSpatialEndAlgEquiv.symm
    (NormedSpace.exp (probeSpatialEndAlgEquiv matrix))

theorem spatialMatrixExponential_hasFDerivAt_zero :
    HasFDerivAt spatialMatrixExponential
      (1 : SpatialMatrix →L[ℝ] SpatialMatrix) 0 := by
  have mappedDerivativeRaw :=
    probeSpatialEndContinuousLinearEquiv.hasFDerivAt
      (x := (0 : SpatialMatrix))
  have mappedDerivative :
      HasFDerivAt probeSpatialEndContinuousLinearEquiv
        (probeSpatialEndContinuousLinearEquiv :
          SpatialMatrix →L[ℝ]
            (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace)) 0 := by
    convert mappedDerivativeRaw using 1
    · apply AddCommGroup.ext
      rfl
    · apply Module.ext
      rfl
    · apply TopologicalSpace.ext
      rfl
    · apply AddCommGroup.ext
      rfl
    · apply Module.ext
      rfl
    · apply TopologicalSpace.ext
      rfl
    · rfl
    · exact HEq.rfl
  have exponentialDerivativeAtMappedZero :
      HasFDerivAt
        (NormedSpace.exp :
          (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) →
            (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace))
        (1 :
          (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) →L[ℝ]
            (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace))
        (probeSpatialEndContinuousLinearEquiv (0 : SpatialMatrix)) := by
    simpa using
      (hasFDerivAt_exp_zero :
        HasFDerivAt
          (NormedSpace.exp :
            (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) →
              (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace))
          (1 :
            (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) →L[ℝ]
              (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace)) 0)
  have exponentialDerivativeRaw :=
    exponentialDerivativeAtMappedZero.comp 0 mappedDerivative
  have pulledDerivativeRaw :=
    probeSpatialEndContinuousLinearEquiv.symm.hasFDerivAt.comp 0
      exponentialDerivativeRaw
  convert pulledDerivativeRaw using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · funext matrix
    rfl
  · apply heq_of_eq
    ext matrix row column
    change matrix row column =
      probeSpatialEndContinuousLinearEquiv.symm
        (probeSpatialEndContinuousLinearEquiv matrix) row column
    simp

open scoped Matrix.Norms.Operator in
theorem spatialMatrixExponential_eq_rawMatrixExp
    (matrix : SpatialMatrix) :
    spatialMatrixExponential matrix = NormedSpace.exp matrix := by
  have mappedExponential := NormedSpace.map_exp
    probeSpatialEndAlgEquiv
    probeSpatialEndContinuousLinearEquiv.continuous matrix
  rw [spatialMatrixExponential, ← mappedExponential]
  simp
  rfl

def coframeSpatialBlockLinear :
    LorentzianCoframe →ₗ[ℝ] SpatialMatrix where
  toFun := coframeSpatialBlock
  map_add' := by
    intro first second
    ext row column
    simp [coframeSpatialBlock]
  map_smul' := by
    intro parameter matrix
    ext row column
    simp [coframeSpatialBlock]

def coframeSpatialBlockCLM :
    LorentzianCoframe →L[ℝ] SpatialMatrix :=
  ⟨coframeSpatialBlockLinear,
    coframeSpatialBlockLinear.continuous_of_finiteDimensional⟩

@[simp] theorem coframeSpatialBlockCLM_apply
    (matrix : LorentzianCoframe) :
    coframeSpatialBlockCLM matrix = coframeSpatialBlock matrix :=
  rfl

theorem coframeSpatialFactor_hasFDerivAt_zero :
    HasFDerivAt coframeSpatialFactor coframeSpatialBlockCLM 0 := by
  have factorEquality :
      coframeSpatialFactor = fun matrix =>
        spatialMatrixExponential (coframeSpatialBlockCLM matrix) := by
    funext matrix
    rw [coframeSpatialBlockCLM_apply,
      spatialMatrixExponential_eq_rawMatrixExp]
    rfl
  rw [factorEquality]
  have outerDerivative : HasFDerivAt spatialMatrixExponential
      (1 : SpatialMatrix →L[ℝ] SpatialMatrix)
      (coframeSpatialBlockCLM 0) := by
    simpa using spatialMatrixExponential_hasFDerivAt_zero
  have composed := outerDerivative.comp 0 coframeSpatialBlockCLM.hasFDerivAt
  convert composed using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · funext matrix
    rfl
  · apply heq_of_eq
    ext matrix row column
    rfl

/-! ### The complete time-gauge factor derivative -/

def coframeEntryCLM
    (row column : LorentzianIndex) :
    LorentzianCoframe →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj column :
      (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj row :
      LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))

@[simp] theorem coframeEntryCLM_apply
    (row column : LorentzianIndex)
    (matrix : LorentzianCoframe) :
    coframeEntryCLM row column matrix = matrix row column :=
  rfl

def coframeShiftCLM :
    LorentzianCoframe →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun spatial =>
    coframeEntryCLM spatial.succ 0 - coframeEntryCLM 0 spatial.succ

@[simp] theorem coframeShiftCLM_apply
    (matrix : LorentzianCoframe) (spatial : Fin 3) :
    coframeShiftCLM matrix spatial =
      matrix spatial.succ 0 - matrix 0 spatial.succ :=
  rfl

private abbrev TimeGaugeParameters :=
  ℝ × ((Fin 3 → ℝ) × SpatialMatrix)

def timeGaugeAssemblyLinear :
    TimeGaugeParameters →ₗ[ℝ] LorentzianCoframe where
  toFun parameters :=
    timeGaugeCoframe parameters.1 parameters.2.1 parameters.2.2
  map_add' := by
    intro first second
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [timeGaugeCoframe, Matrix.add_apply]
  map_smul' := by
    intro parameter value
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [timeGaugeCoframe, Matrix.smul_apply]

def timeGaugeAssemblyCLM :
    TimeGaugeParameters →L[ℝ] LorentzianCoframe :=
  ⟨timeGaugeAssemblyLinear,
    timeGaugeAssemblyLinear.continuous_of_finiteDimensional⟩

@[simp] theorem timeGaugeAssemblyCLM_apply
    (parameters : TimeGaugeParameters) :
    timeGaugeAssemblyCLM parameters =
      timeGaugeCoframe parameters.1 parameters.2.1 parameters.2.2 :=
  rfl

def timeGaugeParameterDerivativeCLM :
    LorentzianCoframe →L[ℝ] TimeGaugeParameters :=
  (coframeEntryCLM 0 0).prod
    (coframeShiftCLM.prod coframeSpatialBlockCLM)

def coframeTimeGaugeGeneratorCLM :
    LorentzianCoframe →L[ℝ] LorentzianCoframe :=
  timeGaugeAssemblyCLM.comp timeGaugeParameterDerivativeCLM

theorem coframeTimeGaugeFactor_hasFDerivAt_zero :
    HasFDerivAt coframeTimeGaugeFactor
      coframeTimeGaugeGeneratorCLM 0 := by
  have lapseDerivative : HasFDerivAt
      (fun matrix : LorentzianCoframe => Real.exp (matrix 0 0))
      (coframeEntryCLM 0 0) 0 := by
    have composed := (Real.hasDerivAt_exp 0).hasFDerivAt.comp 0
      (coframeEntryCLM 0 0).hasFDerivAt
    have derivativeEquality :
        (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)).comp
            (coframeEntryCLM 0 0) =
          coframeEntryCLM 0 0 := by
      ext matrix
      simp
    have composedAtZero : HasFDerivAt
        (Real.exp ∘ (coframeEntryCLM 0 0))
        ((ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)).comp
          (coframeEntryCLM 0 0)) 0 := by
      convert composed using 1
      · apply AddCommGroup.ext
        rfl
      · apply Module.ext
        rfl
      · apply TopologicalSpace.ext
        rfl
      · apply AddCommGroup.ext
        rfl
      · apply Module.ext
        rfl
      · apply heq_of_eq
        simp only [Real.exp_zero]
        rfl
    rw [derivativeEquality] at composedAtZero
    simpa [Function.comp_def] using composedAtZero
  have shiftDerivative : HasFDerivAt
      (fun matrix : LorentzianCoframe =>
        fun spatial => matrix spatial.succ 0 - matrix 0 spatial.succ)
      coframeShiftCLM 0 := by
    exact coframeShiftCLM.hasFDerivAt
  have parameterDerivative : HasFDerivAt
      (fun matrix : LorentzianCoframe =>
        (Real.exp (matrix 0 0),
          ((fun spatial =>
              matrix spatial.succ 0 - matrix 0 spatial.succ),
            coframeSpatialFactor matrix)))
      timeGaugeParameterDerivativeCLM 0 := by
    exact lapseDerivative.prodMk
      (shiftDerivative.prodMk coframeSpatialFactor_hasFDerivAt_zero)
  have assembled := timeGaugeAssemblyCLM.hasFDerivAt.comp 0
    parameterDerivative
  convert assembled using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · funext matrix
    rfl
  · exact HEq.rfl

theorem coframeBoost_add_timeGaugeGenerator :
    coframeBoostGeneratorCLM + coframeTimeGaugeGeneratorCLM =
      (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe) := by
  ext matrix row column
  fin_cases row <;> fin_cases column <;>
    simp [coframeBoostGenerator, coframeTimeGaugeGeneratorCLM,
      timeGaugeParameterDerivativeCLM, timeGaugeCoframe,
      coframeSpatialBlock, Matrix.add_apply]

def coframeMatrixRealMulBilinear :
    LorentzianCoframe →ₗ[ℝ]
      LorentzianCoframe →ₗ[ℝ] LorentzianCoframe :=
  mulLinearMap ℝ

@[simp] theorem coframeMatrixRealMulBilinear_apply
    (first second : LorentzianCoframe) :
    coframeMatrixRealMulBilinear.toContinuousBilinearMap first second =
      first * second :=
  rfl

theorem cauchySafeCoframeChart_hasFDerivAt_zero :
    HasFDerivAt cauchySafeCoframeChart
      (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe) 0 := by
  have productDerivative :=
    coframeMatrixRealMulBilinear.toContinuousBilinearMap
      |>.hasFDerivAt_of_bilinear
        coframeBoostFactor_hasFDerivAt_zero
        coframeTimeGaugeFactor_hasFDerivAt_zero
  have derivativeEquality :
      coframeMatrixRealMulBilinear.toContinuousBilinearMap.precompR
          LorentzianCoframe (coframeBoostFactor 0)
            coframeTimeGaugeGeneratorCLM +
        coframeMatrixRealMulBilinear.toContinuousBilinearMap.precompL
          LorentzianCoframe coframeBoostGeneratorCLM
            (coframeTimeGaugeFactor 0) =
        (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe) := by
    rw [coframeBoostFactor_zero, coframeTimeGaugeFactor_zero]
    rw [← coframeBoost_add_timeGaugeGenerator]
    ext matrix row column
    change
      (1 * coframeTimeGaugeGeneratorCLM matrix) row column +
          (coframeBoostGeneratorCLM matrix * 1) row column =
        (coframeBoostGeneratorCLM + coframeTimeGaugeGeneratorCLM)
          matrix row column
    simp [add_comm]
  rw [derivativeEquality] at productDerivative
  convert productDerivative using 1
  constructor <;> intro derivative <;> exact derivative

private theorem probeSpatialEnd_exp_contDiff :
    ContDiff ℝ ∞
      (NormedSpace.exp :
        (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace) →
          (ProbeSpatialEndSpace →L[ℝ] ProbeSpatialEndSpace)) :=
  contDiff_iff_contDiffAt.mpr fun point =>
    (NormedSpace.exp_analytic point).contDiffAt

theorem spatialMatrixExponential_contDiff :
    ContDiff ℝ ∞ spatialMatrixExponential := by
  change ContDiff ℝ ∞ fun matrix =>
    probeSpatialEndContinuousLinearEquiv.symm
      (NormedSpace.exp (probeSpatialEndContinuousLinearEquiv matrix))
  exact probeSpatialEndContinuousLinearEquiv.symm.contDiff.comp
    (probeSpatialEnd_exp_contDiff.comp
      probeSpatialEndContinuousLinearEquiv.contDiff)

theorem coframeBoostFactor_contDiff :
    ContDiff ℝ ∞ coframeBoostFactor := by
  have factorEquality :
      coframeBoostFactor = fun matrix =>
        coframeMatrixExponential (coframeBoostGeneratorCLM matrix) := by
    funext matrix
    rw [coframeBoostGeneratorCLM_apply,
      coframeMatrixExponential_eq_rawMatrixExp]
    rfl
  rw [factorEquality]
  exact coframeMatrixExponential_contDiff.comp
    coframeBoostGeneratorCLM.contDiff

theorem coframeSpatialFactor_contDiff :
    ContDiff ℝ ∞ coframeSpatialFactor := by
  have factorEquality :
      coframeSpatialFactor = fun matrix =>
        spatialMatrixExponential (coframeSpatialBlockCLM matrix) := by
    funext matrix
    rw [coframeSpatialBlockCLM_apply,
      spatialMatrixExponential_eq_rawMatrixExp]
    rfl
  rw [factorEquality]
  exact spatialMatrixExponential_contDiff.comp
    coframeSpatialBlockCLM.contDiff

theorem coframeTimeGaugeFactor_contDiff :
    ContDiff ℝ ∞ coframeTimeGaugeFactor := by
  have lapseSmooth : ContDiff ℝ ∞
      (fun matrix : LorentzianCoframe => Real.exp (matrix 0 0)) :=
    Real.contDiff_exp.comp (coframeEntryCLM 0 0).contDiff
  have parameterSmooth : ContDiff ℝ ∞
      (fun matrix : LorentzianCoframe =>
        (Real.exp (matrix 0 0),
          ((fun (spatial : Fin 3) =>
              matrix spatial.succ 0 - matrix 0 spatial.succ),
            coframeSpatialFactor matrix))) :=
    lapseSmooth.prodMk
      (coframeShiftCLM.contDiff.prodMk coframeSpatialFactor_contDiff)
  have assembled := timeGaugeAssemblyCLM.contDiff.comp parameterSmooth
  change ContDiff ℝ ∞ (fun matrix : LorentzianCoframe =>
    timeGaugeAssemblyCLM
      (Real.exp (matrix 0 0),
        ((fun (spatial : Fin 3) =>
            matrix spatial.succ 0 - matrix 0 spatial.succ),
          coframeSpatialFactor matrix)))
  convert assembled using 1
  funext matrix
  rfl

theorem cauchySafeCoframeChart_contDiff :
    ContDiff ℝ ∞ cauchySafeCoframeChart := by
  have productSmooth :=
    (coframeMatrixRealMulBilinear.toContinuousBilinearMap.contDiff.comp
      coframeBoostFactor_contDiff).clm_apply
        coframeTimeGaugeFactor_contDiff
  change ContDiff ℝ ∞ (fun matrix =>
    coframeMatrixRealMulBilinear.toContinuousBilinearMap
      (coframeBoostFactor matrix) (coframeTimeGaugeFactor matrix))
  exact productSmooth

/-! ## The Cauchy-safe realization of a supplied coframe second jet -/

def coframeHolonomicSecondJetCauchySafeRealization
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    LorentzianCoframe :=
  cauchySafeCoframeChart
    (coframeHolonomicSecondJetQuadraticRealization jet point)

@[simp] theorem coframeHolonomicSecondJetCauchySafeRealization_origin
    (jet : CoframeHolonomicSecondJet) :
    coframeHolonomicSecondJetCauchySafeRealization jet 0 = 1 := by
  simp [coframeHolonomicSecondJetCauchySafeRealization]

theorem coframeHolonomicSecondJetCauchySafeRealization_det_ne_zero
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    Matrix.det
      (coframeHolonomicSecondJetCauchySafeRealization jet point) ≠ 0 :=
  cauchySafeCoframeChart_det_ne_zero _

theorem coframeHolonomicSecondJetCauchySafeRealization_noncharacteristic
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    coframeTemporalPrincipalScalar
      (coframeHolonomicSecondJetCauchySafeRealization jet point) ≠ 0 :=
  cauchySafeCoframeChart_noncharacteristic _

/-- Every source-realized Cauchy-safe second jet carries the strict positive
coordinate-time Dirac coefficient needed by its native evolution law. -/
theorem
    coframeHolonomicSecondJetCauchySafeRealization_coordinateTimeEvolutionPrincipal_posDef
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    (coframeCoordinateDiracEvolutionPrincipal
      (coframeHolonomicSecondJetCauchySafeRealization jet point) 0).PosDef :=
  cauchySafeCoframeChart_coordinateTimeEvolutionPrincipal_posDef _

theorem coframeHolonomicSecondJetCauchySafeRealization_contDiff
    (jet : CoframeHolonomicSecondJet) :
    ContDiff ℝ ∞
      (coframeHolonomicSecondJetCauchySafeRealization jet) := by
  exact cauchySafeCoframeChart_contDiff.comp
    (coframeHolonomicSecondJetQuadraticRealization_contDiff jet)

theorem coframeHolonomicSecondJetCauchySafeRealization_hasFDerivAt_origin
    (jet : CoframeHolonomicSecondJet) :
    HasFDerivAt
      (coframeHolonomicSecondJetCauchySafeRealization jet)
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
  have quadraticDerivative :
      HasFDerivAt
        (coframeHolonomicSecondJetQuadraticRealization jet)
        (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
    simpa using
      (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0)
  have outerDerivative : HasFDerivAt cauchySafeCoframeChart
      (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe)
      (coframeHolonomicSecondJetQuadraticRealization jet 0) := by
    simpa using cauchySafeCoframeChart_hasFDerivAt_zero
  have composed := outerDerivative.comp 0 quadraticDerivative
  convert composed using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · apply TopologicalSpace.ext
    rfl
  · funext point
    rfl
  · apply heq_of_eq
    ext point row column
    change (0 : ℝ) = 0
    rfl

private def cauchySafeRadialLine
    (direction : BasePoint) : ℝ →L[ℝ] BasePoint :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight direction

private theorem cauchySafe_iteratedDeriv_radialLine_two
    (field : BasePoint → LorentzianCoframe)
    (fieldSmooth : ContDiff ℝ 2 field)
    (direction : BasePoint) :
    iteratedDeriv 2 (field ∘ cauchySafeRadialLine direction) 0 =
      fderiv ℝ (fderiv ℝ field) 0 direction direction := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [(cauchySafeRadialLine direction).iteratedFDeriv_comp_right
    fieldSmooth 0 (by simp)]
  simp [iteratedFDeriv_two_apply, cauchySafeRadialLine]
  rfl

private theorem cauchySafeQuadratic_radialLine_deriv_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    deriv
        (coframeHolonomicSecondJetQuadraticRealization jet ∘
          cauchySafeRadialLine direction) 0 = 0 := by
  have derivativeEquality := congrArg
    (fun derivative => derivative (fun _ : Fin 1 => (1 : ℝ)))
    ((cauchySafeRadialLine direction).iteratedFDeriv_comp_right
      (coframeHolonomicSecondJetQuadraticRealization_contDiff jet)
      0 (i := 1) (by exact WithTop.coe_le_coe.mpr le_top))
  simp only [iteratedFDeriv_one_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    at derivativeEquality
  unfold deriv
  calc
    (fderiv ℝ
        (coframeHolonomicSecondJetQuadraticRealization jet ∘
          cauchySafeRadialLine direction) 0) 1 =
        (fderiv ℝ (coframeHolonomicSecondJetQuadraticRealization jet) 0)
          (cauchySafeRadialLine direction 1) := derivativeEquality
    _ = 0 := by
      rw [(coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt
        jet 0).fderiv]
      simp

private theorem cauchySafeQuadratic_radialLine_iteratedDeriv_two_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    iteratedDeriv 2
        (coframeHolonomicSecondJetQuadraticRealization jet ∘
          cauchySafeRadialLine direction) 0 =
      jet.1 direction direction := by
  rw [cauchySafe_iteratedDeriv_radialLine_two
    (coframeHolonomicSecondJetQuadraticRealization jet)
    ((coframeHolonomicSecondJetQuadraticRealization_contDiff jet).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)) direction]
  change
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetQuadraticRealization jet)
        direction direction = _
  rw [coframeHolonomicSecondJetQuadraticRealization_secondJet]

private theorem cauchySafeChartQuadratic_radialLine_iteratedDeriv_two_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    iteratedDeriv 2
        (cauchySafeCoframeChart ∘
          (coframeHolonomicSecondJetQuadraticRealization jet ∘
            cauchySafeRadialLine direction)) 0 =
      jet.1 direction direction := by
  have chainRule := iteratedDeriv_vcomp_two
    (g := cauchySafeCoframeChart)
    (f := coframeHolonomicSecondJetQuadraticRealization jet ∘
      cauchySafeRadialLine direction)
    (x := 0)
    ((cauchySafeCoframeChart_contDiff.of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    (((coframeHolonomicSecondJetQuadraticRealization_contDiff jet).comp
      (cauchySafeRadialLine direction).contDiff).of_le
        (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
  rw [show
      (coframeHolonomicSecondJetQuadraticRealization jet ∘
        cauchySafeRadialLine direction) 0 = 0 by simp]
    at chainRule
  have innerFirstDerivativeZero :
      (fun _ : Fin 2 =>
        deriv (coframeHolonomicSecondJetQuadraticRealization jet ∘
          cauchySafeRadialLine direction) 0) =
        (fun _ : Fin 2 => (0 : LorentzianCoframe)) := by
    funext index
    exact cauchySafeQuadratic_radialLine_deriv_origin jet direction
  have innerSecondDerivative :
      iteratedDeriv 2
          (coframeHolonomicSecondJetQuadraticRealization jet ∘
            cauchySafeRadialLine direction) 0 =
        jet.1 direction direction :=
    cauchySafeQuadratic_radialLine_iteratedDeriv_two_origin jet direction
  have quadraticOuterTermVanishes :
      iteratedFDeriv ℝ 2 cauchySafeCoframeChart 0
          (fun _ : Fin 2 => (0 : LorentzianCoframe)) = 0 := by
    exact ContinuousMultilinearMap.map_zero _
  calc
    iteratedDeriv 2
        (cauchySafeCoframeChart ∘
          (coframeHolonomicSecondJetQuadraticRealization jet ∘
            cauchySafeRadialLine direction)) 0 =
        (iteratedFDeriv ℝ 2 cauchySafeCoframeChart 0)
            (fun _ : Fin 2 =>
              deriv
                (coframeHolonomicSecondJetQuadraticRealization jet ∘
                  cauchySafeRadialLine direction) 0) +
          (fderiv ℝ cauchySafeCoframeChart 0)
            (iteratedDeriv 2
              (coframeHolonomicSecondJetQuadraticRealization jet ∘
                cauchySafeRadialLine direction) 0) := chainRule
    _ = (iteratedFDeriv ℝ 2 cauchySafeCoframeChart 0)
            (fun _ : Fin 2 => (0 : LorentzianCoframe)) +
          (fderiv ℝ cauchySafeCoframeChart 0)
            (jet.1 direction direction) := by
      congr 1
      · exact congrArg (iteratedFDeriv ℝ 2 cauchySafeCoframeChart 0)
          innerFirstDerivativeZero
      · exact congrArg (fderiv ℝ cauchySafeCoframeChart 0)
          innerSecondDerivative
    _ = 0 + jet.1 direction direction := by
      rw [quadraticOuterTermVanishes,
        cauchySafeCoframeChart_hasFDerivAt_zero.fderiv]
      rfl
    _ = jet.1 direction direction := zero_add _

private theorem
    coframeHolonomicSecondJetCauchySafeRealization_secondJet_diagonal
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetCauchySafeRealization jet)
        direction direction =
      jet.1 direction direction := by
  unfold coframeOriginSecondFrechetJet
  rw [← cauchySafe_iteratedDeriv_radialLine_two
    (coframeHolonomicSecondJetCauchySafeRealization jet)
    ((coframeHolonomicSecondJetCauchySafeRealization_contDiff jet).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)) direction]
  simpa [coframeHolonomicSecondJetCauchySafeRealization,
    Function.comp_def] using
    (cauchySafeChartQuadratic_radialLine_iteratedDeriv_two_origin
      jet direction)

theorem coframeHolonomicSecondJetCauchySafeRealization_secondJet
    (jet : CoframeHolonomicSecondJet) :
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetCauchySafeRealization jet) =
      jet.1 := by
  let actualJet := coframeOriginSecondFrechetJet
    (coframeHolonomicSecondJetCauchySafeRealization jet)
  have actualSymmetry : ∀ first second : BasePoint,
      actualJet first second = actualJet second first := by
    intro first second
    exact
      ((coframeHolonomicSecondJetCauchySafeRealization_contDiff jet).contDiffAt
          |>.isSymmSndFDerivAt (n := ∞) (by
            simpa only [minSmoothness_of_isRCLikeNormedField] using
              (show (2 : ℕ∞ω) ≤ ∞ from
                WithTop.coe_le_coe.mpr le_top))) first second
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change actualJet first second = jet.1 first second
  calc
    actualJet first second =
        (1 / 2 : ℝ) •
          (actualJet (first + second) (first + second) -
            actualJet first first - actualJet second second) := by
      simp only [map_add, add_apply]
      rw [← actualSymmetry first second]
      module
    _ = (1 / 2 : ℝ) •
          (jet.1 (first + second) (first + second) -
            jet.1 first first - jet.1 second second) := by
      rw [
        coframeHolonomicSecondJetCauchySafeRealization_secondJet_diagonal,
        coframeHolonomicSecondJetCauchySafeRealization_secondJet_diagonal,
        coframeHolonomicSecondJetCauchySafeRealization_secondJet_diagonal]
    _ = jet.1 first second := by
      simp only [map_add, add_apply]
      rw [← coframeHolonomicSecondJet_symmetric jet first second]
      module

end

end SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicCauchySafeRealization
