import H0mework.Physics.DiracCovariance.CurvatureCovariance
import H0mework.Physics.Dirac.GravitySpinCovariance

/-!
# Lorentz-admissible six-coordinate curvature covariance

Raw `gl(4)` curvature conjugation does not by itself descend to the current
six-coordinate bivector readout: diagonal and symmetric raw components are
discarded by that readout but can mix into off-diagonal components under
conjugation.  This module therefore performs the descent only on the existing
whole-field `GravityConnectionLorentzAdmissible` domain.

The final lowered-curvature law is generated from the primitive connection
action and the faithful raw theorem.  It does not accept a transformed
curvature field or point-field covariance receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinCurvatureReadoutCovariance

open PointwiseDiracSpinConnectionLift
open PointwiseLorentzianCoframeJet
open ProofFreeRicherAnholonomicSource
open StageNineBlockwiseConstitutive
open StageNineCoframeTwoFormPairing
open StageNineDiracKineticLocalSpinConnection
open StageNineDiracKineticLocalSpinCurvatureCovariance
open StageNineDiracKineticLocalSpinDifferential
open StageNineDiracKineticLocalSpinLiftCovariance
open StageNineDiracKineticLocalSpinMaurerCalculus
open StageNineDiracKineticLocalSpinMaurerLift
open StageNineDiracKineticSpinJurisdiction
open StageNineFormNativeGravitySpinCovariance
open StageNineGlobalBundle
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNinePhysicalBivectorSpinRepresentation
open StageNineSpinMatterBundle

open scoped ContDiff MatrixGroups Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! ## Lorentz-skew raw matrices -/

/-- Matrix-level Lorentz-skew predicate used only for faithful raw curvature
transport. -/
def LorentzMatrixSkew (matrix : LorentzianCoframe) : Prop :=
  matrix.transpose * minkowskiInternalMetric +
    minkowskiInternalMetric * matrix = 0

theorem rawGravityConnectionMatrix_lorentzSkew
    (configuration : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) (direction : LorentzianIndex) :
    LorentzMatrixSkew
      (rawGravityConnectionMatrix configuration point direction) :=
  admissible point direction

theorem fieldDirectionalDerivative_lorentzMatrix_add
    (first second : BasePoint → LorentzianCoframe)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => first candidate + second candidate)
        point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

theorem fieldDirectionalDerivative_lorentzMatrix_transpose
    (field : BasePoint → LorentzianCoframe)
    (smooth : ContDiff ℝ ∞ field)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => (field candidate).transpose) point direction =
      (fieldDirectionalDerivative field point direction).transpose := by
  have actual := fieldDirectionalDerivative_continuousLinear
    lorentzMatrixTransposeCLM field smooth point direction
  change
    fieldDirectionalDerivative
        (fun candidate => (field candidate).transpose) point direction =
      (fieldDirectionalDerivative field point direction).transpose
    at actual
  exact actual

theorem lorentzMatrixSkew_add
    (first second : LorentzianCoframe)
    (firstSkew : LorentzMatrixSkew first)
    (secondSkew : LorentzMatrixSkew second) :
    LorentzMatrixSkew (first + second) := by
  unfold LorentzMatrixSkew at firstSkew secondSkew ⊢
  rw [Matrix.transpose_add]
  calc
    (first.transpose + second.transpose) * minkowskiInternalMetric +
        minkowskiInternalMetric * (first + second) =
      (first.transpose * minkowskiInternalMetric +
          minkowskiInternalMetric * first) +
        (second.transpose * minkowskiInternalMetric +
          minkowskiInternalMetric * second) := by noncomm_ring
    _ = 0 := by rw [firstSkew, secondSkew]; simp

theorem lorentzMatrixSkew_neg
    (matrix : LorentzianCoframe)
    (skew : LorentzMatrixSkew matrix) :
    LorentzMatrixSkew (-matrix) := by
  unfold LorentzMatrixSkew at skew ⊢
  rw [Matrix.transpose_neg]
  calc
    (-matrix.transpose) * minkowskiInternalMetric +
        minkowskiInternalMetric * (-matrix) =
      -(matrix.transpose * minkowskiInternalMetric +
        minkowskiInternalMetric * matrix) := by noncomm_ring
    _ = 0 := by rw [skew]; simp

theorem lorentzMatrixSkew_sub
    (first second : LorentzianCoframe)
    (firstSkew : LorentzMatrixSkew first)
    (secondSkew : LorentzMatrixSkew second) :
    LorentzMatrixSkew (first - second) := by
  rw [sub_eq_add_neg]
  exact lorentzMatrixSkew_add first (-second) firstSkew
    (lorentzMatrixSkew_neg second secondSkew)

theorem lorentzMatrixSkew_commutator
    (first second : LorentzianCoframe)
    (firstSkew : LorentzMatrixSkew first)
    (secondSkew : LorentzMatrixSkew second) :
    LorentzMatrixSkew (first * second - second * first) := by
  have firstAdjoint :
      first.transpose * minkowskiInternalMetric =
        -(minkowskiInternalMetric * first) := by
    rw [eq_neg_iff_add_eq_zero]
    exact firstSkew
  have secondAdjoint :
      second.transpose * minkowskiInternalMetric =
        -(minkowskiInternalMetric * second) := by
    rw [eq_neg_iff_add_eq_zero]
    exact secondSkew
  unfold LorentzMatrixSkew
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    (second.transpose * first.transpose - first.transpose * second.transpose) *
          minkowskiInternalMetric +
        minkowskiInternalMetric * (first * second - second * first) =
      second.transpose *
            (first.transpose * minkowskiInternalMetric) -
          first.transpose *
            (second.transpose * minkowskiInternalMetric) +
        minkowskiInternalMetric * (first * second - second * first) := by
          noncomm_ring
    _ =
      second.transpose * (-(minkowskiInternalMetric * first)) -
          first.transpose * (-(minkowskiInternalMetric * second)) +
        minkowskiInternalMetric * (first * second - second * first) := by
          rw [firstAdjoint, secondAdjoint]
    _ =
      -(second.transpose * minkowskiInternalMetric) * first +
          (first.transpose * minkowskiInternalMetric) * second +
        minkowskiInternalMetric * (first * second - second * first) := by
          noncomm_ring
    _ = 0 := by rw [firstAdjoint, secondAdjoint]; noncomm_ring

/-! ## Derivatives and curvature remain in the Lorentz algebra -/

theorem rawGravityConnectionMatrixDerivative_lorentzSkew
    (configuration : StageNineHolonomicConfiguration)
    (smooth : GravityConnectionSmooth configuration)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    LorentzMatrixSkew
      (fieldDirectionalDerivative
        (fun candidate =>
          rawGravityConnectionMatrix configuration candidate formDirection)
        point derivativeDirection) := by
  let connectionField : BasePoint → LorentzianCoframe := fun candidate =>
    rawGravityConnectionMatrix configuration candidate formDirection
  have connectionSmooth : ContDiff ℝ ∞ connectionField :=
    rawGravityConnectionMatrix_contDiff configuration smooth formDirection
  let leftField : BasePoint → LorentzianCoframe := fun candidate =>
    (connectionField candidate).transpose * minkowskiInternalMetric
  let rightField : BasePoint → LorentzianCoframe := fun candidate =>
    minkowskiInternalMetric * connectionField candidate
  have transposeSmooth : ContDiff ℝ ∞ fun candidate =>
      (connectionField candidate).transpose :=
    lorentzMatrixTransposeCLM.contDiff.comp connectionSmooth
  have leftSmooth : ContDiff ℝ ∞ leftField :=
    lorentzMatrixField_mul_contDiff _ _ transposeSmooth contDiff_const
  have rightSmooth : ContDiff ℝ ∞ rightField :=
    lorentzMatrixField_mul_contDiff _ _ contDiff_const connectionSmooth
  have sumDerivative := fieldDirectionalDerivative_lorentzMatrix_add
    leftField rightField leftSmooth rightSmooth point derivativeDirection
  have leftDerivative := fieldDirectionalDerivative_lorentzMatrix_mul
    (fun candidate => (connectionField candidate).transpose)
    (fun _ : BasePoint => minkowskiInternalMetric)
    transposeSmooth contDiff_const point derivativeDirection
  have rightDerivative := fieldDirectionalDerivative_lorentzMatrix_mul
    (fun _ : BasePoint => minkowskiInternalMetric) connectionField
    contDiff_const connectionSmooth point derivativeDirection
  have transposeDerivative := fieldDirectionalDerivative_lorentzMatrix_transpose
    connectionField connectionSmooth point derivativeDirection
  have skewFieldEquality :
      (fun candidate => leftField candidate + rightField candidate) =
        fun _ : BasePoint => (0 : LorentzianCoframe) := by
    funext candidate
    exact rawGravityConnectionMatrix_lorentzSkew configuration admissible
      candidate formDirection
  rw [skewFieldEquality] at sumDerivative
  have zeroDerivative :
      fieldDirectionalDerivative
        (fun _ : BasePoint => (0 : LorentzianCoframe)) point
          derivativeDirection = 0 := by
    simp [fieldDirectionalDerivative]
  rw [zeroDerivative] at sumDerivative
  unfold LorentzMatrixSkew
  rw [← transposeDerivative]
  rw [← show
      fieldDirectionalDerivative leftField point derivativeDirection =
        fieldDirectionalDerivative
            (fun candidate => (connectionField candidate).transpose)
              point derivativeDirection * minkowskiInternalMetric by
        rw [leftDerivative]
        simp [fieldDirectionalDerivative],
    ← show
      fieldDirectionalDerivative rightField point derivativeDirection =
        minkowskiInternalMetric *
          fieldDirectionalDerivative connectionField point
            derivativeDirection by
        rw [rightDerivative]
        simp [fieldDirectionalDerivative]]
  exact sumDerivative.symm

theorem orderedMixedCurvature_lorentzSkew
    (configuration : StageNineHolonomicConfiguration)
    (smooth : GravityConnectionSmooth configuration)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) (first second : LorentzianIndex) :
    LorentzMatrixSkew
      (coordinateToRawMatrix
        (orderedMixedCurvature configuration point first second)) := by
  rw [coordinateToRawMatrix_orderedMixedCurvature configuration smooth]
  apply lorentzMatrixSkew_add
  · exact lorentzMatrixSkew_sub _ _
      (rawGravityConnectionMatrixDerivative_lorentzSkew configuration smooth
        admissible point first second)
      (rawGravityConnectionMatrixDerivative_lorentzSkew configuration smooth
        admissible point second first)
  · exact lorentzMatrixSkew_commutator _ _
      (rawGravityConnectionMatrix_lorentzSkew configuration admissible point
        first)
      (rawGravityConnectionMatrix_lorentzSkew configuration admissible point
        second)

/-! ## Faithful six-coordinate readout of a Lorentz-skew raw matrix -/

/-- Raise the second index of a mixed raw matrix and retain the canonical six
ordered antisymmetric coordinates. -/
def contravariantLorentzPairReadout
    (matrix : LorentzianCoframe) : GaugeTwoForm :=
  fun pair =>
    minkowskiInternalSign (pairSecond pair) *
      matrix (pairFirst pair) (pairSecond pair)

theorem lorentzMatrixSkew_entry
    (matrix : LorentzianCoframe)
    (skew : LorentzMatrixSkew matrix)
    (first second : LorentzianIndex) :
    minkowskiInternalSign second * matrix second first +
        minkowskiInternalSign first * matrix first second = 0 := by
  have entry := congrFun (congrFun skew first) second
  rw [minkowskiInternalMetric_eq_diagonal_sign] at entry
  simpa [Matrix.transpose_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, mul_comm] using entry

theorem lorentzMatrixSkew_diagonal_zero
    (matrix : LorentzianCoframe)
    (skew : LorentzMatrixSkew matrix)
    (internal : LorentzianIndex) :
    matrix internal internal = 0 := by
  have entry := lorentzMatrixSkew_entry matrix skew internal internal
  fin_cases internal <;>
    norm_num [minkowskiInternalSign] at entry ⊢ <;> linarith

/-- Conjugation of a Lorentz-skew mixed matrix becomes the exterior-square
action on its raised canonical pair coordinates. -/
theorem contravariantLorentzPairReadout_conjugate
    (groupElement : SpinPlus13)
    (matrix : LorentzianCoframe)
    (skew : LorentzMatrixSkew matrix) :
    contravariantLorentzPairReadout
        (spinLorentzMatrix groupElement * matrix *
          (spinLorentzMatrix groupElement)⁻¹) =
      spinLorentzTwoFormRepresentation groupElement
        (contravariantLorentzPairReadout matrix) := by
  have diagonalZero (internal : LorentzianIndex) :
      matrix internal internal = 0 :=
    lorentzMatrixSkew_diagonal_zero matrix skew internal
  have h01 := lorentzMatrixSkew_entry matrix skew 0 1
  have h02 := lorentzMatrixSkew_entry matrix skew 0 2
  have h03 := lorentzMatrixSkew_entry matrix skew 0 3
  have h12 := lorentzMatrixSkew_entry matrix skew 1 2
  have h13 := lorentzMatrixSkew_entry matrix skew 1 3
  have h23 := lorentzMatrixSkew_entry matrix skew 2 3
  have one_ne_zero : (1 : LorentzianIndex) ≠ 0 := by decide
  have two_ne_zero : (2 : LorentzianIndex) ≠ 0 := by decide
  have three_ne_zero : (3 : LorentzianIndex) ≠ 0 := by decide
  simp [minkowskiInternalSign, one_ne_zero, two_ne_zero, three_ne_zero]
    at h01 h02 h03 h12 h13 h23
  have h10 : matrix 1 0 = matrix 0 1 := by linarith only [h01]
  have h20 : matrix 2 0 = matrix 0 2 := by linarith only [h02]
  have h30 : matrix 3 0 = matrix 0 3 := by linarith only [h03]
  have h21 : matrix 2 1 = -matrix 1 2 := by linarith only [h12]
  have h31 : matrix 3 1 = -matrix 1 3 := by linarith only [h13]
  have h32 : matrix 3 2 = -matrix 2 3 := by linarith only [h23]
  funext pair
  change
    contravariantLorentzPairReadout
        (spinLorentzMatrix groupElement * matrix *
          (spinLorentzMatrix groupElement)⁻¹) pair =
      coframeTwoFormLinear (spinLorentzMatrix groupElement)
        (contravariantLorentzPairReadout matrix) pair
  rw [spinLorentzMatrix_nonsingInv_minkowski]
  fin_cases pair <;>
    simp [contravariantLorentzPairReadout, coframeTwoFormLinear,
      coframeWedge, Matrix.mul_apply, Matrix.transpose_apply,
      minkowskiInternalMetric, pairFirst, pairSecond,
      Fin.sum_univ_four, Fin.sum_univ_six, diagonalZero] <;>
    rw [h10, h20, h30, h21, h31, h32] <;>
    ring

/-! ## Descent of the primitive curvature producer -/

/-- Dependency-light form of the canonical lowered-curvature component
bridge. -/
theorem orderedMixedCurvature_canonicalPair_eq_holonomic_of_connectionSmooth
    (configuration : StageNineHolonomicConfiguration)
    (smooth : GravityConnectionSmooth configuration)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    holonomicGravityCurvature configuration point internalPair spacetimePair =
      minkowskiInternalSign (pairFirst internalPair) *
        orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair, pairSecond internalPair) := by
  unfold holonomicGravityCurvature orderedMixedCurvature matrixBracket
  dsimp only
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply]
  rw [connectionMatrixDerivative_apply_of_connectionSmooth configuration smooth,
    connectionMatrixDerivative_apply_of_connectionSmooth configuration smooth]
  simp [connectionMatrix]

/-- The raised canonical pair readout is exactly the faithful raw pair
readout, with no whole-configuration smoothness premise. -/
theorem holonomicContravariantGravityCurvature_eq_pairReadout
    (configuration : StageNineHolonomicConfiguration)
    (smooth : GravityConnectionSmooth configuration)
    (point : BasePoint)
    (internalPair spacetimePair : Fin 6) :
    holonomicContravariantGravityCurvature configuration point
        internalPair spacetimePair =
      contravariantLorentzPairReadout
        (coordinateToRawMatrix
          (orderedMixedCurvature configuration point
            (pairFirst spacetimePair) (pairSecond spacetimePair)))
        internalPair := by
  rw [holonomicContravariantGravityCurvature_apply,
    orderedMixedCurvature_canonicalPair_eq_holonomic_of_connectionSmooth
      configuration smooth]
  unfold lorentzianTwoFormSign contravariantLorentzPairReadout
  have signSquare :
      minkowskiInternalSign (pairFirst internalPair) ^ 2 = 1 := by
    fin_cases internalPair <;>
      norm_num [minkowskiInternalSign, pairFirst]
  change
    (minkowskiInternalSign (pairFirst internalPair) *
        minkowskiInternalSign (pairSecond internalPair)) *
      (minkowskiInternalSign (pairFirst internalPair) *
        orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair, pairSecond internalPair)) =
    minkowskiInternalSign (pairSecond internalPair) *
      coordinateToRawMatrix
        (orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair))
        (pairFirst internalPair) (pairSecond internalPair)
  change
    (minkowskiInternalSign (pairFirst internalPair) *
        minkowskiInternalSign (pairSecond internalPair)) *
      (minkowskiInternalSign (pairFirst internalPair) *
        orderedMixedCurvature configuration point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
          (pairFirst internalPair, pairSecond internalPair)) =
    minkowskiInternalSign (pairSecond internalPair) *
      orderedMixedCurvature configuration point
        (pairFirst spacetimePair) (pairSecond spacetimePair)
        (pairFirst internalPair, pairSecond internalPair)
  calc
    _ = minkowskiInternalSign (pairFirst internalPair) ^ 2 *
        minkowskiInternalSign (pairSecond internalPair) *
          orderedMixedCurvature configuration point
            (pairFirst spacetimePair) (pairSecond spacetimePair)
            (pairFirst internalPair, pairSecond internalPair) := by ring
    _ = _ := by rw [signSquare]; ring

/-- The primitive local Spin action preserves the whole-field Lorentz
admissibility domain. -/
theorem localSpinDiracKineticAction_gravityConnection_admissible
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (admissible : GravityConnectionLorentzAdmissible configuration) :
    GravityConnectionLorentzAdmissible
      (localSpinDiracKineticAction spinField configuration) := by
  intro point direction
  change LorentzMatrixSkew
    (rawGravityConnectionMatrix
      (localSpinDiracKineticAction spinField configuration) point direction)
  rw [rawGravityConnectionMatrix_localSpinAction]
  apply lorentzMatrixSkew_sub
  · exact spinWeylDualHomogeneousLorentzConnection_lorentzSkew
      (spinField point) (configuration.gravityConnection point)
      (admissible point) direction
  · exact localSpinWeylDualMaurerConnection_lorentzSkew
      spinField spinSmooth point direction

/-- Raised six-coordinate curvature covariance generated from the primitive
connection action on the Lorentz-admissible domain. -/
theorem holonomicContravariantGravityCurvature_localSpin_covariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    holonomicContravariantGravityCurvature
        (localSpinDiracKineticAction spinField configuration) point =
      spinLorentzPhysicalBivectorRepresentation
        (spinWeylDual (spinField point))
        (holonomicContravariantGravityCurvature configuration point) := by
  let transformed := localSpinDiracKineticAction spinField configuration
  let connectionSmooth :=
    gravityConnectionSmooth_of_smooth configuration smooth
  let transformedSmooth : GravityConnectionSmooth transformed :=
    localSpinDiracKineticAction_gravityConnectionSmooth spinField
      configuration spinSmooth connectionSmooth
  funext internalPair spacetimePair
  change
    holonomicContravariantGravityCurvature transformed point internalPair
        spacetimePair =
      spinLorentzTwoFormLinearEquiv (spinWeylDual (spinField point))
        (fun sourceInternalPair =>
          holonomicContravariantGravityCurvature configuration point
            sourceInternalPair spacetimePair) internalPair
  let originalRaw := coordinateToRawMatrix
    (orderedMixedCurvature configuration point
      (pairFirst spacetimePair) (pairSecond spacetimePair))
  let transformedRaw := coordinateToRawMatrix
    (orderedMixedCurvature transformed point
      (pairFirst spacetimePair) (pairSecond spacetimePair))
  have originalReadout :
      (fun sourceInternalPair =>
        holonomicContravariantGravityCurvature configuration point
          sourceInternalPair spacetimePair) =
        contravariantLorentzPairReadout originalRaw := by
    funext sourceInternalPair
    exact holonomicContravariantGravityCurvature_eq_pairReadout
      configuration connectionSmooth point sourceInternalPair spacetimePair
  have transformedReadout :
      (fun sourceInternalPair =>
        holonomicContravariantGravityCurvature transformed point
          sourceInternalPair spacetimePair) =
        contravariantLorentzPairReadout transformedRaw := by
    funext sourceInternalPair
    exact holonomicContravariantGravityCurvature_eq_pairReadout
      transformed transformedSmooth point sourceInternalPair spacetimePair
  have rawCovariance :
      transformedRaw =
        spinLorentzMatrix (spinWeylDual (spinField point)) * originalRaw *
          (spinLorentzMatrix (spinWeylDual (spinField point)))⁻¹ := by
    simpa [transformed, originalRaw, transformedRaw,
      localSpinWeylDualLorentzMatrix,
      localSpinWeylDualLorentzInverseMatrix] using
      orderedMixedCurvature_localSpin_raw_covariant_of_smooth spinField
        configuration spinSmooth smooth point
          (pairFirst spacetimePair) (pairSecond spacetimePair)
  have rawSkew : LorentzMatrixSkew originalRaw :=
    orderedMixedCurvature_lorentzSkew configuration connectionSmooth
      admissible point (pairFirst spacetimePair) (pairSecond spacetimePair)
  have pairCovariance := contravariantLorentzPairReadout_conjugate
    (spinWeylDual (spinField point)) originalRaw rawSkew
  change
    (fun sourceInternalPair =>
      holonomicContravariantGravityCurvature transformed point
        sourceInternalPair spacetimePair) internalPair = _
  rw [transformedReadout, originalReadout, rawCovariance]
  exact congrFun pairCovariance internalPair

/-- Lowered six-coordinate curvature covariance in the exact `N ρ N`
representation consumed by the form-native BF action. -/
theorem holonomicGravityCurvature_localSpin_covariant
    (spinField : BasePoint → SpinPlus13)
    (configuration : StageNineHolonomicConfiguration)
    (spinSmooth : LocalSpinFieldSmooth spinField)
    (smooth : configuration.Smooth)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    holonomicGravityCurvature
        (localSpinDiracKineticAction spinField configuration) point =
      spinLorentzLoweredPhysicalBivector
        (spinWeylDual (spinField point))
        (holonomicGravityCurvature configuration point) := by
  apply gravityInternalPairVarianceNormalization_injective
  rw [gravityInternalPairVarianceNormalization_spinLowered]
  exact holonomicContravariantGravityCurvature_localSpin_covariant
    spinField configuration spinSmooth smooth admissible point

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracKineticLocalSpinCurvatureReadoutCovariance
