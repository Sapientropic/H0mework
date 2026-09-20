import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# S9-C3f2: actual mixed-index gravity Bianchi identity

The full ordered curvature below is generated from the same primitive smooth
gravity connection stored by `StageNineHolonomicConfiguration`.  Its
differential Bianchi identity is proved in faithful finite Euclidean matrix
coordinates, using mixed-second Fréchet derivative symmetry, the directional
Leibniz rule for the actual matrix commutator, and the matrix Jacobi identity.
An injective raw-matrix readout keeps the coordinate proof tied to `gl(4)`.

The existing physical `Fin 6 x Fin 6` curvature is not replaced or hand
filled: a separate theorem identifies every canonical oriented pair with the
Minkowski-lowered component of this full curvature.  Smoothness alone does
not make the primitive connection Lorentz skew, so `so(1,3)` interpretation
remains behind the explicit `GravityConnectionLorentzAdmissible` domain gate.

This is an off-shell kinematic theorem.  It consumes no curvature, Bianchi,
stationarity, field-equation, stress, spin, Noether, or conservation receipt.
-/

namespace SaturationMonoid.PhysicsCore.StageNineGravityBianchi

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open scoped ContDiff

noncomputable section

abbrev GravityMatrix :=
  EuclideanSpace ℝ (LorentzianIndex × LorentzianIndex)

abbrev GravityRawMatrix := Matrix LorentzianIndex LorentzianIndex ℝ

/-- Faithful readout from the finite Euclidean derivative carrier to the raw
mixed-index matrix used by the gravity connection. -/
def coordinateToRawMatrix : GravityMatrix →ₗ[ℝ] GravityRawMatrix where
  toFun coordinate internalOut internalIn := coordinate (internalOut, internalIn)
  map_add' := by
    intro first second
    rfl
  map_smul' := by
    intro parameter coordinate
    rfl

theorem coordinateToRawMatrix_injective :
    Function.Injective coordinateToRawMatrix := by
  intro first second equality
  ext index
  rcases index with ⟨internalOut, internalIn⟩
  exact congrFun (congrFun equality internalOut) internalIn

/-- Actual matrix commutator transported to the faithful finite Euclidean
coordinate carrier. -/
def matrixBracket (first second : GravityMatrix) : GravityMatrix :=
  WithLp.toLp 2 fun index : LorentzianIndex × LorentzianIndex =>
    ∑ middle : LorentzianIndex,
      (first (index.1, middle) * second (middle, index.2) -
        second (index.1, middle) * first (middle, index.2))

theorem coordinateToRawMatrix_matrixBracket
    (first second : GravityMatrix) :
    coordinateToRawMatrix (matrixBracket first second) =
      coordinateToRawMatrix first * coordinateToRawMatrix second -
        coordinateToRawMatrix second * coordinateToRawMatrix first := by
  ext internalOut internalIn
  change
    (∑ middle : LorentzianIndex,
        (first (internalOut, middle) * second (middle, internalIn) -
          second (internalOut, middle) * first (middle, internalIn))) =
      (∑ middle : LorentzianIndex,
          first (internalOut, middle) * second (middle, internalIn)) -
        ∑ middle : LorentzianIndex,
          second (internalOut, middle) * first (middle, internalIn)
  rw [Finset.sum_sub_distrib]

theorem matrixBracket_add_left (first second residual : GravityMatrix) :
    matrixBracket (first + second) residual =
      matrixBracket first residual + matrixBracket second residual := by
  apply coordinateToRawMatrix_injective
  simp only [map_add, coordinateToRawMatrix_matrixBracket]
  noncomm_ring

theorem matrixBracket_add_right (first second residual : GravityMatrix) :
    matrixBracket residual (first + second) =
      matrixBracket residual first + matrixBracket residual second := by
  apply coordinateToRawMatrix_injective
  simp only [map_add, coordinateToRawMatrix_matrixBracket]
  noncomm_ring

theorem matrixBracket_smul_left
    (parameter : ℝ) (first residual : GravityMatrix) :
    matrixBracket (parameter • first) residual =
      parameter • matrixBracket first residual := by
  ext index
  simp only [matrixBracket, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro middle _
  ring

theorem matrixBracket_smul_right
    (parameter : ℝ) (first residual : GravityMatrix) :
    matrixBracket residual (parameter • first) =
      parameter • matrixBracket residual first := by
  ext index
  simp only [matrixBracket, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro middle _
  ring

theorem matrixBracket_neg_left (first residual : GravityMatrix) :
    matrixBracket (-first) residual = -matrixBracket first residual := by
  simpa only [neg_one_smul] using
    matrixBracket_smul_left (-1) first residual

theorem matrixBracket_neg_right (first residual : GravityMatrix) :
    matrixBracket residual (-first) = -matrixBracket residual first := by
  simpa only [neg_one_smul] using
    matrixBracket_smul_right (-1) first residual

theorem matrixBracket_sub_left
    (first second residual : GravityMatrix) :
    matrixBracket (first - second) residual =
      matrixBracket first residual - matrixBracket second residual := by
  rw [sub_eq_add_neg, matrixBracket_add_left,
    matrixBracket_neg_left, sub_eq_add_neg]

theorem matrixBracket_sub_right
    (first second residual : GravityMatrix) :
    matrixBracket residual (first - second) =
      matrixBracket residual first - matrixBracket residual second := by
  rw [sub_eq_add_neg, matrixBracket_add_right,
    matrixBracket_neg_right, sub_eq_add_neg]

def matrixBracketBilinear :
    GravityMatrix →ₗ[ℝ] GravityMatrix →ₗ[ℝ] GravityMatrix where
  toFun first :=
    { toFun := fun second => matrixBracket first second
      map_add' := by
        intro second third
        exact matrixBracket_add_right second third first
      map_smul' := by
        intro parameter second
        exact matrixBracket_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact matrixBracket_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    exact matrixBracket_smul_left parameter first residual

theorem matrixBracket_skew (first second : GravityMatrix) :
    matrixBracket first second = -matrixBracket second first := by
  apply coordinateToRawMatrix_injective
  simp only [map_neg, coordinateToRawMatrix_matrixBracket]
  noncomm_ring

theorem matrixBracket_jacobi (first second third : GravityMatrix) :
    matrixBracket first (matrixBracket second third) +
        matrixBracket second (matrixBracket third first) +
        matrixBracket third (matrixBracket first second) = 0 := by
  apply coordinateToRawMatrix_injective
  simp only [map_add, map_zero, coordinateToRawMatrix_matrixBracket]
  noncomm_ring

theorem matrixBracket_contDiff
    (first second : BasePoint → GravityMatrix)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      matrixBracket (first point) (second point) := by
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      matrixBracketBilinear.toContinuousBilinearMap (first point) :=
    matrixBracketBilinear.toContinuousBilinearMap.contDiff.comp firstSmooth
  simpa [matrixBracketBilinear] using outerSmooth.clm_apply secondSmooth

theorem fieldDirectionalDerivative_matrixBracket
    (first second : BasePoint → GravityMatrix)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => matrixBracket (first candidate) (second candidate))
        point direction =
      matrixBracket
          (fieldDirectionalDerivative first point direction) (second point) +
        matrixBracket (first point)
          (fieldDirectionalDerivative second point direction) := by
  let bracket := matrixBracketBilinear.toContinuousBilinearMap
  have firstDifferentiable : DifferentiableAt ℝ first point :=
    (firstSmooth.differentiable (by simp)).differentiableAt
  have secondDifferentiable : DifferentiableAt ℝ second point :=
    (secondSmooth.differentiable (by simp)).differentiableAt
  have outerDerivative : HasFDerivAt
      (fun candidate => bracket (first candidate))
      (bracket.comp (fderiv ℝ first point)) point :=
    bracket.hasFDerivAt.comp point firstDifferentiable.hasFDerivAt
  have totalDerivative :
      fderiv ℝ (fun candidate =>
          bracket (first candidate) (second candidate)) point =
        (bracket (first point)).comp (fderiv ℝ second point) +
          (bracket.comp (fderiv ℝ first point)).flip (second point) :=
    (outerDerivative.clm_apply secondDifferentiable.hasFDerivAt).fderiv
  change
    fderiv ℝ (fun candidate =>
        bracket (first candidate) (second candidate)) point
          (coordinateDirection direction) = _
  rw [totalDerivative]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  change
    matrixBracket (first point)
          (fieldDirectionalDerivative second point direction) +
        matrixBracket
          (fieldDirectionalDerivative first point direction) (second point) = _
  abel

theorem mixedMatrixFieldDirectionalDerivative_comm
    (field : BasePoint → GravityMatrix)
    (smooth : ContDiff ℝ ∞ field)
    (point : BasePoint)
    (first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate first)
        point second =
      fieldDirectionalDerivative
        (fun candidate => fieldDirectionalDerivative field candidate second)
        point first := by
  have derivativeSmooth : ContDiff ℝ ∞ (fderiv ℝ field) :=
    smooth.fderiv_right (m := ∞) (by simp)
  have derivativeDifferentiable :
      DifferentiableAt ℝ (fderiv ℝ field) point :=
    (derivativeSmooth.differentiable (by simp)).differentiableAt
  have evaluatedSecondDerivative
      (inner outer : LorentzianIndex) :
      fderiv ℝ
          (fun candidate =>
            fderiv ℝ field candidate (coordinateDirection inner))
          point (coordinateDirection outer) =
        fderiv ℝ (fderiv ℝ field) point
          (coordinateDirection outer)
          (coordinateDirection inner) := by
    let evaluation :
        (BasePoint →L[ℝ] GravityMatrix) →L[ℝ] GravityMatrix :=
      ContinuousLinearMap.apply ℝ GravityMatrix (coordinateDirection inner)
    have hEvaluation : HasFDerivAt
        (fun candidate => evaluation (fderiv ℝ field candidate))
        (evaluation.comp (fderiv ℝ (fderiv ℝ field) point)) point := by
      exact evaluation.hasFDerivAt.comp point
        derivativeDifferentiable.hasFDerivAt
    have evaluated := congrArg
      (fun derivative : BasePoint →L[ℝ] GravityMatrix =>
        derivative (coordinateDirection outer))
      hEvaluation.fderiv
    change
      fderiv ℝ
          (fun candidate =>
            fderiv ℝ field candidate (coordinateDirection inner))
          point (coordinateDirection outer) =
        fderiv ℝ (fderiv ℝ field) point
          (coordinateDirection outer)
          (coordinateDirection inner)
      at evaluated
    exact evaluated
  have symmetricSecond : IsSymmSndFDerivAt ℝ field point :=
    smooth.contDiffAt.isSymmSndFDerivAt (by
      have finiteOrder : (2 : WithTop ℕ∞) ≤ ∞ :=
        WithTop.coe_le_coe.2 (OrderTop.le_top _)
      simpa [minSmoothness] using finiteOrder)
  unfold fieldDirectionalDerivative
  calc
    fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection first))
        point (coordinateDirection second) =
      fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection second)
        (coordinateDirection first) :=
      evaluatedSecondDerivative first second
    _ =
      fderiv ℝ (fderiv ℝ field) point
        (coordinateDirection first)
        (coordinateDirection second) :=
      symmetricSecond.eq
        (coordinateDirection second)
        (coordinateDirection first)
    _ =
      fderiv ℝ
        (fun candidate =>
          fderiv ℝ field candidate (coordinateDirection second))
        point (coordinateDirection first) :=
      (evaluatedSecondDerivative second first).symm

def connectionMatrix
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : LorentzianIndex) : GravityMatrix :=
  WithLp.toLp 2 fun index : LorentzianIndex × LorentzianIndex =>
    configuration.gravityConnection point direction index.1 index.2

theorem connectionMatrix_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzianIndex) :
    ContDiff ℝ ∞ fun point => connectionMatrix configuration point direction := by
  apply contDiff_piLp'
  rintro ⟨internalOut, internalIn⟩
  exact smooth.2.1 direction internalOut internalIn

def connectionMatrixDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) : GravityMatrix :=
  fieldDirectionalDerivative
    (fun candidate => connectionMatrix configuration candidate formDirection)
    point derivativeDirection

theorem connectionMatrixDerivative_apply
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (derivativeDirection formDirection internalOut internalIn : LorentzianIndex) :
    connectionMatrixDerivative configuration point derivativeDirection formDirection
        (internalOut, internalIn) =
      gravityConnectionDerivative configuration point derivativeDirection
        formDirection internalOut internalIn := by
  unfold connectionMatrixDerivative gravityConnectionDerivative
    fieldDirectionalDerivative connectionMatrix
  let projection : GravityMatrix →L[ℝ] ℝ :=
    EuclideanSpace.proj (internalOut, internalIn)
  have differentiable :=
    (connectionMatrix_contDiff configuration smooth formDirection).differentiable
      (by simp) point
  have composed :=
    (projection.hasFDerivAt.comp point differentiable.hasFDerivAt).fderiv
  have evaluated := congrArg
    (fun derivative : BasePoint →L[ℝ] ℝ =>
      derivative (coordinateDirection derivativeDirection)) composed
  simpa [projection, Function.comp_def, connectionMatrix] using evaluated.symm

theorem connectionMatrixDerivative_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (derivativeDirection formDirection : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      connectionMatrixDerivative configuration point
        derivativeDirection formDirection := by
  have derivativeSmooth : ContDiff ℝ ∞
      (fderiv ℝ fun point =>
        connectionMatrix configuration point formDirection) :=
    (connectionMatrix_contDiff configuration smooth formDirection).fderiv_right
      (m := ∞) (by simp)
  simpa [connectionMatrixDerivative, fieldDirectionalDerivative] using
    derivativeSmooth.clm_apply
      (contDiff_const : ContDiff ℝ ∞ fun _ : BasePoint =>
        coordinateDirection derivativeDirection)

theorem connectionMatrixDerivative_mixed_comm
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (formDirection first second : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          connectionMatrixDerivative configuration candidate
            first formDirection)
        point second =
      fieldDirectionalDerivative
        (fun candidate =>
          connectionMatrixDerivative configuration candidate
            second formDirection)
        point first := by
  unfold connectionMatrixDerivative
  exact mixedMatrixFieldDirectionalDerivative_comm
    (fun candidate => connectionMatrix configuration candidate formDirection)
    (connectionMatrix_contDiff configuration smooth formDirection)
    point first second

/-- Full ordered mixed-index curvature of the primitive gravity connection.
This exposes every ordered spacetime pair and every mixed internal component;
it is not an independently fillable curvature slot. -/
def orderedMixedCurvature
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (first second : LorentzianIndex) : GravityMatrix :=
  connectionMatrixDerivative configuration point first second -
    connectionMatrixDerivative configuration point second first +
    matrixBracket
      (connectionMatrix configuration point first)
      (connectionMatrix configuration point second)

def orderedMixedCurvatureDirectionalDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) : GravityMatrix :=
  fieldDirectionalDerivative
    (fun candidate => orderedMixedCurvature configuration candidate first second)
    point derivativeDirection

/-- Adjoint covariant derivative of the full mixed gravity curvature. -/
def covariantMixedCurvatureDerivative
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) : GravityMatrix :=
  orderedMixedCurvatureDirectionalDerivative configuration point
      derivativeDirection first second +
    matrixBracket
      (connectionMatrix configuration point derivativeDirection)
      (orderedMixedCurvature configuration point first second)

theorem orderedMixedCurvature_contDiff
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (first second : LorentzianIndex) :
    ContDiff ℝ ∞ fun point =>
      orderedMixedCurvature configuration point first second := by
  have firstDerivative := connectionMatrixDerivative_contDiff
    configuration smooth first second
  have secondDerivative := connectionMatrixDerivative_contDiff
    configuration smooth second first
  have bracketSmooth := matrixBracket_contDiff
    (fun point => connectionMatrix configuration point first)
    (fun point => connectionMatrix configuration point second)
    (connectionMatrix_contDiff configuration smooth first)
    (connectionMatrix_contDiff configuration smooth second)
  exact (firstDerivative.sub secondDerivative).add bracketSmooth

theorem fieldDirectionalDerivative_add_of_contDiff
    (first second : BasePoint → GravityMatrix)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => first candidate + second candidate)
        point direction =
      fieldDirectionalDerivative first point direction +
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_add
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

theorem fieldDirectionalDerivative_sub_of_contDiff
    (first second : BasePoint → GravityMatrix)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => first candidate - second candidate)
        point direction =
      fieldDirectionalDerivative first point direction -
        fieldDirectionalDerivative second point direction := by
  unfold fieldDirectionalDerivative
  rw [fderiv_fun_sub
    (firstSmooth.differentiable (by simp) point)
    (secondSmooth.differentiable (by simp) point)]
  rfl

def orderedMixedCurvatureDerivativeExpansion
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) : GravityMatrix :=
  fieldDirectionalDerivative
      (fun candidate =>
        connectionMatrixDerivative configuration candidate first second)
      point derivativeDirection -
    fieldDirectionalDerivative
      (fun candidate =>
        connectionMatrixDerivative configuration candidate second first)
      point derivativeDirection +
    matrixBracket
      (connectionMatrixDerivative configuration point derivativeDirection first)
      (connectionMatrix configuration point second) +
    matrixBracket
      (connectionMatrix configuration point first)
      (connectionMatrixDerivative configuration point derivativeDirection second)

theorem orderedMixedCurvatureDirectionalDerivative_eq_expansion
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (derivativeDirection first second : LorentzianIndex) :
    orderedMixedCurvatureDirectionalDerivative configuration point
        derivativeDirection first second =
      orderedMixedCurvatureDerivativeExpansion configuration point
        derivativeDirection first second := by
  have firstDerivativeSmooth := connectionMatrixDerivative_contDiff
    configuration smooth first second
  have secondDerivativeSmooth := connectionMatrixDerivative_contDiff
    configuration smooth second first
  have firstConnectionSmooth := connectionMatrix_contDiff
    configuration smooth first
  have secondConnectionSmooth := connectionMatrix_contDiff
    configuration smooth second
  have bracketSmooth := matrixBracket_contDiff
    (fun candidate => connectionMatrix configuration candidate first)
    (fun candidate => connectionMatrix configuration candidate second)
    firstConnectionSmooth secondConnectionSmooth
  unfold orderedMixedCurvatureDirectionalDerivative orderedMixedCurvature
  rw [fieldDirectionalDerivative_add_of_contDiff
    (fun candidate =>
      connectionMatrixDerivative configuration candidate first second -
        connectionMatrixDerivative configuration candidate second first)
    (fun candidate => matrixBracket
      (connectionMatrix configuration candidate first)
      (connectionMatrix configuration candidate second))
    (firstDerivativeSmooth.sub secondDerivativeSmooth) bracketSmooth]
  rw [fieldDirectionalDerivative_sub_of_contDiff
    (fun candidate =>
      connectionMatrixDerivative configuration candidate first second)
    (fun candidate =>
      connectionMatrixDerivative configuration candidate second first)
    firstDerivativeSmooth secondDerivativeSmooth]
  rw [fieldDirectionalDerivative_matrixBracket
    (fun candidate => connectionMatrix configuration candidate first)
    (fun candidate => connectionMatrix configuration candidate second)
    firstConnectionSmooth secondConnectionSmooth]
  unfold orderedMixedCurvatureDerivativeExpansion connectionMatrixDerivative
  abel

theorem orderedMixedCurvature_canonicalPair_eq_holonomic
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
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
  rw [connectionMatrixDerivative_apply configuration smooth,
    connectionMatrixDerivative_apply configuration smooth]
  simp [connectionMatrix]

/-- Off-shell differential Bianchi identity for the full mixed `gl(4)`
curvature generated by the actual primitive gravity connection. -/
theorem holonomicGravityGL4Curvature_bianchi
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (first second third : LorentzianIndex) :
    covariantMixedCurvatureDerivative configuration point first second third +
        covariantMixedCurvatureDerivative configuration point second third first +
        covariantMixedCurvatureDerivative configuration point third first second = 0 := by
  rw [show covariantMixedCurvatureDerivative configuration point first second third =
      orderedMixedCurvatureDerivativeExpansion configuration point first second third +
        matrixBracket (connectionMatrix configuration point first)
          (orderedMixedCurvature configuration point second third) by
    rw [covariantMixedCurvatureDerivative,
      orderedMixedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  rw [show covariantMixedCurvatureDerivative configuration point second third first =
      orderedMixedCurvatureDerivativeExpansion configuration point second third first +
        matrixBracket (connectionMatrix configuration point second)
          (orderedMixedCurvature configuration point third first) by
    rw [covariantMixedCurvatureDerivative,
      orderedMixedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  rw [show covariantMixedCurvatureDerivative configuration point third first second =
      orderedMixedCurvatureDerivativeExpansion configuration point third first second +
        matrixBracket (connectionMatrix configuration point third)
          (orderedMixedCurvature configuration point first second) by
    rw [covariantMixedCurvatureDerivative,
      orderedMixedCurvatureDirectionalDerivative_eq_expansion configuration smooth]]
  unfold orderedMixedCurvatureDerivativeExpansion orderedMixedCurvature
  simp only [matrixBracket_add_right, matrixBracket_sub_right]
  rw [connectionMatrixDerivative_mixed_comm
    configuration smooth point third second first]
  rw [connectionMatrixDerivative_mixed_comm
    configuration smooth point second third first]
  rw [connectionMatrixDerivative_mixed_comm
    configuration smooth point first third second]
  rw [matrixBracket_skew
    (connectionMatrixDerivative configuration point first second)
    (connectionMatrix configuration point third)]
  rw [matrixBracket_skew
    (connectionMatrixDerivative configuration point second third)
    (connectionMatrix configuration point first)]
  rw [matrixBracket_skew
    (connectionMatrixDerivative configuration point third first)
    (connectionMatrix configuration point second)]
  calc
    _ = matrixBracket (connectionMatrix configuration point first)
          (matrixBracket
            (connectionMatrix configuration point second)
            (connectionMatrix configuration point third)) +
        matrixBracket (connectionMatrix configuration point second)
          (matrixBracket
            (connectionMatrix configuration point third)
            (connectionMatrix configuration point first)) +
        matrixBracket (connectionMatrix configuration point third)
          (matrixBracket
            (connectionMatrix configuration point first)
            (connectionMatrix configuration point second)) := by
      abel
    _ = 0 := matrixBracket_jacobi
      (connectionMatrix configuration point first)
      (connectionMatrix configuration point second)
      (connectionMatrix configuration point third)

/-- Explicit domain gate for interpreting the primitive mixed connection as
an `so(1,3)` connection.  Smoothness alone does not prove this predicate. -/
def GravityConnectionLorentzAdmissible
    (configuration : StageNineHolonomicConfiguration) : Prop :=
  ∀ point, LorentzSkew (configuration.gravityConnection point)

theorem gravityConnection_lorentzSkew_of_admissible
    (configuration : StageNineHolonomicConfiguration)
    (admissible : GravityConnectionLorentzAdmissible configuration)
    (point : BasePoint) :
    LorentzSkew (configuration.gravityConnection point) :=
  admissible point

end

end SaturationMonoid.PhysicsCore.StageNineGravityBianchi
