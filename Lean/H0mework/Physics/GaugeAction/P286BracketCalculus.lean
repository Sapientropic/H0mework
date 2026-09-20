import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# S9-C3f0: dependency-light P286 bracket calculus

This module isolates exactly the Lie-algebra and smooth-calculus facts needed
by the P286 Bianchi identity.  The bracket is the actual matrix commutator on
the typed `su(3) × su(2) × u(1)` carrier, transported through the already
chosen faithful finite coordinates.  No curvature, Bianchi, field equation,
stationarity, current, or conservation certificate is accepted as data.

The two analytic inputs are the derivative rule for a continuous bilinear map
and symmetry of the second Fréchet derivative of a smooth field.  In
particular, no monoid associativity claim is used as a substitute for the
matrix Jacobi identity.
-/

namespace SaturationMonoid.PhysicsCore.StageNineP286BracketCalculus

open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open scoped ContDiff

noncomputable section

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-- The actual typed P286 commutator transported to its chosen finite real
coordinate space. -/
def coordinateBracket
    (first second : P286CoordinateCarrier) : P286CoordinateCarrier :=
  p286CoordinateEquiv
    (p286LieBracket (p286CoordinateEquiv.symm first)
      (p286CoordinateEquiv.symm second))

theorem suLieBracket_add_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (first + second) residual =
      suLieBracket first residual + suLieBracket second residual := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_add_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (first + second) =
      suLieBracket residual first + suLieBracket residual second := by
  apply Subtype.ext
  simp [suLieBracket, Matrix.add_mul, Matrix.mul_add]
  abel

theorem suLieBracket_smul_left
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket (parameter • first) residual =
      parameter • suLieBracket first residual := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem suLieBracket_smul_right
    {n : Type*} [Fintype n] [DecidableEq n]
    (parameter : ℝ) (first residual : SpecialUnitaryLieMatrix n) :
    suLieBracket residual (parameter • first) =
      parameter • suLieBracket residual first := by
  apply Subtype.ext
  simp [suLieBracket]
  rw [smul_sub]

theorem p286LieBracket_add_left
    (first second residual : P286LieBlockData) :
    p286LieBracket (first + second) residual =
      p286LieBracket first residual + p286LieBracket second residual := by
  apply Prod.ext
  · exact suLieBracket_add_left first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_left first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_add_right
    (first second residual : P286LieBlockData) :
    p286LieBracket residual (first + second) =
      p286LieBracket residual first + p286LieBracket residual second := by
  apply Prod.ext
  · exact suLieBracket_add_right first.1 second.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_add_right first.2.1 second.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_left
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket (parameter • first) residual =
      parameter • p286LieBracket first residual := by
  apply Prod.ext
  · exact suLieBracket_smul_left parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_left parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_smul_right
    (parameter : ℝ) (first residual : P286LieBlockData) :
    p286LieBracket residual (parameter • first) =
      parameter • p286LieBracket residual first := by
  apply Prod.ext
  · exact suLieBracket_smul_right parameter first.1 residual.1
  · apply Prod.ext
    · exact suLieBracket_smul_right parameter first.2.1 residual.2.1
    · simp [p286LieBracket]

theorem coordinateBracket_add_left
    (first second residual : P286CoordinateCarrier) :
    coordinateBracket (first + second) residual =
      coordinateBracket first residual + coordinateBracket second residual := by
  unfold coordinateBracket
  rw [p286CoordinateEquiv.symm.map_add, p286LieBracket_add_left, map_add]

theorem coordinateBracket_add_right
    (first second residual : P286CoordinateCarrier) :
    coordinateBracket residual (first + second) =
      coordinateBracket residual first + coordinateBracket residual second := by
  unfold coordinateBracket
  rw [p286CoordinateEquiv.symm.map_add, p286LieBracket_add_right, map_add]

theorem coordinateBracket_smul_left
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    coordinateBracket (parameter • first) residual =
      parameter • coordinateBracket first residual := by
  unfold coordinateBracket
  rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBracket_smul_left, map_smul]

theorem coordinateBracket_smul_right
    (parameter : ℝ) (first residual : P286CoordinateCarrier) :
    coordinateBracket residual (parameter • first) =
      parameter • coordinateBracket residual first := by
  unfold coordinateBracket
  rw [p286CoordinateEquiv.symm.map_smul,
    p286LieBracket_smul_right, map_smul]

theorem coordinateBracket_neg_left
    (first residual : P286CoordinateCarrier) :
    coordinateBracket (-first) residual = -coordinateBracket first residual := by
  simpa only [neg_one_smul] using
    coordinateBracket_smul_left (-1) first residual

theorem coordinateBracket_neg_right
    (first residual : P286CoordinateCarrier) :
    coordinateBracket residual (-first) = -coordinateBracket residual first := by
  simpa only [neg_one_smul] using
    coordinateBracket_smul_right (-1) first residual

theorem coordinateBracket_sub_left
    (first second residual : P286CoordinateCarrier) :
    coordinateBracket (first - second) residual =
      coordinateBracket first residual - coordinateBracket second residual := by
  rw [sub_eq_add_neg, coordinateBracket_add_left,
    coordinateBracket_neg_left, sub_eq_add_neg]

theorem coordinateBracket_sub_right
    (first second residual : P286CoordinateCarrier) :
    coordinateBracket residual (first - second) =
      coordinateBracket residual first - coordinateBracket residual second := by
  rw [sub_eq_add_neg, coordinateBracket_add_right,
    coordinateBracket_neg_right, sub_eq_add_neg]

/-- The actual P286 bracket as a continuous bilinear map in the faithful
finite coordinate chart. -/
def coordinateBracketBilinear :
    P286CoordinateCarrier →ₗ[ℝ]
      P286CoordinateCarrier →ₗ[ℝ] P286CoordinateCarrier where
  toFun first :=
    { toFun := fun second => coordinateBracket first second
      map_add' := by
        intro second third
        exact coordinateBracket_add_right second third first
      map_smul' := by
        intro parameter second
        exact coordinateBracket_smul_right parameter second first }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro residual
    exact coordinateBracket_add_left first second residual
  map_smul' := by
    intro parameter first
    apply LinearMap.ext
    intro residual
    exact coordinateBracket_smul_left parameter first residual

@[simp] theorem coordinateBracketBilinear_apply
    (first second : P286CoordinateCarrier) :
    coordinateBracketBilinear first second = coordinateBracket first second :=
  rfl

theorem suLieBracket_skew
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second : SpecialUnitaryLieMatrix n) :
    suLieBracket first second = -suLieBracket second first := by
  apply Subtype.ext
  simp [suLieBracket]

theorem suLieBracket_jacobi
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second third : SpecialUnitaryLieMatrix n) :
    suLieBracket first (suLieBracket second third) +
        suLieBracket second (suLieBracket third first) +
        suLieBracket third (suLieBracket first second) = 0 := by
  apply Subtype.ext
  simp [suLieBracket]
  noncomm_ring

theorem p286LieBracket_skew (first second : P286LieBlockData) :
    p286LieBracket first second = -p286LieBracket second first := by
  apply Prod.ext
  · exact suLieBracket_skew first.1 second.1
  · apply Prod.ext
    · exact suLieBracket_skew first.2.1 second.2.1
    · simp [p286LieBracket]

theorem p286LieBracket_jacobi
    (first second third : P286LieBlockData) :
    p286LieBracket first (p286LieBracket second third) +
        p286LieBracket second (p286LieBracket third first) +
        p286LieBracket third (p286LieBracket first second) = 0 := by
  apply Prod.ext
  · exact suLieBracket_jacobi first.1 second.1 third.1
  · apply Prod.ext
    · exact suLieBracket_jacobi first.2.1 second.2.1 third.2.1
    · simp [p286LieBracket]

theorem coordinateBracket_skew
    (first second : P286CoordinateCarrier) :
    coordinateBracket first second = -coordinateBracket second first := by
  apply p286CoordinateEquiv.symm.injective
  simpa [coordinateBracket] using
    p286LieBracket_skew (p286CoordinateEquiv.symm first)
      (p286CoordinateEquiv.symm second)

theorem coordinateBracket_jacobi
    (first second third : P286CoordinateCarrier) :
    coordinateBracket first (coordinateBracket second third) +
        coordinateBracket second (coordinateBracket third first) +
        coordinateBracket third (coordinateBracket first second) = 0 := by
  apply p286CoordinateEquiv.symm.injective
  simpa [coordinateBracket] using
    p286LieBracket_jacobi (p286CoordinateEquiv.symm first)
      (p286CoordinateEquiv.symm second)
      (p286CoordinateEquiv.symm third)

theorem coordinateBracket_contDiff
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second) :
    ContDiff ℝ ∞ fun point =>
      coordinateBracket (first point) (second point) := by
  have outerSmooth : ContDiff ℝ ∞ fun point =>
      coordinateBracketBilinear.toContinuousBilinearMap (first point) :=
    coordinateBracketBilinear.toContinuousBilinearMap.contDiff.comp
      firstSmooth
  simpa [coordinateBracketBilinear] using
    outerSmooth.clm_apply secondSmooth

/-- Directional Leibniz rule for the actual typed P286 bracket. -/
theorem fieldDirectionalDerivative_coordinateBracket
    (first second : BasePoint → P286CoordinateCarrier)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => coordinateBracket (first candidate) (second candidate))
        point direction =
      coordinateBracket
          (fieldDirectionalDerivative first point direction) (second point) +
        coordinateBracket (first point)
          (fieldDirectionalDerivative second point direction) := by
  let bracket := coordinateBracketBilinear.toContinuousBilinearMap
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
    coordinateBracket (first point)
          (fieldDirectionalDerivative second point direction) +
        coordinateBracket
          (fieldDirectionalDerivative first point direction) (second point) = _
  abel

/-- Schwarz symmetry for the two actual coordinate-direction Fréchet
derivatives of a smooth P286-coordinate field. -/
theorem mixedFieldDirectionalDerivative_comm
    (field : BasePoint → P286CoordinateCarrier)
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
        (BasePoint →L[ℝ] P286CoordinateCarrier) →L[ℝ]
          P286CoordinateCarrier :=
      ContinuousLinearMap.apply ℝ P286CoordinateCarrier
        (coordinateDirection inner)
    have hEvaluation : HasFDerivAt
        (fun candidate => evaluation (fderiv ℝ field candidate))
        (evaluation.comp (fderiv ℝ (fderiv ℝ field) point)) point := by
      exact evaluation.hasFDerivAt.comp point
        derivativeDifferentiable.hasFDerivAt
    have evaluated := congrArg
      (fun derivative : BasePoint →L[ℝ] P286CoordinateCarrier =>
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

end

end SaturationMonoid.PhysicsCore.StageNineP286BracketCalculus
