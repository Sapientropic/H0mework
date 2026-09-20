import Mathlib.Analysis.Matrix.Order
import H0mework.Physics.Matter.SU7ExteriorBreakingYukawa

/-!
# S9-C3h200v: current-coframe Dirac temporal principal

The earlier Stage-9 matter producer inverted `i γ⁰` only on the
identity-coframe carrier.  This module extracts the actual temporal principal
at an arbitrary coframe:

```text
e
→ Γ₀(e) := Σₐ (e⁻¹)₀ₐ γᵃ
→ P₀(e) := i Γ₀(e)
→ q(e) := -Σₐ ηₐₐ ((e⁻¹)₀ₐ)²
→ P₀(e)² = q(e) id.
```

On the canonically defined noncharacteristic locus `q(e) ≠ 0`, the inverse is
therefore `q(e)⁻¹ P₀(e)`.  No inverse witness, square root, sign branch,
normalization parameter, residual, target derivative, or equation receipt is
accepted by the constructor.  The noncharacteristic hypothesis appears only
in theorems asserting that the total algebraic formula is an inverse.

This is the dependency-light algebraic producer core.  A later profile module
must prove that its source/action-generated coframe lies in the
noncharacteristic locus locally and must derive the corresponding density
term for the adjoint equation.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCurrentCoframeMatterTemporalPrincipal

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseLorentzianCoframeJet
open SU7ExteriorBreakingYukawa
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- The scalar square of the actual temporal Dirac principal.  Equivalently,
this is the negative inverse-metric time-time coefficient wherever the
coframe is nondegenerate. -/
def coframeTemporalPrincipalScalar
    (coframe : LorentzianCoframe) : ℝ :=
  -∑ internal : LorentzianIndex,
    minkowskiInternalSign internal *
      (coframe⁻¹ (0 : LorentzianIndex) internal) ^ 2

/-- Actual temporal principal `i Γ₀(e)` on the complete Stage-7 matter
carrier. -/
def currentCoframeMatterTemporalPrincipal
    (coframe : LorentzianCoframe) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • diracMatrixMatterAction
    (inverseCoframeDiracGamma
      { coframe := coframe, derivative := 0 }
      (0 : LorentzianIndex))

/-- The inverse-coframe gamma contraction squares to its Lorentzian norm.
The proof is a finite computation in the already established concrete
Clifford representation. -/
theorem inverseCoframeDiracGamma_time_sq
    (coframe : LorentzianCoframe) :
    inverseCoframeDiracGamma
          { coframe := coframe, derivative := 0 }
          (0 : LorentzianIndex) *
        inverseCoframeDiracGamma
          { coframe := coframe, derivative := 0 }
          (0 : LorentzianIndex) =
      (-(coframeTemporalPrincipalScalar coframe : ℂ)) •
        (1 : DiracMatrix) := by
  have iSq : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [inverseCoframeDiracGamma, coframeTemporalPrincipalScalar,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo,
      diracGammaThree, Matrix.mul_apply, Matrix.one_apply,
      minkowskiInternalSign, Fin.sum_univ_four] <;>
    ring_nf
  all_goals
    rw [iSq]
    ring

private theorem diracMatrixMatterAction_smul_one
    (coefficient : ℂ)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction
        (coefficient • (1 : DiracMatrix)) matter =
      coefficient • matter := by
  funext row
  fin_cases row <;>
    simp [diracMatrixMatterAction, Matrix.one_apply,
      Fin.sum_univ_four]

/-- The actual temporal matter principal has scalar square `q(e)`. -/
theorem currentCoframeMatterTemporalPrincipal_sq
    (coframe : LorentzianCoframe)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipal coframe
        (currentCoframeMatterTemporalPrincipal coframe matter) =
      (coframeTemporalPrincipalScalar coframe : ℂ) • matter := by
  unfold currentCoframeMatterTemporalPrincipal
  simp only [LinearMap.smul_apply]
  rw [map_smul, smul_smul, Complex.I_mul_I]
  rw [← LinearMap.comp_apply, ← diracMatrixMatterAction_mul]
  rw [inverseCoframeDiracGamma_time_sq]
  rw [diracMatrixMatterAction_smul_one]
  module

/-! ## Symmetric-hyperbolic coordinate-time principal -/

private def temporalDiracPrincipalMatrix
    (coframe : LorentzianCoframe) : DiracMatrix :=
  Complex.I • inverseCoframeDiracGamma
    { coframe := coframe, derivative := 0 } 0

private theorem temporalDiracPrincipalMatrix_sq
    (coframe : LorentzianCoframe) :
    temporalDiracPrincipalMatrix coframe *
        temporalDiracPrincipalMatrix coframe =
      (coframeTemporalPrincipalScalar coframe : ℂ) •
        (1 : DiracMatrix) := by
  unfold temporalDiracPrincipalMatrix
  rw [smul_mul_smul, Complex.I_mul_I,
    inverseCoframeDiracGamma_time_sq]
  module

private theorem temporalDiracPrincipalMatrix_frameTime_anticommute
    (coframe : LorentzianCoframe) :
    diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe +
        temporalDiracPrincipalMatrix coframe * diracFramePrincipal 0 =
      ((2 * coframe⁻¹ 0 0 : ℝ) : ℂ) • (1 : DiracMatrix) := by
  have iSq : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [pow_two, Complex.I_mul_I]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [temporalDiracPrincipalMatrix, diracFramePrincipal,
      inverseCoframeDiracGamma, diracGamma, diracGammaZero,
      diracGammaOne, diracGammaTwo, diracGammaThree,
      Fin.sum_univ_four] <;>
    ring_nf
  all_goals
    rw [iSq]
    ring

/-- The coordinate-time evolution principal obeys its Lorentzian quadratic
polynomial.  This is the algebraic bridge from a future-timelike inverse
coframe row to strict matrix positivity. -/
theorem coframeCoordinateDiracEvolutionPrincipal_time_quadratic
    (coframe : LorentzianCoframe) :
    let principal :=
      coframeCoordinateDiracEvolutionPrincipal coframe 0
    principal * principal +
        (coframeTemporalPrincipalScalar coframe : ℂ) •
          (1 : DiracMatrix) =
      ((2 * coframe⁻¹ 0 0 : ℝ) : ℂ) • principal := by
  dsimp
  change
    (diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe) *
          (diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe) +
        (coframeTemporalPrincipalScalar coframe : ℂ) •
          (1 : DiracMatrix) =
      ((2 * coframe⁻¹ 0 0 : ℝ) : ℂ) •
        (diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe)
  have timeSquare :
      diracFramePrincipal 0 * diracFramePrincipal 0 =
        (1 : DiracMatrix) :=
    diracFrameEvolutionPrincipal_time_eq_one
  have temporalSquare := temporalDiracPrincipalMatrix_sq coframe
  have anticommutator :=
    temporalDiracPrincipalMatrix_frameTime_anticommute coframe
  have reversedProduct :
      temporalDiracPrincipalMatrix coframe * diracFramePrincipal 0 =
        ((2 * coframe⁻¹ 0 0 : ℝ) : ℂ) •
            (1 : DiracMatrix) -
          diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe := by
    exact eq_sub_of_add_eq' anticommutator
  rw [← mul_assoc
      (diracFramePrincipal 0 * temporalDiracPrincipalMatrix coframe)
      (diracFramePrincipal 0) (temporalDiracPrincipalMatrix coframe),
    mul_assoc (diracFramePrincipal 0)
      (temporalDiracPrincipalMatrix coframe) (diracFramePrincipal 0),
    reversedProduct]
  noncomm_ring [timeSquare, temporalSquare]

/-- A future-timelike coordinate-time inverse-coframe row makes the
transformed Dirac time coefficient strictly positive definite. -/
theorem coframeCoordinateDiracEvolutionPrincipal_posDef_of_futureTimelike
    (coframe : LorentzianCoframe)
    (future : 0 < coframe⁻¹ 0 0)
    (timelike : 0 < coframeTemporalPrincipalScalar coframe) :
    (coframeCoordinateDiracEvolutionPrincipal coframe 0).PosDef := by
  let principal := coframeCoordinateDiracEvolutionPrincipal coframe 0
  have principalHermitian : principal.IsHermitian :=
    coframeCoordinateDiracEvolutionPrincipal_isHermitian coframe 0
  have principalSquareSemidefinite :
      (principal * principal).PosSemidef := by
    simpa [principalHermitian.eq] using
      (Matrix.posSemidef_conjTranspose_mul_self principal)
  have scalarIdentityPositive :
      (coframeTemporalPrincipalScalar coframe •
        (1 : DiracMatrix)).PosDef :=
    Matrix.PosDef.one.smul timelike
  have numeratorPositive :
      (principal * principal +
        coframeTemporalPrincipalScalar coframe •
          (1 : DiracMatrix)).PosDef :=
    Matrix.PosDef.posSemidef_add
      principalSquareSemidefinite scalarIdentityPositive
  have twiceFuture : 0 < 2 * coframe⁻¹ 0 0 :=
    mul_pos (by norm_num) future
  have scaledPositive :
      ((2 * coframe⁻¹ 0 0)⁻¹ •
        (principal * principal +
          coframeTemporalPrincipalScalar coframe •
            (1 : DiracMatrix))).PosDef :=
    numeratorPositive.smul (inv_pos.mpr twiceFuture)
  have quadraticComplex :=
    coframeCoordinateDiracEvolutionPrincipal_time_quadratic coframe
  dsimp only at quadraticComplex
  have quadraticReal :
      principal * principal +
          coframeTemporalPrincipalScalar coframe •
            (1 : DiracMatrix) =
        (2 * coframe⁻¹ 0 0) • principal := by
    ext row column
    have entry := congrFun (congrFun quadraticComplex row) column
    simpa only [principal, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul, smul_eq_mul] using entry
  rw [quadraticReal] at scaledPositive
  simpa only [smul_smul, inv_mul_cancel₀ twiceFuture.ne', one_smul]
    using scaledPositive

/-- Canonical total formula for the temporal principal inverse.  It is
meaningful as an inverse precisely on the noncharacteristic locus; no proof
or branch data is stored in the value. -/
def currentCoframeMatterTemporalPrincipalInverse
    (coframe : LorentzianCoframe) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  ((coframeTemporalPrincipalScalar coframe : ℂ)⁻¹) •
    currentCoframeMatterTemporalPrincipal coframe

theorem currentCoframeMatterTemporalPrincipalInverse_left
    (coframe : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar coframe ≠ 0)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipalInverse coframe
        (currentCoframeMatterTemporalPrincipal coframe matter) =
      matter := by
  have noncharacteristicComplex :
      (coframeTemporalPrincipalScalar coframe : ℂ) ≠ 0 := by
    exact_mod_cast noncharacteristic
  unfold currentCoframeMatterTemporalPrincipalInverse
  rw [LinearMap.smul_apply,
    currentCoframeMatterTemporalPrincipal_sq]
  simp [smul_smul, noncharacteristicComplex]

theorem currentCoframeMatterTemporalPrincipalInverse_right
    (coframe : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar coframe ≠ 0)
    (matter : DiracExteriorMatterCarrier) :
    currentCoframeMatterTemporalPrincipal coframe
        (currentCoframeMatterTemporalPrincipalInverse coframe matter) =
      matter := by
  have noncharacteristicComplex :
      (coframeTemporalPrincipalScalar coframe : ℂ) ≠ 0 := by
    exact_mod_cast noncharacteristic
  unfold currentCoframeMatterTemporalPrincipalInverse
  simp only [LinearMap.smul_apply]
  rw [map_smul, currentCoframeMatterTemporalPrincipal_sq]
  simp [smul_smul, noncharacteristicComplex]

/-- Current-coframe temporal Dirac action law with all non-temporal terms
already generated by the action graph. -/
def CurrentCoframeMatterTemporalActionLaw
    (coframe : LorentzianCoframe)
    (knownVector timeCovariantDerivative :
      DiracExteriorMatterCarrier) : Prop :=
  currentCoframeMatterTemporalPrincipal coframe timeCovariantDerivative +
      knownVector =
    0

/-- Branch-free action-generated temporal covariant derivative. -/
def actionGeneratedCurrentCoframeMatterTemporalDerivative
    (coframe : LorentzianCoframe)
    (knownVector : DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  -currentCoframeMatterTemporalPrincipalInverse coframe knownVector

theorem
    actionGeneratedCurrentCoframeMatterTemporalDerivative_satisfies_actionLaw
    (coframe : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar coframe ≠ 0)
    (knownVector : DiracExteriorMatterCarrier) :
    CurrentCoframeMatterTemporalActionLaw coframe knownVector
      (actionGeneratedCurrentCoframeMatterTemporalDerivative
        coframe knownVector) := by
  unfold CurrentCoframeMatterTemporalActionLaw
    actionGeneratedCurrentCoframeMatterTemporalDerivative
  rw [map_neg,
    currentCoframeMatterTemporalPrincipalInverse_right]
  · simp
  · exact noncharacteristic

/-- The current-coframe action law has no hidden temporal branch. -/
theorem currentCoframeMatterTemporalActionLaw_unique
    (coframe : LorentzianCoframe)
    (noncharacteristic : coframeTemporalPrincipalScalar coframe ≠ 0)
    (knownVector first second : DiracExteriorMatterCarrier)
    (firstLaw :
      CurrentCoframeMatterTemporalActionLaw coframe knownVector first)
    (secondLaw :
      CurrentCoframeMatterTemporalActionLaw coframe knownVector second) :
    first = second := by
  have principalEqual :
      currentCoframeMatterTemporalPrincipal coframe first =
        currentCoframeMatterTemporalPrincipal coframe second := by
    unfold CurrentCoframeMatterTemporalActionLaw at firstLaw secondLaw
    calc
      currentCoframeMatterTemporalPrincipal coframe first =
          -knownVector :=
        eq_neg_of_add_eq_zero_left firstLaw
      _ =
          currentCoframeMatterTemporalPrincipal coframe second :=
        (eq_neg_of_add_eq_zero_left secondLaw).symm
  calc
    first =
        currentCoframeMatterTemporalPrincipalInverse coframe
          (currentCoframeMatterTemporalPrincipal coframe first) :=
      (currentCoframeMatterTemporalPrincipalInverse_left
        coframe noncharacteristic first).symm
    _ =
        currentCoframeMatterTemporalPrincipalInverse coframe
          (currentCoframeMatterTemporalPrincipal coframe second) := by
      rw [principalEqual]
    _ = second :=
      currentCoframeMatterTemporalPrincipalInverse_left
        coframe noncharacteristic second

@[simp] theorem coframeTemporalPrincipalScalar_one :
    coframeTemporalPrincipalScalar (1 : LorentzianCoframe) = 1 := by
  simp [coframeTemporalPrincipalScalar, minkowskiInternalSign,
    Matrix.one_apply, Fin.sum_univ_four]

end

end
  SaturationMonoid.PhysicsCore.StageNineCurrentCoframeMatterTemporalPrincipal
