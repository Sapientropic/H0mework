import H0mework.Physics.Holonomic.HolonomicField

/-!
# Lightweight directional calculus for Dirac matter coordinates

This module isolates the finite-dimensional bilinear calculus used by local
Spin transport.  The derivative of a matrix action is computed from the two
actual input fields.  No matrix derivative, transformed matter jet, or
covariance receipt is accepted as an independent input.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracMatterCoordinateCalculus

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineHolonomicField

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false

/-- Directional chain rule for a continuous bilinear map on actual smooth
fields. -/
theorem fieldDirectionalDerivative_continuousBilinear
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (bilinear : V →L[ℝ] W →L[ℝ] X)
    (first : BasePoint → V) (second : BasePoint → W)
    (firstSmooth : ContDiff ℝ ∞ first)
    (secondSmooth : ContDiff ℝ ∞ second)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate => bilinear (first candidate) (second candidate))
        point direction =
      bilinear (fieldDirectionalDerivative first point direction)
          (second point) +
        bilinear (first point)
          (fieldDirectionalDerivative second point direction) := by
  have firstDifferentiable : DifferentiableAt ℝ first point :=
    (firstSmooth.differentiable (by simp)).differentiableAt
  have secondDifferentiable : DifferentiableAt ℝ second point :=
    (secondSmooth.differentiable (by simp)).differentiableAt
  have outerDerivative : HasFDerivAt
      (fun candidate => bilinear (first candidate))
      (bilinear.comp (fderiv ℝ first point)) point :=
    bilinear.hasFDerivAt.comp point firstDifferentiable.hasFDerivAt
  have totalDerivative :
      fderiv ℝ
          (fun candidate => bilinear (first candidate) (second candidate))
          point =
        (bilinear (first point)).comp (fderiv ℝ second point) +
          (bilinear.comp (fderiv ℝ first point)).flip (second point) :=
    (outerDerivative.clm_apply secondDifferentiable.hasFDerivAt).fderiv
  change
    fderiv ℝ
        (fun candidate => bilinear (first candidate) (second candidate))
        point (coordinateDirection direction) = _
  rw [totalDerivative]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  change
    bilinear (first point)
          (fieldDirectionalDerivative second point direction) +
        bilinear (fieldDirectionalDerivative first point direction)
          (second point) = _
  abel

/-- Additivity of the actual Dirac action in its matrix input. -/
theorem diracMatrixMatterAction_add_matrix
    (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first + second) matter =
      diracMatrixMatterAction first matter +
        diracMatrixMatterAction second matter := by
  funext row
  simp [diracMatrixMatterAction, add_smul, Finset.sum_add_distrib]

/-- Subtractivity of the actual Dirac action in its matrix input. -/
theorem diracMatrixMatterAction_sub_matrix
    (first second : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (first - second) matter =
      diracMatrixMatterAction first matter -
        diracMatrixMatterAction second matter := by
  funext row
  change
    (∑ column : DiracSpinorIndex,
      (first row column - second row column) • matter column) =
      (∑ column : DiracSpinorIndex,
        first row column • matter column) -
        ∑ column : DiracSpinorIndex,
          second row column • matter column
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro column _
  module

/-- Complex linearity of the actual Dirac action in its matrix input. -/
theorem diracMatrixMatterAction_smul_matrix
    (parameter : ℂ) (matrix : DiracMatrix)
    (matter : DiracExteriorMatterCarrier) :
    diracMatrixMatterAction (parameter • matrix) matter =
      parameter • diracMatrixMatterAction matrix matter := by
  funext row
  change
    (∑ column : DiracSpinorIndex,
      (parameter * matrix row column) • matter column) =
      parameter •
        ∑ column : DiracSpinorIndex,
          matrix row column • matter column
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [smul_smul]

/-- Complex-bilinear coordinate form of the actual Dirac-matrix action. -/
def diracMatrixMatterCoordinateBilinear :
    DiracMatrix →ₗ[ℂ]
      MatterCoordinateCarrier →ₗ[ℂ] MatterCoordinateCarrier where
  toFun matrix :=
    { toFun := fun coordinates =>
        matterCoordinateEquiv
          (diracMatrixMatterAction matrix
            (matterCoordinateEquiv.symm coordinates))
      map_add' := by
        intro first second
        simp only [map_add]
      map_smul' := by
        intro parameter coordinates
        simp only [map_smul, RingHom.id_apply] }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro coordinates
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (first + second)
            (matterCoordinateEquiv.symm coordinates)) =
        matterCoordinateEquiv
            (diracMatrixMatterAction first
              (matterCoordinateEquiv.symm coordinates)) +
          matterCoordinateEquiv
            (diracMatrixMatterAction second
              (matterCoordinateEquiv.symm coordinates))
    rw [diracMatrixMatterAction_add_matrix, map_add]
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro coordinates
    change
      matterCoordinateEquiv
          (diracMatrixMatterAction (parameter • matrix)
            (matterCoordinateEquiv.symm coordinates)) =
        parameter •
          matterCoordinateEquiv
            (diracMatrixMatterAction matrix
              (matterCoordinateEquiv.symm coordinates))
    rw [diracMatrixMatterAction_smul_matrix, map_smul]

/-- Real-bilinear restriction used by the real Fréchet derivative. -/
def diracMatrixMatterCoordinateRealBilinear :
    DiracMatrix →ₗ[ℝ]
      MatterCoordinateCarrier →ₗ[ℝ] MatterCoordinateCarrier where
  toFun matrix :=
    (diracMatrixMatterCoordinateBilinear matrix).restrictScalars ℝ
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro matter
    exact LinearMap.congr_fun
      (diracMatrixMatterCoordinateBilinear.map_add first second) matter
  map_smul' := by
    intro parameter matrix
    apply LinearMap.ext
    intro matter
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact LinearMap.congr_fun
      (diracMatrixMatterCoordinateBilinear.map_smul
        (parameter : ℂ) matrix) matter

@[simp] theorem diracMatrixMatterCoordinateRealBilinear_apply
    (matrix : DiracMatrix) (coordinates : MatterCoordinateCarrier) :
    diracMatrixMatterCoordinateRealBilinear matrix coordinates =
      matterCoordinateEquiv
        (diracMatrixMatterAction matrix
          (matterCoordinateEquiv.symm coordinates)) :=
  rfl

/-- Product rule for an actual Dirac-matrix field acting on an actual matter
coordinate field. -/
theorem fieldDirectionalDerivative_diracMatrixMatterCoordinate
    (matrix : BasePoint → DiracMatrix)
    (matter : BasePoint → MatterCoordinateCarrier)
    (matrixSmooth : ContDiff ℝ ∞ matrix)
    (matterSmooth : ContDiff ℝ ∞ matter)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (fun candidate =>
          diracMatrixMatterCoordinateRealBilinear
            (matrix candidate) (matter candidate))
        point direction =
      diracMatrixMatterCoordinateRealBilinear
          (fieldDirectionalDerivative matrix point direction)
          (matter point) +
        diracMatrixMatterCoordinateRealBilinear (matrix point)
          (fieldDirectionalDerivative matter point direction) :=
  fieldDirectionalDerivative_continuousBilinear
    diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
    matrix matter matrixSmooth matterSmooth point direction

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracMatterCoordinateCalculus
