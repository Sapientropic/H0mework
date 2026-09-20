import H0mework.Physics.Holonomic.CoframeHolonomicSecondJetCarrier
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Canonical matrix-exponential realization of a coframe second jet

This module exponentiates the canonical homogeneous-quadratic realization of
a holonomic coframe Hessian.  The resulting coframe is smooth and invertible
at every point while retaining the supplied origin Hessian exactly.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicMatrixExponentialRealization

open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeHolonomicSecondJetCarrier
open StageNineHolonomicField
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev CoframeEndSpace :=
  WithLp 2 (LorentzianIndex → ℝ)

private noncomputable def coframeEndAlgEquiv :
    LorentzianCoframe ≃ₐ[ℝ]
      (CoframeEndSpace →L[ℝ] CoframeEndSpace) :=
  (Matrix.toLpLinAlgEquiv (R := ℝ) (n := LorentzianIndex) 2).trans
    (Module.End.toContinuousLinearMap CoframeEndSpace)

private noncomputable def coframeEndContinuousLinearEquiv :
    LorentzianCoframe ≃L[ℝ]
      (CoframeEndSpace →L[ℝ] CoframeEndSpace) :=
  coframeEndAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

private local instance coframeEndRatNormedAlgebra :
    NormedAlgebra ℚ (CoframeEndSpace →L[ℝ] CoframeEndSpace) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

private theorem coframeEnd_exp_contDiff :
    ContDiff ℝ ∞
      (NormedSpace.exp :
        (CoframeEndSpace →L[ℝ] CoframeEndSpace) →
          (CoframeEndSpace →L[ℝ] CoframeEndSpace)) :=
  contDiff_iff_contDiffAt.mpr fun point =>
    (NormedSpace.exp_analytic point).contDiffAt

def coframeMatrixExponential
    (matrix : LorentzianCoframe) : LorentzianCoframe :=
  coframeEndAlgEquiv.symm
    (NormedSpace.exp (coframeEndAlgEquiv matrix))

theorem coframeMatrixExponential_contDiff :
    ContDiff ℝ ∞ coframeMatrixExponential := by
  change ContDiff ℝ ∞ fun matrix =>
    coframeEndContinuousLinearEquiv.symm
      (NormedSpace.exp (coframeEndContinuousLinearEquiv matrix))
  exact coframeEndContinuousLinearEquiv.symm.contDiff.comp
    (coframeEnd_exp_contDiff.comp
      coframeEndContinuousLinearEquiv.contDiff)

theorem coframeMatrixExponential_hasFDerivAt_zero :
    HasFDerivAt coframeMatrixExponential
      (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe) 0 := by
  have mappedDerivativeRaw :=
    coframeEndContinuousLinearEquiv.hasFDerivAt
      (x := (0 : LorentzianCoframe))
  have mappedDerivative :
      HasFDerivAt coframeEndContinuousLinearEquiv
        (coframeEndContinuousLinearEquiv :
          LorentzianCoframe →L[ℝ]
            (CoframeEndSpace →L[ℝ] CoframeEndSpace)) 0 := by
    convert mappedDerivativeRaw using 1
  have exponentialDerivativeAtMappedZero :
      HasFDerivAt
        (NormedSpace.exp :
          (CoframeEndSpace →L[ℝ] CoframeEndSpace) →
            (CoframeEndSpace →L[ℝ] CoframeEndSpace))
        (1 :
          (CoframeEndSpace →L[ℝ] CoframeEndSpace) →L[ℝ]
            (CoframeEndSpace →L[ℝ] CoframeEndSpace))
        (coframeEndContinuousLinearEquiv (0 : LorentzianCoframe)) := by
    simpa using
      (hasFDerivAt_exp_zero :
        HasFDerivAt
          (NormedSpace.exp :
            (CoframeEndSpace →L[ℝ] CoframeEndSpace) →
              (CoframeEndSpace →L[ℝ] CoframeEndSpace))
          (1 :
            (CoframeEndSpace →L[ℝ] CoframeEndSpace) →L[ℝ]
              (CoframeEndSpace →L[ℝ] CoframeEndSpace)) 0)
  have exponentialDerivativeRaw :=
    exponentialDerivativeAtMappedZero.comp 0 mappedDerivative
  have pulledDerivativeRaw :=
    coframeEndContinuousLinearEquiv.symm.hasFDerivAt.comp 0
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
  · ext matrix
    simp

@[simp] theorem coframeMatrixExponential_zero :
    coframeMatrixExponential 0 = 1 := by
  simp [coframeMatrixExponential]

/-- The matrix exponential is invertible at every input. -/
theorem coframeMatrixExponential_det_ne_zero
    (matrix : LorentzianCoframe) :
    Matrix.det (coframeMatrixExponential matrix) ≠ 0 := by
  have exponentIsUnit :
      IsUnit
        (NormedSpace.exp
          (coframeEndAlgEquiv matrix)) :=
    NormedSpace.isUnit_exp _
  have exponentialIsUnit : IsUnit (coframeMatrixExponential matrix) :=
    exponentIsUnit.map coframeEndAlgEquiv.symm.toRingHom
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp exponentialIsUnit)

private def radialLine (direction : BasePoint) : ℝ →L[ℝ] BasePoint :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight direction

private theorem iteratedDeriv_radialLine_two
    (field : BasePoint → LorentzianCoframe)
    (fieldSmooth : ContDiff ℝ 2 field)
    (direction : BasePoint) :
    iteratedDeriv 2 (field ∘ radialLine direction) 0 =
      fderiv ℝ (fderiv ℝ field) 0 direction direction := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [(radialLine direction).iteratedFDeriv_comp_right
    fieldSmooth 0 (by simp)]
  simp [iteratedFDeriv_two_apply, radialLine]

private theorem quadraticRealization_radialLine_deriv_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    deriv
        (coframeHolonomicSecondJetQuadraticRealization jet ∘
          radialLine direction) 0 = 0 := by
  have derivativeEquality := congrArg
    (fun derivative => derivative (fun _ : Fin 1 => (1 : ℝ)))
    ((radialLine direction).iteratedFDeriv_comp_right
      (coframeHolonomicSecondJetQuadraticRealization_contDiff jet)
      0 (i := 1) (by exact WithTop.coe_le_coe.mpr le_top))
  simp only [iteratedFDeriv_one_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    at derivativeEquality
  unfold deriv
  rw [derivativeEquality,
    (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0).fderiv]
  simp

private theorem quadraticRealization_radialLine_iteratedDeriv_two_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    iteratedDeriv 2
        (coframeHolonomicSecondJetQuadraticRealization jet ∘
          radialLine direction) 0 =
      jet.1 direction direction := by
  rw [iteratedDeriv_radialLine_two
    (coframeHolonomicSecondJetQuadraticRealization jet)
    ((coframeHolonomicSecondJetQuadraticRealization_contDiff jet).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)) direction]
  change
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetQuadraticRealization jet)
        direction direction = _
  rw [coframeHolonomicSecondJetQuadraticRealization_secondJet]

private theorem matrixExponentialQuadratic_radialLine_iteratedDeriv_two_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    iteratedDeriv 2
        (coframeMatrixExponential ∘
          (coframeHolonomicSecondJetQuadraticRealization jet ∘
            radialLine direction)) 0 =
      jet.1 direction direction := by
  have chainRule := iteratedDeriv_vcomp_two
    (g := coframeMatrixExponential)
    (f := coframeHolonomicSecondJetQuadraticRealization jet ∘
      radialLine direction)
    (x := 0)
    ((coframeMatrixExponential_contDiff.of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    (((coframeHolonomicSecondJetQuadraticRealization_contDiff jet).comp
      (radialLine direction).contDiff).of_le
        (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)
  rw [show
      (coframeHolonomicSecondJetQuadraticRealization jet ∘
        radialLine direction) 0 = 0 by simp]
    at chainRule
  rw [quadraticRealization_radialLine_deriv_origin,
    quadraticRealization_radialLine_iteratedDeriv_two_origin,
    coframeMatrixExponential_hasFDerivAt_zero.fderiv] at chainRule
  have quadraticOuterTermVanishes :
      iteratedFDeriv ℝ 2 coframeMatrixExponential 0
          (fun _ : Fin 2 => (0 : LorentzianCoframe)) = 0 := by
    exact ContinuousMultilinearMap.map_zero _
  rw [quadraticOuterTermVanishes, zero_add] at chainRule
  simpa using chainRule

/-- The matrix exponential of the canonical quadratic realization of a
holonomic coframe Hessian. -/
def coframeHolonomicSecondJetMatrixExponentialRealization
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    LorentzianCoframe :=
  coframeEndAlgEquiv.symm
    (NormedSpace.exp
      (coframeEndAlgEquiv
        (coframeHolonomicSecondJetQuadraticRealization jet point)))

@[simp] theorem coframeHolonomicSecondJetMatrixExponentialRealization_origin
    (jet : CoframeHolonomicSecondJet) :
    coframeHolonomicSecondJetMatrixExponentialRealization jet 0 = 1 := by
  simp [coframeHolonomicSecondJetMatrixExponentialRealization]

/-- Every value of the exponential realization is an invertible coframe. -/
theorem coframeHolonomicSecondJetMatrixExponentialRealization_det_ne_zero
    (jet : CoframeHolonomicSecondJet) (point : BasePoint) :
    Matrix.det
      (coframeHolonomicSecondJetMatrixExponentialRealization jet point) ≠ 0 := by
  have exponentIsUnit :
      IsUnit
        (NormedSpace.exp
          (coframeEndAlgEquiv
            (coframeHolonomicSecondJetQuadraticRealization jet point))) :=
    NormedSpace.isUnit_exp _
  have realizationIsUnit :
      IsUnit
        (coframeHolonomicSecondJetMatrixExponentialRealization jet point) :=
    exponentIsUnit.map coframeEndAlgEquiv.symm.toRingHom
  exact isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp realizationIsUnit)

/-- The exponential realization is globally smooth. -/
theorem coframeHolonomicSecondJetMatrixExponentialRealization_contDiff
    (jet : CoframeHolonomicSecondJet) :
    ContDiff ℝ ∞
      (coframeHolonomicSecondJetMatrixExponentialRealization jet) := by
  change ContDiff ℝ ∞ fun point =>
    coframeEndContinuousLinearEquiv.symm
      (NormedSpace.exp
        (coframeEndContinuousLinearEquiv
          (coframeHolonomicSecondJetQuadraticRealization jet point)))
  exact coframeEndContinuousLinearEquiv.symm.contDiff.comp
    (coframeEnd_exp_contDiff.comp
      (coframeEndContinuousLinearEquiv.contDiff.comp
        (coframeHolonomicSecondJetQuadraticRealization_contDiff jet)))

/-- The exponential realization has zero complete first derivative at the
origin. -/
theorem coframeHolonomicSecondJetMatrixExponentialRealization_hasFDerivAt_origin
    (jet : CoframeHolonomicSecondJet) :
    HasFDerivAt
      (coframeHolonomicSecondJetMatrixExponentialRealization jet)
      (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
  have quadraticDerivative :
      HasFDerivAt
        (coframeHolonomicSecondJetQuadraticRealization jet)
        (0 : BasePoint →L[ℝ] LorentzianCoframe) 0 := by
    simpa using
      (coframeHolonomicSecondJetQuadraticRealization_hasFDerivAt jet 0)
  have mappedDerivativeRaw :=
    coframeEndContinuousLinearEquiv.hasFDerivAt.comp 0 quadraticDerivative
  have mappedDerivative :
      HasFDerivAt
        (fun point =>
          coframeEndContinuousLinearEquiv
            (coframeHolonomicSecondJetQuadraticRealization jet point))
        (0 : BasePoint →L[ℝ]
          (CoframeEndSpace →L[ℝ] CoframeEndSpace)) 0 := by
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
    · funext point
      rfl
    · simp
  have exponentialDerivativeAtMappedOrigin :
      HasFDerivAt
        (NormedSpace.exp :
          (CoframeEndSpace →L[ℝ] CoframeEndSpace) →
            (CoframeEndSpace →L[ℝ] CoframeEndSpace))
        (1 :
          (CoframeEndSpace →L[ℝ] CoframeEndSpace) →L[ℝ]
            (CoframeEndSpace →L[ℝ] CoframeEndSpace))
        (coframeEndContinuousLinearEquiv
          (coframeHolonomicSecondJetQuadraticRealization jet 0)) := by
    simpa using
      (hasFDerivAt_exp_zero :
        HasFDerivAt
          (NormedSpace.exp :
            (CoframeEndSpace →L[ℝ] CoframeEndSpace) →
              (CoframeEndSpace →L[ℝ] CoframeEndSpace))
          (1 :
            (CoframeEndSpace →L[ℝ] CoframeEndSpace) →L[ℝ]
              (CoframeEndSpace →L[ℝ] CoframeEndSpace)) 0)
  have exponentialDerivativeRaw :=
    exponentialDerivativeAtMappedOrigin.comp 0 mappedDerivative
  have pulledDerivativeRaw :=
    coframeEndContinuousLinearEquiv.symm.hasFDerivAt.comp 0
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
  · funext point
    rfl
  · simp

/-- Every coordinate component of the complete first jet vanishes at the
origin. -/
theorem coframeHolonomicSecondJetMatrixExponentialRealization_firstJet_origin
    (jet : CoframeHolonomicSecondJet)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative
        (coframeHolonomicSecondJetMatrixExponentialRealization jet)
        0 direction = 0 := by
  unfold fieldDirectionalDerivative
  rw [
    (coframeHolonomicSecondJetMatrixExponentialRealization_hasFDerivAt_origin
      jet).fderiv]
  simp

private theorem
    coframeHolonomicSecondJetMatrixExponentialRealization_secondJet_diagonal
    (jet : CoframeHolonomicSecondJet)
    (direction : BasePoint) :
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetMatrixExponentialRealization jet)
        direction direction =
      jet.1 direction direction := by
  unfold coframeOriginSecondFrechetJet
  rw [← iteratedDeriv_radialLine_two
    (coframeHolonomicSecondJetMatrixExponentialRealization jet)
    ((coframeHolonomicSecondJetMatrixExponentialRealization_contDiff jet).of_le
      (by exact WithTop.coe_le_coe.mpr le_top)) direction]
  simpa [coframeHolonomicSecondJetMatrixExponentialRealization,
    coframeMatrixExponential, Function.comp_def] using
    (matrixExponentialQuadratic_radialLine_iteratedDeriv_two_origin
      jet direction)

/-- The exponential realization preserves the supplied complete second
Fréchet germ exactly. -/
theorem coframeHolonomicSecondJetMatrixExponentialRealization_secondJet
    (jet : CoframeHolonomicSecondJet) :
    coframeOriginSecondFrechetJet
        (coframeHolonomicSecondJetMatrixExponentialRealization jet) =
      jet.1 := by
  let actualJet := coframeOriginSecondFrechetJet
    (coframeHolonomicSecondJetMatrixExponentialRealization jet)
  have actualSymmetry : ∀ first second : BasePoint,
      actualJet first second = actualJet second first := by
    intro first second
    exact
      ((coframeHolonomicSecondJetMatrixExponentialRealization_contDiff jet).contDiffAt
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
        coframeHolonomicSecondJetMatrixExponentialRealization_secondJet_diagonal,
        coframeHolonomicSecondJetMatrixExponentialRealization_secondJet_diagonal,
        coframeHolonomicSecondJetMatrixExponentialRealization_secondJet_diagonal]
    _ = jet.1 first second := by
      simp only [map_add, add_apply]
      rw [← coframeHolonomicSecondJet_symmetric jet first second]
      module

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeHolonomicMatrixExponentialRealization
