import H0mework.Physics.Holonomic.CoframeHolonomicMatrixExponentialRealization

/-!
# Matrix-exponential retraction of a coframe increment

This module retracts an additive coframe increment through the matrix
exponential relative to one nondegenerate base coframe.  It canonically
retains the base value, the zero-increment first germ, and global
nondegeneracy.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeMatrixExponentialRetraction

open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicMatrixExponentialRealization
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

private abbrev RetractionCoframeEndSpace :=
  WithLp 2 (LorentzianIndex → ℝ)

private noncomputable def retractionCoframeEndAlgEquiv :
    LorentzianCoframe ≃ₐ[ℝ]
      (RetractionCoframeEndSpace →L[ℝ] RetractionCoframeEndSpace) :=
  (Matrix.toLpLinAlgEquiv (R := ℝ) (n := LorentzianIndex) 2).trans
    (Module.End.toContinuousLinearMap RetractionCoframeEndSpace)

private noncomputable def retractionCoframeEndContinuousLinearEquiv :
    LorentzianCoframe ≃L[ℝ]
      (RetractionCoframeEndSpace →L[ℝ] RetractionCoframeEndSpace) :=
  retractionCoframeEndAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

private def coframeLeftMultiplicationCLM
    (base : LorentzianCoframe) :
    LorentzianCoframe →L[ℝ] LorentzianCoframe := by
  let leftOnEnd :
      (RetractionCoframeEndSpace →L[ℝ] RetractionCoframeEndSpace) →L[ℝ]
        (RetractionCoframeEndSpace →L[ℝ] RetractionCoframeEndSpace) :=
    (ContinuousLinearMap.compL ℝ
      RetractionCoframeEndSpace RetractionCoframeEndSpace
      RetractionCoframeEndSpace)
      (retractionCoframeEndContinuousLinearEquiv base)
  exact retractionCoframeEndContinuousLinearEquiv.symm.toContinuousLinearMap.comp
    (leftOnEnd.comp
      retractionCoframeEndContinuousLinearEquiv.toContinuousLinearMap)

@[simp] private theorem coframeLeftMultiplicationCLM_apply
    (base increment : LorentzianCoframe) :
    coframeLeftMultiplicationCLM base increment = base * increment := by
  change retractionCoframeEndAlgEquiv.symm
      (retractionCoframeEndAlgEquiv base *
        retractionCoframeEndAlgEquiv increment) = _
  rw [← map_mul]
  simp

/-- Retraction of an additive coframe increment through the Lie-group
exponential based at `base`. -/
def coframeMatrixExponentialRetraction
    (base increment : LorentzianCoframe) : LorentzianCoframe :=
  base * coframeMatrixExponential (base⁻¹ * increment)

@[simp] theorem coframeMatrixExponentialRetraction_zero
    (base : LorentzianCoframe) :
    coframeMatrixExponentialRetraction base 0 = base := by
  simp [coframeMatrixExponentialRetraction]

/-- A nondegenerate base remains nondegenerate after every retracted
increment. -/
theorem coframeMatrixExponentialRetraction_det_ne_zero
    (base increment : LorentzianCoframe)
    (baseNondegenerate : Matrix.det base ≠ 0) :
    Matrix.det (coframeMatrixExponentialRetraction base increment) ≠ 0 := by
  rw [coframeMatrixExponentialRetraction, Matrix.det_mul]
  exact mul_ne_zero baseNondegenerate
    (coframeMatrixExponential_det_ne_zero (base⁻¹ * increment))

/-- At a zero increment, exponential retraction preserves the complete first
germ of that increment. -/
theorem coframeMatrixExponentialRetraction_comp_hasFDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (base : LorentzianCoframe)
    (baseNondegenerate : Matrix.det base ≠ 0)
    (increment : E → LorentzianCoframe)
    (point : E)
    (derivative : E →L[ℝ] LorentzianCoframe)
    (incrementDerivative : HasFDerivAt increment derivative point)
    (incrementZero : increment point = 0) :
    HasFDerivAt
      (fun candidate =>
        coframeMatrixExponentialRetraction base (increment candidate))
      derivative point := by
  let inverseLeft := coframeLeftMultiplicationCLM base⁻¹
  let baseLeft := coframeLeftMultiplicationCLM base
  have inverseIncrementDerivative :
      HasFDerivAt
        (fun candidate => base⁻¹ * increment candidate)
        (inverseLeft.comp derivative) point := by
    have composed :=
      inverseLeft.hasFDerivAt.comp point incrementDerivative
    apply composed.congr_of_eventuallyEq
    filter_upwards with candidate
    exact
      (coframeLeftMultiplicationCLM_apply base⁻¹
        (increment candidate)).symm
  have exponentialDerivative :
      HasFDerivAt
        (fun candidate =>
          coframeMatrixExponential (base⁻¹ * increment candidate))
        ((1 : LorentzianCoframe →L[ℝ] LorentzianCoframe).comp
          (inverseLeft.comp derivative)) point := by
    have outerAt : HasFDerivAt coframeMatrixExponential
        (1 : LorentzianCoframe →L[ℝ] LorentzianCoframe)
        (base⁻¹ * increment point) := by
      simpa [incrementZero] using
        coframeMatrixExponential_hasFDerivAt_zero
    exact outerAt.comp point inverseIncrementDerivative
  have retractedDerivative :
      HasFDerivAt
        (fun candidate =>
          base *
            coframeMatrixExponential (base⁻¹ * increment candidate))
        (baseLeft.comp
          ((1 : LorentzianCoframe →L[ℝ] LorentzianCoframe).comp
            (inverseLeft.comp derivative))) point := by
    have composed :=
      baseLeft.hasFDerivAt.comp point exponentialDerivative
    apply composed.congr_of_eventuallyEq
    filter_upwards with candidate
    exact
      (coframeLeftMultiplicationCLM_apply base
        (coframeMatrixExponential
          (base⁻¹ * increment candidate))).symm
  convert retractedDerivative using 1
  · rfl
  · ext direction
    simp only [baseLeft, inverseLeft, ContinuousLinearMap.comp_apply,
      one_apply_eq_self,
      coframeLeftMultiplicationCLM_apply]
    symm
    rw [← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv base
        (isUnit_iff_ne_zero.mpr baseNondegenerate), Matrix.one_mul]

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeMatrixExponentialRetraction
