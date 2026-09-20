import H0mework.Physics.SpinPair.Regularity

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineGlobalIntegratedAction StageNineHolonomicField

noncomputable section

def phaseCoefficientVelocity (point : BasePoint) : DiracSpinorIndex → Fin 2 → ℂ :=
  fun row column => spinPairCoefficients (upperPhase point * ((frequency : ℂ) * Complex.I))
    (lowerPhase point * ((-frequency : ℂ) * Complex.I)) row column

theorem phaseCoefficients_hasFDerivAt (point : BasePoint) :
    HasFDerivAt (fun point => spinPairCoefficients (upperPhase point) (lowerPhase point))
      ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
        (phaseCoefficientVelocity point)) point := by
  have component (row : DiracSpinorIndex) (column : Fin 2) :
      HasFDerivAt (fun candidate =>
        spinPairCoefficients (upperPhase candidate) (lowerPhase candidate) row column)
        ((EuclideanSpace.proj (0 : Fin 4) : BasePoint →L[ℝ] ℝ).smulRight
          (phaseCoefficientVelocity point row column)) point := by
    fin_cases row <;> fin_cases column
    · simpa [spinPairCoefficients, phaseCoefficientVelocity] using
        hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · exact phase_hasFDerivAt frequency point
    · convert (phase_hasFDerivAt frequency point).neg using 1 <;>
        first | rfl | ext vector; simp [phaseCoefficientVelocity, spinPairCoefficients, upperPhase]
    · simpa [spinPairCoefficients, phaseCoefficientVelocity] using
        hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · simpa [spinPairCoefficients, phaseCoefficientVelocity] using
        hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
    · simpa [phaseCoefficientVelocity, spinPairCoefficients, upperPhase, lowerPhase] using
        phase_hasFDerivAt (-frequency) point
    · convert (phase_hasFDerivAt (-frequency) point).neg using 1 <;>
        first | rfl | ext vector; simp [phaseCoefficientVelocity, spinPairCoefficients, lowerPhase]
    · simpa [spinPairCoefficients, phaseCoefficientVelocity] using
        hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) point
  apply hasFDerivAt_pi''
  intro row
  apply hasFDerivAt_pi''
  intro column
  convert component row column using 1 <;> rfl

theorem phaseLinear_directionalDerivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (linear : (DiracSpinorIndex → Fin 2 → ℂ) →L[ℝ] E)
    (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative
      (fun candidate => linear (spinPairCoefficients (upperPhase candidate) (lowerPhase candidate)))
      point direction =
      if direction = 0 then linear (phaseCoefficientVelocity point) else 0 := by
  have derivative := linear.hasFDerivAt.comp point (phaseCoefficients_hasFDerivAt point)
  change HasFDerivAt (fun candidate =>
    linear (spinPairCoefficients (upperPhase candidate) (lowerPhase candidate))) _ point at derivative
  unfold fieldDirectionalDerivative
  rw [derivative.fderiv]
  change linear ((coordinateDirection direction) 0 • phaseCoefficientVelocity point) = _
  by_cases same : direction = 0
  · subst direction
    simp [coordinateDirection]
  · simp [coordinateDirection, Ne.symm same, same]

theorem actual_matterCoordinateDerivative
    (point : BasePoint) (direction : LorentzianIndex) :
    matterCoordinateEquiv.symm
      (fieldDirectionalDerivative (fun candidate => matterCoordinateEquiv (actual.matter candidate))
        point direction) =
      if direction = 0 then
        spinPairMatter (upperPhase point * ((frequency : ℂ) * Complex.I))
          (lowerPhase point * ((-frequency : ℂ) * Complex.I)) else 0 := by
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  have derivative := phaseLinear_directionalDerivative linear point direction
  change fieldDirectionalDerivative
    (fun candidate => matterCoordinateEquiv (actual.matter candidate)) point direction = _ at derivative
  rw [derivative]
  split_ifs
  · exact matterCoordinateEquiv.symm_apply_apply _
  · exact map_zero _

private def dualEvaluationLinear (matter : DiracExteriorMatterCarrier) :
    (DiracSpinorIndex → Fin 2 → ℂ) →ₗ[ℂ] ℂ where
  toFun coefficients := ∑ spin, ∑ state,
    coefficients spin state * sourceColorDoubletDual state (matter spin)
  map_add' := by
    intro first second
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro coefficient values
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro spin _
    apply Finset.sum_congr rfl
    intro state _
    ring

theorem actual_conjugateMatterDerivative
    (matter : DiracExteriorMatterCarrier) (point : BasePoint) (direction : LorentzianIndex) :
    fieldDirectionalDerivative (fun candidate => actual.conjugateMatter candidate matter) point direction =
      if direction = 0 then
        spinPairDual (upperDualPhase point * ((frequency : ℂ) * Complex.I))
          (lowerDualPhase point * ((-frequency : ℂ) * Complex.I)) matter else 0 := by
  let linear := ((spinScale : ℂ) • (dualEvaluationLinear matter)).restrictScalars ℝ
  have field (candidate : BasePoint) :
      linear.toContinuousLinearMap
        (spinPairCoefficients (upperPhase candidate) (lowerPhase candidate)) =
      actual.conjugateMatter candidate matter := by
    change (spinScale : ℂ) * spinPairDual (upperPhase candidate) (lowerPhase candidate) matter = _
    simp [actual_conjugateMatter, spinPairDual, sourceColorDiracDual, spinPairCoefficients,
      upperDualPhase, lowerDualPhase, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  have derivative := phaseLinear_directionalDerivative linear.toContinuousLinearMap point direction
  simp_rw [field] at derivative
  rw [derivative]
  split_ifs
  · change (spinScale : ℂ) * sourceColorDiracDual (phaseCoefficientVelocity point) matter = _
    simp [phaseCoefficientVelocity, spinPairDual, sourceColorDiracDual, spinPairCoefficients,
      upperDualPhase, lowerDualPhase, Fin.sum_univ_four, Fin.sum_univ_two]
    ring
  · rfl

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
