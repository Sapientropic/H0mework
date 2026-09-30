import H0mework.Versions.X.NavierStokes.CartanAction.Source

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCartanSpinSupport

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineLorentzConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineFullDiracAdjointMaterial SU7ExteriorBreakingYukawa
open StageNineResidualLinearPlebanskiTorsionReduction StageNineTopologicalLorentzThreeFormDuality
open StageNineTopologicalLorentzThreeFormDualInverse
open ThreeDimensionalPeriodicCoarseFilterCore
open NativeSourceCartan NativeMaterialMomentumJet

noncomputable section

theorem spinLift_basis (direction index : Fin 4) (pair : Fin 6) :
    diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm
      (loweredLorentzBivectorOneFormCoordinate direction pair)) index =
      if index = direction then (2 : ℂ)⁻¹ •
        (diracGamma (lorentzBivectorFirst pair) * diracGamma (lorentzBivectorSecond pair)) else 0 := by
  unfold diracSpinConnectionLift
  simp only [loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  by_cases same : index = direction
  · subst index
    simp [loweredLorentzBivectorOneFormCoordinate, Pi.single_apply, apply_ite, ite_smul]
  · simp [loweredLorentzBivectorOneFormCoordinate, same]

def tripleCurrent (velocity : PhysicalSpace) (first second third : Fin 4) : ℝ :=
  (NativeCanonicalFluidCoframe.dual velocity (Complex.I •
    diracMatrixMatterAction (diracGamma first * (diracGamma second * diracGamma third))
      (NativeCanonicalFluidCoframe.matter velocity))).re

private theorem gamma_square (direction : Fin 4) :
    diracGamma direction * diracGamma direction = (minkowskiInternalSign direction : ℂ) • 1 := by
  fin_cases direction <;> simp [diracGamma, minkowskiInternalSign]

private theorem current_real (velocity : PhysicalSpace) (direction : Fin 4) :
    (NativeCanonicalFluidCoframe.dual velocity
      (diracMatrixMatterAction (diracGamma direction) (NativeCanonicalFluidCoframe.matter velocity))).im = 0 :=
  (NativeCanonicalFluidCoframe.canonical_paired velocity).diracCurrent_real direction

theorem tripleCurrent_first (velocity : PhysicalSpace) (first second : Fin 4) :
    tripleCurrent velocity first first second = 0 := by
  unfold tripleCurrent
  rw [← mul_assoc, gamma_square, Matrix.smul_mul, one_mul, diracMatrixMatterAction_smul_matrix]
  simp [map_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, current_real]

private theorem gamma_swap (first second : Fin 4) (different : first ≠ second) :
    diracGamma first * diracGamma second = -(diracGamma second * diracGamma first) := by
  apply add_eq_zero_iff_eq_neg.mp
  rw [diracGamma_clifford]
  simp [complexMinkowskiEntry, minkowskiInternalMetric, different]

theorem tripleCurrent_last (velocity : PhysicalSpace) (first second : Fin 4) :
    tripleCurrent velocity first second first = 0 := by
  by_cases same : first = second
  · subst second
    exact tripleCurrent_first velocity first first
  unfold tripleCurrent
  rw [← mul_assoc, gamma_swap first second same, neg_mul, mul_assoc, gamma_square,
    Matrix.mul_smul, mul_one]
  rw [← neg_smul, diracMatrixMatterAction_smul_matrix]
  simp [map_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, current_real]

theorem spinCLM_coordinate (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) :
    spinCLM velocity (loweredLorentzBivectorOneFormCoordinate direction pair) =
      coefficient velocity direction / 2 * tripleCurrent velocity direction
        (lorentzBivectorFirst pair) (lorentzBivectorSecond pair) := by
  rw [spinCLM_apply]
  have zero : diracMatrixMatterAction (0 : DiracMatrix) (NativeCanonicalFluidCoframe.matter velocity) = 0 := by
    funext spin
    simp [diracMatrixMatterAction]
  have axis (index : Fin 4) : diracMatrixMatterAction (diracSpinConnectionLift
      (lorentzSkewConnectionOfBivectorOneForm (loweredLorentzBivectorOneFormCoordinate direction pair)) index)
      (NativeCanonicalFluidCoframe.matter velocity) =
      if index = direction then (2 : ℂ)⁻¹ • diracMatrixMatterAction
        (diracGamma (lorentzBivectorFirst pair) * diracGamma (lorentzBivectorSecond pair))
          (NativeCanonicalFluidCoframe.matter velocity) else 0 := by
    rw [spinLift_basis]
    split_ifs
    · exact diracMatrixMatterAction_smul_matrix _ _ _
    · exact zero
  simp only [NativePauliCoframeAction.gaugeVectorAt, axis, apply_ite, map_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [NativeCanonicalFluidCoframe.inverseGamma]
  rw [StageNineLorentzConnectionVariation.diracMatrixMatterAction_real_smul_matrix_local]
  simp only [map_smul]
  rw [← LinearMap.comp_apply, ← diracMatrixMatterAction_mul]
  simp only [tripleCurrent, coefficient]
  simp [map_smul, LinearMap.map_smul_of_tower, smul_eq_mul, Complex.mul_re, Complex.mul_im]
  ring

theorem spinCLM_repeated_zero (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6)
    (repeated : direction = lorentzBivectorFirst pair ∨ direction = lorentzBivectorSecond pair) :
    spinCLM velocity (loweredLorentzBivectorOneFormCoordinate direction pair) = 0 := by
  rw [spinCLM_coordinate]
  rcases repeated with first | second
  · rw [first, tripleCurrent_first, mul_zero]
  · rw [second, tripleCurrent_last, mul_zero]

theorem spinResponse_coordinate (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6) :
    spinResponse velocity pair (missingTripleOfOneForm direction) =
      -(oneWedgeThreeSign direction * spinCLM velocity
        (loweredLorentzBivectorOneFormCoordinate direction pair)) := by
  simp [spinResponse, lorentzOneFormContinuousDualThreeForm, missingTripleOfOneForm_involutive]

theorem spinResponse_repeated_zero (velocity : PhysicalSpace) (direction : Fin 4) (pair : Fin 6)
    (repeated : direction = lorentzBivectorFirst pair ∨ direction = lorentzBivectorSecond pair) :
    spinResponse velocity pair (missingTripleOfOneForm direction) = 0 := by
  rw [spinResponse_coordinate, spinCLM_repeated_zero velocity direction pair repeated, mul_zero, neg_zero]

theorem spinResponse_support (velocity : PhysicalSpace) (pair : Fin 6) (triple : Fin 4)
    (repeated : missingTripleOfOneForm triple = lorentzBivectorFirst pair ∨
      missingTripleOfOneForm triple = lorentzBivectorSecond pair) :
    spinResponse velocity pair triple = 0 := by
  simpa only [missingTripleOfOneForm_involutive] using
    spinResponse_repeated_zero velocity (missingTripleOfOneForm triple) pair repeated

end
end SaturationMonoid.NavierStokes.NativeCartanSpinSupport
