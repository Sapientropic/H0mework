import H0mework.Physics.SpinPair.Adjoint
import H0mework.Physics.Fluid.Fields

set_option autoImplicit false
open scoped Matrix ContDiff

namespace SaturationMonoid.PhysicsCore.Stage9CU.Fluid.InitialLift

open DiracCliffordRepresentation DiracExteriorMatterAction
open Stage9C.Material.SpinPair StageNineFullDiracAdjointMaterial
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineCanonicalCauchyState

noncomputable section

def coefficients (value : Fin 3 → ℝ) : DiracSpinorIndex → Fin 2 → ℂ :=
  !![0, 0; 0, 0;
    1 + (value 2 : ℂ) / 4, ((value 0 : ℂ) - Complex.I * (value 1 : ℂ)) / 4;
    ((value 0 : ℂ) + Complex.I * (value 1 : ℂ)) / 4, 1 - (value 2 : ℂ) / 4]

def dualCoefficients (value : Fin 3 → ℝ) : DiracSpinorIndex → Fin 2 → ℂ :=
  !![1 + (value 2 : ℂ) / 4, ((value 0 : ℂ) + Complex.I * (value 1 : ℂ)) / 4;
    ((value 0 : ℂ) - Complex.I * (value 1 : ℂ)) / 4, 1 - (value 2 : ℂ) / 4;
    0, 0; 0, 0]

def matter (value : Fin 3 → ℝ) : DiracExteriorMatterCarrier :=
  sourceColorDiracMatter (coefficients value)

def dual (value : Fin 3 → ℝ) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  sourceColorDiracDual (dualCoefficients value)

theorem fullAdjointPaired (value : Fin 3 → ℝ) :
    FullDiracAdjointPaired (matter value) (dual value) := by
  change dual value = fullCanonicalDiracAdjoint (matter value)
  apply LinearMap.ext
  intro candidate
  rw [fullCanonicalDiracAdjoint_evaluate]
  simp only [matter, sourceColorDiracMatter, fullInternalPair_colorLinear]
  simp [dual, sourceColorDiracDual, coefficients, dualCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two, map_ofNat, sub_eq_add_neg]

theorem spatialCurrent_eq (value : Fin 3 → ℝ) (direction : Fin 3) :
    (dual value (diracMatrixMatterAction (diracGamma direction.succ) (matter value))).re =
      value direction := by
  change (∑ spin, ∑ color, dualCoefficients value spin color *
    sourceColorDoubletDual color
      (diracMatrixMatterAction (diracGamma direction.succ) (sourceColorDiracMatter (coefficients value)) spin)).re = _
  simp only [sourceColorDoubletDual_diracMatrix]
  fin_cases direction <;>
    simp [coefficients, dualCoefficients, diracGamma, diracGammaOne, diracGammaTwo,
      diracGammaThree, Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem temporalCurrent_eq (value : Fin 3 → ℝ) :
    (dual value (diracMatrixMatterAction (diracGamma 0) (matter value))).re =
      2 + ((value 0)^2 + (value 1)^2 + (value 2)^2) / 8 := by
  change (∑ spin, ∑ color, dualCoefficients value spin color *
    sourceColorDoubletDual color
      (diracMatrixMatterAction (diracGamma 0) (sourceColorDiracMatter (coefficients value)) spin)).re = _
  simp only [sourceColorDoubletDual_diracMatrix]
  simp [coefficients, dualCoefficients, diracGamma, diracGammaZero,
    Fin.sum_univ_four, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

theorem temporalCurrent_pos (value : Fin 3 → ℝ) :
    0 < (dual value (diracMatrixMatterAction (diracGamma 0) (matter value))).re := by
  rw [temporalCurrent_eq]
  positivity

theorem coefficients_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → StageNineSpatialPoint}
    (smooth : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun point => coefficients (fun direction => u point direction)) := by
  have each (direction : Fin 3) : ContDiff ℝ ∞ (fun point => (u point direction : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_piLp 2).mp smooth direction)
  apply contDiff_pi.2
  intro spin
  apply contDiff_pi.2
  intro color
  fin_cases spin <;> fin_cases color
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const.add ((each 2).div_const 4)
  · exact ((each 0).sub (contDiff_const.mul (each 1))).div_const 4
  · exact ((each 0).add (contDiff_const.mul (each 1))).div_const 4
  · exact contDiff_const.sub ((each 2).div_const 4)

theorem matter_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → StageNineSpatialPoint} (smooth : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (matter (fun direction => u point direction))) := by
  let linear := (sourceColorMatterCoordinateLinear.restrictScalars ℝ).toContinuousLinearMap
  exact linear.contDiff.comp (coefficients_contDiff smooth)

private theorem dualCoefficients_eq_star (value : Fin 3 → ℝ) (spin : Fin 4) (color : Fin 2) :
    dualCoefficients value spin color = star (coefficients value (![2, 3, 0, 1] spin) color) := by
  fin_cases spin <;> fin_cases color <;>
    simp [dualCoefficients, coefficients, sub_eq_add_neg]

theorem dual_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → StageNineSpatialPoint} (smooth : ContDiff ℝ ∞ u)
    (candidate : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => dual (fun direction => u point direction) candidate) := by
  have coefficient (spin : Fin 4) (color : Fin 2) :
      ContDiff ℝ ∞ (fun point => dualCoefficients (fun direction => u point direction) spin color) := by
    simp only [dualCoefficients_eq_star]
    exact Complex.conjCLE.contDiff.comp
      ((contDiff_pi.mp (contDiff_pi.mp (coefficients_contDiff smooth) _)) color)
  change ContDiff ℝ ∞ (fun point => ∑ spin, ∑ color,
    dualCoefficients (fun direction => u point direction) spin color *
      sourceColorDoubletDual color (candidate spin))
  apply ContDiff.sum
  intro spin _
  apply ContDiff.sum
  intro color _
  exact (coefficient spin color).mul contDiff_const

end
end SaturationMonoid.PhysicsCore.Stage9CU.Fluid.InitialLift
