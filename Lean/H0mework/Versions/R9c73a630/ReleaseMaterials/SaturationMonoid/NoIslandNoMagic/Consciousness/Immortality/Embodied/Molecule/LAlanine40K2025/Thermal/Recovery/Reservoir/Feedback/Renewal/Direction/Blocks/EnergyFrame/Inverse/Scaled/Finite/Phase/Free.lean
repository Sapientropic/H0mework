import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
open Collision Load.Source Load.Producer.StrictThermal
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def freePolynomial : LoadedJoint := Matrix.kronecker pcPolynomial environmentPolynomial

theorem pc_polynomial_norm : ‖pcPolynomial‖ ≤ 1+(1/10^18 : ℝ) := by
  have h := norm_sub_le_norm_sub_add_norm_sub pcPolynomial (numericPCFree : Matrix PairController PairController ℂ) 0
  simp only [sub_zero,CStarRing.norm_coe_unitary] at h
  have error := pc_polynomial_error
  rw [norm_sub_rev] at error
  linarith

theorem numeric_free_polynomial_error : ‖(numericFree : LoadedJoint)-freePolynomial‖ ≤ (3/10^18 : ℝ) := by
  let U := (numericPCFree : Matrix PairController PairController ℂ)
  let V := (Load.Recovery.Control.environmentUnitary (Propagation.Producer.nativeClockStep : ℝ) : Matrix (Fin 2) (Fin 2) ℂ)
  have split : (numericFree : LoadedJoint)-freePolynomial=
      Matrix.kronecker (U-pcPolynomial) V+Matrix.kronecker pcPolynomial (V-environmentPolynomial) := by
    ext i j
    simp only [numericFree,Load.Quantum.localUnitary,freePolynomial,U,V,Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.add_apply,Matrix.sub_apply]
    ring
  rw [split]
  apply (norm_add_le _ _).trans
  apply (add_le_add (kronecker_norm_le _ _) (kronecker_norm_le _ _)).trans
  have vnorm : ‖V‖=1 := CStarRing.norm_coe_unitary _
  rw [vnorm,mul_one]
  have product := mul_le_mul pc_polynomial_norm environment_polynomial_error
    (norm_nonneg (V-environmentPolynomial)) (by norm_num : (0 : ℝ) ≤ 1+1/10^18)
  have first : ‖U-pcPolynomial‖ ≤ (1/10^18 : ℝ) := pc_polynomial_error
  nlinarith

theorem actual_free_polynomial_error : ‖(actualFree : LoadedJoint)-freePolynomial‖ ≤ (56/10^15 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (actualFree : LoadedJoint) (numericFree : LoadedJoint) freePolynomial
  linarith [actual_numeric_free_error,numeric_free_polynomial_error]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Phase
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
