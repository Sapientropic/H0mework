import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Star

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
open scoped Matrix BigOperators
noncomputable section

def coefficientPolynomial (s d z : ℂ) (N : Nat) : Fin 3 → ℂ :=
  fun k => ∑ n ∈ Finset.range N, (n.factorial : ℂ)⁻¹*z^n*coefficientPower s d n k

theorem original_star_polynomial (s d z : ℂ) (N : Nat) :
    Phase.polynomial (z • (s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d)) N=
      starAssembly d (coefficientPolynomial s d z N) := by
  unfold Phase.polynomial coefficientPolynomial
  simp only [smul_pow,star_assembly_power,star_assembly_smul,mul_assoc]
  exact star_assembly_sum _ _ _

theorem original_star_flow (s d : ℂ) (time : ℝ) :
    Phase.flowPolynomial (s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d) time=
      starAssembly d (coefficientPolynomial s d ((time : ℂ)*(-Complex.I)) 14) := by
  have scalar : time • (-Complex.I • (s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d))=
      ((time : ℂ)*(-Complex.I)) • (s • (1 : Matrix (Fin 3) (Fin 3) ℂ)+starCore d) := by
    ext i j
    simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,mul_assoc]
  rw [Phase.flowPolynomial,scalar,original_star_polynomial]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
