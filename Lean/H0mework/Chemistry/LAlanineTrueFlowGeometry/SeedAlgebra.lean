import H0mework.Chemistry.LAlanineTrueFlowGeometry.SeedTransverse

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowGeometry

open SourceGaussianModel ContinuousSeed Matrix
open scoped Matrix
noncomputable section

theorem seedNormal_eq_cross : seedNormal = basisVector 0 ⨯₃ basisVector 1 := by
  ext i
  fin_cases i <;> simp [seedNormal, seedNormalQ, basisVector, cross_apply]

theorem seedNormal_dot_basis (j : Fin 2) : seedNormal ⬝ᵥ basisVector j = 0 := by
  rw [seedNormal_eq_cross, dotProduct_comm]
  fin_cases j
  · exact dot_self_cross _ _
  · exact dot_cross_self _ _

theorem seed_basis_minor_ne_zero :
    basisVector 0 0 * basisVector 1 1 - basisVector 0 1 * basisVector 1 0 ≠ 0 := by
  have original : Geometry.Source.basis 0 0 * Geometry.Source.basis 1 1 -
      Geometry.Source.basis 1 0 * Geometry.Source.basis 0 1 ≠ 0 := by decide +kernel
  simp only [basisVector]
  exact_mod_cast original

theorem seed_basis_coefficients (a b : ℝ)
    (zero : a • basisVector 0 + b • basisVector 1 = 0) : a = 0 ∧ b = 0 := by
  have first : a * basisVector 0 0 + b * basisVector 1 0 = 0 := congrFun zero 0
  have second : a * basisVector 0 1 + b * basisVector 1 1 = 0 := congrFun zero 1
  have left : a * (basisVector 0 0 * basisVector 1 1 -
      basisVector 0 1 * basisVector 1 0) = 0 := by
    linear_combination basisVector 1 1 * first - basisVector 1 0 * second
  have right : b * (basisVector 0 0 * basisVector 1 1 -
      basisVector 0 1 * basisVector 1 0) = 0 := by
    linear_combination basisVector 0 0 * second - basisVector 0 1 * first
  exact ⟨(mul_eq_zero.mp left).resolve_right seed_basis_minor_ne_zero,
    (mul_eq_zero.mp right).resolve_right seed_basis_minor_ne_zero⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowGeometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
