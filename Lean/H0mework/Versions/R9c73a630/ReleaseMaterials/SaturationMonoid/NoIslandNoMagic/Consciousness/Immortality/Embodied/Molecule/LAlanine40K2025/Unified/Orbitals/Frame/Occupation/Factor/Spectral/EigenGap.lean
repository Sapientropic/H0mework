import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Spectral.Polynomial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
noncomputable section
attribute [local irreducible] Occupation.gamma

private theorem polynomial_cfc :
    cfc (fun x : ℝ => x^2 - 2*x) Occupation.gamma =
      Occupation.gamma * Occupation.gamma - (2 : ℂ) • Occupation.gamma := by
  have hermitian := Occupation.gamma_hermitian.isSelfAdjoint
  rw [cfc_sub (fun x : ℝ => x^2) (fun x : ℝ => 2*x) Occupation.gamma]
  rw [cfc_pow_id (R := ℝ) Occupation.gamma 2, cfc_const_mul_id (R := ℝ) 2 Occupation.gamma]
  simp only [pow_two]
  rfl

theorem eigenvalue_polynomial_gap (i : Basis) :
    |Occupation.gamma_hermitian.eigenvalues i ^ 2 -
      2 * Occupation.gamma_hermitian.eigenvalues i| < (1 / 1000 : ℝ) := by
  let eigen : ℝ := Occupation.gamma_hermitian.eigenvalues i
  have hSpectrum : eigen ∈ spectrum ℝ Occupation.gamma :=
    Occupation.gamma_hermitian.eigenvalues_mem_spectrum_real i
  have hCfc : ‖eigen^2 - 2*eigen‖ ≤
      ‖cfc (fun x : ℝ => x^2 - 2*x) Occupation.gamma‖ :=
    norm_apply_le_norm_cfc (fun x : ℝ => x^2 - 2*x)
      Occupation.gamma hSpectrum (by fun_prop) Occupation.gamma_hermitian.isSelfAdjoint
  rw [polynomial_cfc] at hCfc
  simpa only [Real.norm_eq_abs] using hCfc.trans_lt actual_gamma_quadratic_gap

theorem occupied_eigenvalue_near_two (i : Basis) (h : Occupation.occupied i) :
    |Occupation.gamma_hermitian.eigenvalues i - 2| < (1 / 1000 : ℝ) := by
  let eigen : ℝ := Occupation.gamma_hermitian.eigenvalues i
  have gap := eigenvalue_polynomial_gap i
  have positive : 1 < eigen := h
  have factor : eigen^2 - 2*eigen = eigen*(eigen-2) := by ring
  rw [factor,abs_mul,abs_of_pos (by linarith : 0 < eigen)] at gap
  have nonnegative : 0 ≤ |eigen-2| := abs_nonneg _
  nlinarith

theorem unoccupied_eigenvalue_near_zero (i : Basis) (h : ¬ Occupation.occupied i) :
    |Occupation.gamma_hermitian.eigenvalues i| < (1 / 1000 : ℝ) := by
  let eigen : ℝ := Occupation.gamma_hermitian.eigenvalues i
  have gap := eigenvalue_polynomial_gap i
  have atMost : eigen ≤ 1 := le_of_not_gt h
  have factor : eigen^2 - 2*eigen = eigen*(eigen-2) := by ring
  rw [factor,abs_mul,abs_of_nonpos (by linarith : eigen-2 ≤ 0)] at gap
  have nonnegative : 0 ≤ |eigen| := abs_nonneg _
  nlinarith

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.Spectral
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
