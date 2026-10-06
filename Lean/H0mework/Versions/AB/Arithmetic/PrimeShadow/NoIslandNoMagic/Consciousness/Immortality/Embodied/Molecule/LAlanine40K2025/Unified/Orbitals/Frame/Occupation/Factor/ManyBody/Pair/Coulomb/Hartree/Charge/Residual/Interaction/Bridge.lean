import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Kernel

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def d3Matrix : Matrix Basis Basis ℝ := normalizedDensityMatrix
def occupationMatrix : Matrix Basis Basis ℝ := fun i k => 2 * (projector24 i k).re
def deltaMatrix : Matrix Basis Basis ℝ := fun i k => residualMatrix i k

theorem density_from_D3 (x : Point) : densityFrom d3Matrix x = sourceDensity x := by
  exact (original_D3_density_expansion x).symm

theorem density_from_occupation (x : Point) :
    densityFrom occupationMatrix x = projectedDensity x := by
  exact (projected_density_expansion x).symm

theorem matrix_split : d3Matrix = occupationMatrix + deltaMatrix := by
  ext i k
  simp only [d3Matrix,occupationMatrix,deltaMatrix,residualMatrix,Matrix.add_apply]
  ring

def d3HartreeEnergy : ℝ :=
  (1 / 2 : ℝ) * ∫ z : Point × Point,
    sourceDensity z.1 * sourceDensity z.2 * kernel (z.2-z.1)

theorem d3_hartree_source :
    d3HartreeEnergy = (1 / 2 : ℝ) * fourCenter d3Matrix d3Matrix := by
  unfold d3HartreeEnergy
  have h (z : Point × Point) :
      sourceDensity z.1 * sourceDensity z.2 * kernel (z.2-z.1) =
        pairIntegrand d3Matrix d3Matrix z := by
    simp only [pairIntegrand,density_from_D3]
  simp_rw [h]
  rw [pair_integral_four_center]

theorem occupation_hartree_source :
    directEnergy.re = (1 / 2 : ℝ) * fourCenter occupationMatrix occupationMatrix := by
  have h (z : Point × Point) : realHartreeIntegrand z =
      (1 / 2 : ℝ) * pairIntegrand occupationMatrix occupationMatrix z := by
    simp only [realHartreeIntegrand,pairIntegrand,density_from_occupation,
      projected_density_norm]
    ring
  calc
    directEnergy.re = ∫ z : Point × Point, realHartreeIntegrand z := by
      rw [direct_energy_real_integral]
      simp only [integral_complex_ofReal,Complex.ofReal_re]
    _ = ∫ z : Point × Point, (1 / 2 : ℝ) *
        pairIntegrand occupationMatrix occupationMatrix z := by simp_rw [h]
    _ = (1 / 2 : ℝ) * ∫ z : Point × Point,
        pairIntegrand occupationMatrix occupationMatrix z := by rw [integral_const_mul]
    _ = _ := by rw [pair_integral_four_center]

theorem four_center_add_left (A B C : Matrix Basis Basis ℝ) :
    fourCenter (A + B) C = fourCenter A C + fourCenter B C := by
  simp only [fourCenter,Matrix.add_apply,add_mul,Finset.sum_add_distrib]

theorem four_center_add_right (A B C : Matrix Basis Basis ℝ) :
    fourCenter A (B + C) = fourCenter A B + fourCenter A C := by
  simp only [fourCenter,Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem d3_occupation_hartree_residual :
    d3HartreeEnergy - directEnergy.re =
      (1 / 2 : ℝ) *
        (fourCenter deltaMatrix d3Matrix +
          fourCenter occupationMatrix deltaMatrix) := by
  rw [d3_hartree_source,occupation_hartree_source]
  rw [matrix_split]
  simp only [four_center_add_left,four_center_add_right]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
