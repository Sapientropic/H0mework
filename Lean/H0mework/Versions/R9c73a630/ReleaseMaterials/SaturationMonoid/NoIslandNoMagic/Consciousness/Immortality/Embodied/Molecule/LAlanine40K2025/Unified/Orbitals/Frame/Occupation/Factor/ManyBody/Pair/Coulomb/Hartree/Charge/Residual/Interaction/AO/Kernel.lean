import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.Bridge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Proxy.Correction.Algebra

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped BigOperators
noncomputable section

def densityFrom (A : Matrix Basis Basis ℝ) (x : Point) : ℝ :=
  ∑ i : Basis, ∑ j : Basis, A i j * ao i x * ao j x

def pairIntegrand (A B : Matrix Basis Basis ℝ) (z : Point × Point) : ℝ :=
  densityFrom A z.1 * densityFrom B z.2 * kernel (z.2 - z.1)

def fourCenter (A B : Matrix Basis Basis ℝ) : ℝ :=
  ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    A k l * B i j * electronRepulsion k l i j

theorem source_density_ao (x : Point) :
    densityFrom Proxy.Correction.d3AO x = sourceDensity x := by
  rfl

theorem pair_integrand_expansion (A B : Matrix Basis Basis ℝ) (z : Point × Point) :
    pairIntegrand A B z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        A k l * B i j *
          (ao k z.1 * ao l z.1 * (ao i z.2 * ao j z.2) * kernel (z.2 - z.1)) := by
  simp only [pairIntegrand,densityFrom,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pair_integrable (A B : Matrix Basis Basis ℝ) :
    Integrable (pairIntegrand A B) := by
  change Integrable (fun z : Point × Point => pairIntegrand A B z)
  simp_rw [pair_integrand_expansion]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (quartet_integrable k l i j).const_mul _))))

theorem pair_integral_four_center (A B : Matrix Basis Basis ℝ) :
    (∫ z : Point × Point, pairIntegrand A B z) = fourCenter A B := by
  have each (i j k l : Basis) : Integrable (fun z : Point × Point =>
      A k l * B i j *
        (ao k z.1 * ao l z.1 * (ao i z.2 * ao j z.2) * kernel (z.2 - z.1))) :=
    (quartet_integrable k l i j).const_mul _
  simp_rw [pair_integrand_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))))]
  unfold fourCenter
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun l _ => each i j k l)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun l _ => each i j k l)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [integral_const_mul,electronRepulsion]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
