import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
open LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def densityFrom (A : Matrix Basis Basis ℝ) (x : Point) : ℝ :=
  ∑ i : Basis, ∑ k : Basis,
    A i k * normalizedOrbital i x * normalizedOrbital k x

def pairIntegrand (A B : Matrix Basis Basis ℝ) (z : Point × Point) : ℝ :=
  densityFrom A z.1 * densityFrom B z.2 * kernel (z.2-z.1)

def fourCenter (A B : Matrix Basis Basis ℝ) : ℝ :=
  ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
    A j l * B i k * normalizedRepulsion j l i k

theorem pair_integrand_expansion (A B : Matrix Basis Basis ℝ) (z : Point × Point) :
    pairIntegrand A B z =
      ∑ i : Basis, ∑ k : Basis, ∑ j : Basis, ∑ l : Basis,
        A j l * B i k *
          (normalizedOrbital j z.1 * normalizedOrbital l z.1 *
            (normalizedOrbital i z.2 * normalizedOrbital k z.2) * kernel (z.2-z.1)) := by
  simp only [pairIntegrand,densityFrom]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem pair_integrable (A B : Matrix Basis Basis ℝ) :
    Integrable (pairIntegrand A B) := by
  change Integrable (fun z : Point × Point => pairIntegrand A B z)
  simp_rw [pair_integrand_expansion]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ =>
      (normalized_quartet_integrable j l i k).const_mul _))))

theorem pair_integral_four_center (A B : Matrix Basis Basis ℝ) :
    (∫ z : Point × Point, pairIntegrand A B z) = fourCenter A B := by
  have each (i k j l : Basis) : Integrable (fun z : Point × Point =>
      A j l * B i k *
        (normalizedOrbital j z.1 * normalizedOrbital l z.1 *
          (normalizedOrbital i z.2 * normalizedOrbital k z.2) * kernel (z.2-z.1))) :=
    (normalized_quartet_integrable j l i k).const_mul _
  simp_rw [pair_integrand_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ =>
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => each i k j l))))]
  unfold fourCenter
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun l _ => each i k j l)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => each i k j l))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finsetSum _ (fun l _ => each i k j l)]
  apply Finset.sum_congr rfl
  intro l _
  simp only [integral_const_mul,normalizedRepulsion]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
