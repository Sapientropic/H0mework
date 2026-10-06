import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.TwoBodyResponse
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open BasinRefinement SourceFiniteData SourceGaussianModel SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def pairDensity (z : Point × Point) : ℂ :=
  ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    spinSummedTwoBody i j k l *
      (normalizedOrbital i z.1 * normalizedOrbital k z.1 *
        (normalizedOrbital j z.2 * normalizedOrbital l z.2) : ℝ)

theorem pair_density_full_U (time : ℝ) (z : Point × Point) : pairDensity z =
    ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      spinSummedTwoBody i j k l *
        inner ℂ (normalizedSection i time z.1) (normalizedSection k time z.1) *
        inner ℂ (normalizedSection j time z.2) (normalizedSection l time z.2) := by
  unfold pairDensity
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [normalizedSection_pair,normalizedSection_pair]
  push_cast
  ring

def pairCoulombIntegrand (z : Point × Point) : ℂ :=
  pairDensity z * (kernel (z.2-z.1) : ℝ)

def pairCoulombEnergy : ℂ :=
  (1 / 2 : ℂ) * ∫ z : Point × Point, pairCoulombIntegrand z

def sourceRepulsionSum : ℂ :=
  (1 / 2 : ℂ) *
    ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      spinSummedTwoBody i j k l * (normalizedRepulsion i k j l : ℝ)

private theorem pair_integrand_expansion (z : Point × Point) :
    pairCoulombIntegrand z =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        spinSummedTwoBody i j k l *
          (normalizedOrbital i z.1 * normalizedOrbital k z.1 *
            (normalizedOrbital j z.2 * normalizedOrbital l z.2) *
              kernel (z.2-z.1) : ℝ) := by
  simp only [pairCoulombIntegrand,pairDensity]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  push_cast
  ring

theorem pair_integrable : Integrable pairCoulombIntegrand := by
  change Integrable (fun z : Point × Point => pairCoulombIntegrand z)
  simp_rw [pair_integrand_expansion]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (normalized_quartet_integrable i k j l).ofReal.const_mul _))))

theorem pair_coulomb_energy_source : pairCoulombEnergy = sourceRepulsionSum := by
  have each (i j k l : Basis) : Integrable (fun z : Point × Point =>
      spinSummedTwoBody i j k l *
        (normalizedOrbital i z.1 * normalizedOrbital k z.1 *
          (normalizedOrbital j z.2 * normalizedOrbital l z.2) *
            kernel (z.2-z.1) : ℝ)) :=
    (normalized_quartet_integrable i k j l).ofReal.const_mul _
  simp_rw [pairCoulombEnergy,sourceRepulsionSum,pair_integrand_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))))]
  congr 1
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
  simp only [integral_const_mul,integral_complex_ofReal,normalizedRepulsion]

theorem pair_coulomb_energy_original_ao :
    pairCoulombEnergy = (1 / 2 : ℂ) *
      ∑ a : Basis, ∑ b : Basis, ∑ c : Basis, ∑ d : Basis,
        spinSummedTwoBody a b c d *
          ((∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
            (normalizedSourceFrame i a * normalizedSourceFrame j c *
              normalizedSourceFrame k b * normalizedSourceFrame l d) *
                electronRepulsion i j k l) : ℝ) := by
  rw [pair_coulomb_energy_source]
  simp only [sourceRepulsionSum]
  simp_rw [actual_coulomb_transformation]

def directEnergy : ℂ :=
  (2 : ℂ) * ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    projector24 i k * projector24 j l * (normalizedRepulsion i k j l : ℝ)

def exchangeEnergy : ℂ :=
  ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
    projector24 i l * projector24 j k * (normalizedRepulsion i k j l : ℝ)

theorem pair_coulomb_direct_exchange :
    pairCoulombEnergy = directEnergy - exchangeEnergy := by
  rw [pair_coulomb_energy_source]
  unfold sourceRepulsionSum directEnergy exchangeEnergy
  simp_rw [spin_summed_two_body]
  have each (i j k l : Basis) :
      ((4 : ℂ) * projector24 i k * projector24 j l -
          (2 : ℂ) * projector24 i l * projector24 j k) *
          (normalizedRepulsion i k j l : ℝ) =
        4 * (projector24 i k * projector24 j l * (normalizedRepulsion i k j l : ℝ)) -
        2 * (projector24 i l * projector24 j k * (normalizedRepulsion i k j l : ℝ)) := by
    ring
  simp_rw [each,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
