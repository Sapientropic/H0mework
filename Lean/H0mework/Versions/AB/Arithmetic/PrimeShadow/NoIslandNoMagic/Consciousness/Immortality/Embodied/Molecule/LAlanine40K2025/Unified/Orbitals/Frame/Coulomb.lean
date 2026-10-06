import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Orbitals
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Coulomb

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient SourceCoulomb MeasureTheory
open scoped Matrix BigOperators
noncomputable section

private theorem expanded_quartet (a b c d : Basis → ℝ) (z : Point × Point) :
    expansion a z.1 * expansion b z.1 * (expansion c z.2 * expansion d z.2) * kernel (z.2-z.1) =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (a i*b j*c k*d l) * (ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*kernel (z.2-z.1)) := by
  have expand (a b : Basis → ℝ) (x : Point) :
      expansion a x * expansion b x = ∑ i : Basis, ∑ j : Basis, (a i*ao i x)*(b j*ao j x) := by
    unfold expansion
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [expand,expand]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem expansion_quartet_integrable (a b c d : Basis → ℝ) :
    Integrable (fun z : Point × Point =>
      expansion a z.1 * expansion b z.1 * (expansion c z.2 * expansion d z.2) * kernel (z.2-z.1)) := by
  simp_rw [expanded_quartet]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
      (quartet_integrable i j k l).const_mul _))))

theorem expansion_quartet_integral (a b c d : Basis → ℝ) :
    (∫ z : Point × Point,
      expansion a z.1 * expansion b z.1 * (expansion c z.2 * expansion d z.2) * kernel (z.2-z.1)) =
      ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
        (a i*b j*c k*d l) * electronRepulsion i j k l := by
  have each (i j k l : Basis) : Integrable (fun z : Point × Point =>
      (a i*b j*c k*d l) * (ao i z.1*ao j z.1*(ao k z.2*ao l z.2)*kernel (z.2-z.1))) :=
    (quartet_integrable i j k l).const_mul _
  simp_rw [expanded_quartet]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => each i j k l))))]
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
  simp only [integral_const_mul,electronRepulsion]

def normalizedRepulsion (a b c d : Basis) : ℝ := ∫ z : Point × Point,
  normalizedOrbital a z.1 * normalizedOrbital b z.1 *
    (normalizedOrbital c z.2 * normalizedOrbital d z.2) * kernel (z.2-z.1)

theorem normalized_quartet_integrable (a b c d : Basis) :
    Integrable (fun z : Point × Point => normalizedOrbital a z.1 * normalizedOrbital b z.1 *
      (normalizedOrbital c z.2 * normalizedOrbital d z.2) * kernel (z.2-z.1)) :=
  expansion_quartet_integrable _ _ _ _

theorem actual_coulomb_transformation (a b c d : Basis) : normalizedRepulsion a b c d =
    ∑ i : Basis, ∑ j : Basis, ∑ k : Basis, ∑ l : Basis,
      (normalizedSourceFrame i a * normalizedSourceFrame j b * normalizedSourceFrame k c *
        normalizedSourceFrame l d) * electronRepulsion i j k l :=
  expansion_quartet_integral _ _ _ _

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
