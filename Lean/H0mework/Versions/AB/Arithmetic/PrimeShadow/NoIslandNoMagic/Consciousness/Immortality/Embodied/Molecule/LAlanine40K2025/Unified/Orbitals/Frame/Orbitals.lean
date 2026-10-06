import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Normalize

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData SourceGaussianModel ContinuousGradient MeasureTheory
open scoped Matrix BigOperators
noncomputable section

def normalizedOrbital (b : Basis) : Point → ℝ := expansion (fun i => normalizedSourceFrame i b)

theorem expansion_pair (left right : Basis → ℝ) :
    (∫ x : Point, expansion left x * expansion right x) =
      ∑ b : Basis, ∑ c : Basis, left b * right c * overlap b c := by
  have each (b c : Basis) : Integrable (fun x => (left b * right c) * (ao b x * ao c x)) :=
    (source_product_integrable b c zeroJet zeroJet).const_mul _
  have rewrite (x : Point) : expansion left x * expansion right x =
      ∑ b : Basis, ∑ c : Basis, (left b * right c) * (ao b x * ao c x) := by
    simp only [expansion,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    ring
  simp_rw [rewrite]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => each b c))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun c _ => each b c)]
  simp only [integral_const_mul,overlap]

theorem normalized_pair_integrable (b c : Basis) :
    Integrable (fun x : Point => normalizedOrbital b x * normalizedOrbital c x) :=
  expansion_product_integrable _ _

theorem normalized_pair (positive : actualGram.PosDef) (b c : Basis) :
    (∫ x : Point, normalizedOrbital b x * normalizedOrbital c x) = if b = c then 1 else 0 := by
  rw [normalizedOrbital,normalizedOrbital,expansion_pair]
  have equality := congrArg (fun M : Matrix Basis Basis ℝ => M b c) (normalized_original_metric positive)
  rw [Metric.congruence_entry] at equality
  simpa only [originalMetric,Matrix.of_apply,Matrix.one_apply] using equality

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
