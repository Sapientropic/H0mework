import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Positive

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open BasinRefinement SourceFiniteData
open scoped Matrix
noncomputable section

theorem inverse_injective_from_actual_gram (positive : actualGram.PosDef) :
    Function.Injective realInverse.mulVec := by
  intro v w same
  apply Matrix.mulVec_injective_of_isUnit positive.isUnit
  simp only [actualGram,← Matrix.mulVec_mulVec]
  rw [same]

theorem original_metric_positive (positive : actualGram.PosDef) : originalMetric.PosDef := by
  have inverse : IsUnit realInverse := Matrix.mulVec_injective_iff_isUnit.mp
    (inverse_injective_from_actual_gram positive)
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff inverse).mp
  have transpose : star realInverse = realInverse.transpose := by
    ext i j
    simp only [Matrix.star_apply,star_trivial,Matrix.transpose_apply]
  simpa only [actualGram,transpose] using positive

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
