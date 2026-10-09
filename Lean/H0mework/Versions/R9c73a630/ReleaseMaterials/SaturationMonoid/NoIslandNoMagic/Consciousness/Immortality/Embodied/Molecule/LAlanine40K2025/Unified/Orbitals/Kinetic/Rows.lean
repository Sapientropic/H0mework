import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Kinetic.Coefficients

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Kinetic
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient SourceSignedEvaluator
noncomputable section

/-- Kinetic summands propose the differentiated-descriptor list; the kernel
    recognizes coefficient, exponent and penalty cell by cell. -/
noncomputable def KineticRowComputed (materials : RadialIndex → RadialMaterial)
    (b c : Basis) (row : List Summand) : Prop :=
  row.map (summandDescriptor materials) = kineticDescriptors b c

private theorem kinetic_sum_contains (materials : RadialIndex → RadialMaterial)
    (row : List Summand)
    (valid : ∀ s ∈ row, Holds (materials s.kernel).interval
      (radialKernel (materials s.kernel).gamma (materials s.kernel).penalty)) :
    Holds (rowInterval materials row)
      ((row.map (summandDescriptor materials)).map descriptorValue).sum := by
  induction row with
  | nil => simpa only [rowInterval,List.map_nil,List.foldr_nil,List.sum_nil,Rat.cast_zero] using point_holds 0
  | cons s rest ih =>
      have first := mul_holds _ _ _ _ (point_holds s.coefficient) (valid s (by simp))
      have remaining := ih (fun t ht => valid t (by simp [ht]))
      exact add_holds _ _ _ _ first remaining

/-- The interval contains the actual kinetic matrix element. -/
theorem kinetic_row_contains (materials : RadialIndex → RadialMaterial) (b c : Basis) (row : List Summand)
    (computed : KineticRowComputed materials b c row)
    (valid : ∀ s ∈ row, Holds (materials s.kernel).interval
      (radialKernel (materials s.kernel).gamma (materials s.kernel).penalty)) :
    Holds (rowInterval materials row) (kinetic b c) := by
  have result := kinetic_sum_contains materials row valid
  rw [computed,← kinetic_descriptors_evaluated] at result
  exact result

end
end LAlanine40K2025.UnifiedOrbitals.Kinetic
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
