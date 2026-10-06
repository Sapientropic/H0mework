import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Enclosure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceGaussianModel SourceFiniteData ContinuousGradient SourceSignedEvaluator

abbrev RadialIndex := Fin 3859

structure Summand where
  kernel : RadialIndex
  coefficient : ℚ
  deriving Inhabited

abbrev Descriptor := ℚ × ℚ × ℚ
def termDescriptor (first second : Term) : Descriptor :=
  (primitiveCoefficient first second,pairExponent first second,pairPenalty first second)
noncomputable def descriptorValue (d : Descriptor) : ℝ :=
  (d.1 : ℝ) * radialKernel d.2.1 d.2.2

noncomputable def sourceDescriptors (b c : Basis) : List Descriptor :=
  (sourceTerms b).flatMap (fun first => (sourceTerms c).map (termDescriptor first))

theorem source_descriptors_evaluated (b c : Basis) :
    overlap b c = ((sourceDescriptors b c).map descriptorValue).sum := by
  rw [original_overlap_evaluated]
  simp only [overlapProgram,termOverlapProgram,sourceDescriptors,
    List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,Function.comp_def,
    descriptorValue,termDescriptor]
  congr 1
  apply List.map_congr_left
  intro first _
  congr 1
  apply List.map_congr_left
  intro second _
  exact term_computed_radial first second

def summandDescriptor (materials : RadialIndex → RadialMaterial) (s : Summand) : Descriptor :=
  (s.coefficient,(materials s.kernel).gamma,(materials s.kernel).penalty)
def summandInterval (materials : RadialIndex → RadialMaterial) (s : Summand) : Pair :=
  mul (point s.coefficient) (materials s.kernel).interval
def rowInterval (materials : RadialIndex → RadialMaterial) (row : List Summand) : Pair :=
  (row.map (summandInterval materials)).foldr add (point 0)
noncomputable def RowComputed (materials : RadialIndex → RadialMaterial) (b c : Basis) (row : List Summand) : Prop :=
  row.map (summandDescriptor materials) = sourceDescriptors b c

private theorem sum_contains (materials : RadialIndex → RadialMaterial) (row : List Summand)
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

/-- Original ordered primitive multiplicities are retained by the descriptor equality. -/
theorem original_row_contains (materials : RadialIndex → RadialMaterial) (b c : Basis) (row : List Summand)
    (computed : RowComputed materials b c row)
    (valid : ∀ s ∈ row, Holds (materials s.kernel).interval
      (radialKernel (materials s.kernel).gamma (materials s.kernel).penalty)) :
    Holds (rowInterval materials row) (overlap b c) := by
  have result := sum_contains materials row valid
  rw [computed,← source_descriptors_evaluated] at result
  exact result

end LAlanine40K2025.UnifiedOrbitals
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
